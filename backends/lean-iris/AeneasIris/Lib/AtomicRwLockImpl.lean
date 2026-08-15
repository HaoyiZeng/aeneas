import AeneasIris.Lib.RwLockImpl
import AeneasIris.Effects.AtomicHeapAPI

/-! # The ITree `RwLock` over an atomic heap

`RwLockImpl` reaches for `Conc.sync` four times -- around both acquisitions and
both releases -- because the plain heap it reads the state word through never
yields, so without those wrappers nothing could ever interleave.  Here not one
yield is written by hand: the state word is read and written through
`AtomicHeapAPI`, and every interference point comes from the operation itself.

The ghost state is `RwLockImpl`'s, unchanged.  Unqualified operations are the
atomic ones; the payload accesses are qualified, and are deliberate -- the value
a lock guards is ordinary memory, protected by the lock rather than by being an
atomic. -/

namespace AeneasIris.AtomicRwLockImpl

open Iris BI Aeneas.Data.Coinductive
open AeneasIris AeneasIris.AtomicHeapAPI
open AeneasIris.RwLockImpl (Handle ReadGuard WriteGuard mkReadGuard mkWriteGuard)
open Aeneas.Std (StateE StepE Loc Val RustHeap)
open scoped Aeneas.Std
open AeneasIris.Step (lat stepH)
open Iris.CMRA Iris.OFE
open scoped Iris

section Code

variable {E : Effect.{1}} [StateE RustHeap.{0} -< E] [StepE.{1} -< E]
variable [Aeneas.Std.FailE.{1} -< E]
variable [Aeneas.Std.ConcE.{1} -< E]
variable {T : Type}

noncomputable def new (v : T) : ITree E (Handle T) := do
  let d ← HeapAPI.alloc v
  let s ← HeapAPI.alloc (0 : Int)
  return ⟨s, d⟩

/-- The compare-and-swap is retried, because losing it to another reader is not
the same as finding the lock held for writing: `RwLockAPI` asks that a `try_read`
succeed whenever the lock is not write-locked, and only a retry delivers that
once the load and the swap are separated by an interference point.  Rust retries
here for the same reason, and gives up only on seeing the lock held. -/
noncomputable def try_read_acquire (lk : Handle T) : ITree E (Option (ReadGuard T)) :=
  ITree.iter (fun _ => do
    let n : Int ← load lk.state
    if n < 0 then
      return .inr none
    else
      let ok ← cas lk.state n (n + 1)
      if ok then return .inr (some ⟨lk⟩) else return .inl ()) ()

noncomputable def try_write_acquire (lk : Handle T) : ITree E (Option (WriteGuard T)) := do
  let ok ← cas lk.state (0 : Int) (-1)
  if ok then return some ⟨lk⟩ else return none

/-- One loop, not a wait around a retry: a reader that loses the swap and a
reader that finds the lock held both do the same thing, which is to go round
again.  No `Conc.sync` either -- the load it goes back to is an atomic access,
so the yield is already there. -/
noncomputable def read_acquire (lk : Handle T) : ITree E (ReadGuard T) :=
  ITree.iter (fun _ => do
    let n : Int ← load lk.state
    if n < 0 then
      return .inl ()
    else
      let ok ← cas lk.state n (n + 1)
      if ok then return .inr (⟨lk⟩ : ReadGuard T) else return .inl ()) ()

noncomputable def write_acquire (lk : Handle T) : ITree E (WriteGuard T) :=
  AeneasIris.Conc.waitUntil (try_write_acquire (E := E) lk)

/-- Releasing a read lock is a decrement, so it is one atomic operation and not a
compare-and-swap retried until it wins.  That is what Rust does, and here it also
means the release cannot fail: `.read 0` has word 1 and `.free` has word 0. -/
noncomputable def read_release (g : ReadGuard T) : ITree E Unit := do
  let _ : Int ← faa g.lock.state (-1)
  return ()

noncomputable def write_release (g : WriteGuard T) : ITree E Unit :=
  store g.lock.state (0 : Int)

noncomputable def try_read (lk : Handle T) :
    ITree E (Option (ReadGuard T × (ReadGuard T → ITree E Unit))) :=
  ITree.bind (try_read_acquire (E := E) lk)
    (fun r => .ret (r.map (fun g => (g, read_release))))

noncomputable def try_write (lk : Handle T) :
    ITree E (Option (WriteGuard T × (WriteGuard T → ITree E Unit))) :=
  ITree.bind (try_write_acquire (E := E) lk)
    (fun r => .ret (r.map (fun g => (g, write_release))))

noncomputable def read (lk : Handle T) :
    ITree E (ReadGuard T × (ReadGuard T → ITree E Unit)) :=
  ITree.bind (read_acquire (E := E) lk) (fun g => .ret (g, read_release))

noncomputable def write (lk : Handle T) :
    ITree E (WriteGuard T × (WriteGuard T → ITree E Unit)) :=
  ITree.bind (write_acquire (E := E) lk) (fun g => .ret (g, write_release))

noncomputable def read_deref (g : ReadGuard T) : ITree E T :=
  HeapAPI.load g.lock.data

noncomputable def write_deref (g : WriteGuard T) : ITree E T :=
  HeapAPI.load g.lock.data

noncomputable def write_deref_mut (g : WriteGuard T) :
    ITree E (T × (T → ITree E (WriteGuard T)) × (WriteGuard T → ITree E (WriteGuard T))) :=
  ITree.bind (HeapAPI.load (E := E) g.lock.data) (fun v =>
    .ret (v, (fun w => ITree.bind (HeapAPI.store g.lock.data w) (fun _ => .ret g)),
             (fun g' => .ret g')))

/-- Plain, like allocation: dropping demands the lock be free and owned, so no
other thread holds a reference and there is nothing to synchronise with.  A
yield here would also be unusable, since it needs the full mask. -/
noncomputable def drop (lk : Handle T) : ITree E Unit := do
  let _ ← HeapAPI.free lk.data
  HeapAPI.free lk.state

end Code

section Specs

open AeneasIris.AtomicWpi
open AeneasIris.Heap AeneasIris.HeapAPI
open AeneasIris.RwLockImpl
open AeneasIris.Conc (ConcH)

variable {GF : BundledGFunctors} [Iris.InvGS_gen hlc GF] [HeapGS.{0} GF] [RwSpinG GF]
variable {E : Effect.{1}} [StateE RustHeap.{0} -< E] [StepE.{1} -< E]
variable [Aeneas.Std.FailE.{1} -< E]
variable [Aeneas.Std.ConcE.{1} -< E]
variable {Hd : Handler E GF} [stateH heapInterp -<ₕ Hd]
variable {m : Mode} [stepH GF m -<ₕ Hd]
variable [ConcH GF -<ₕ Hd]
variable {T : Type}

omit [StateE RustHeap -< E] [StepE -< E] [Aeneas.Std.FailE -< E] in
/-- A yield in front of an operation is a yield in front of the whole block: it
lets a proof open the atomic update around the access *and* its continuation,
exactly as it would over the plain heap. -/
private theorem sync_bind {α β : Type} (op : ITree E α) (k : α → ITree E β) :
    (Conc.sync op >>= k) = Conc.sync (op >>= k) := by
  show ITree.bind (ITree.bind _ _) _ = ITree.bind _ (fun _ => ITree.bind _ _)
  simp only [ITree.bind_assoc']

omit [HeapGS GF] [RwSpinG GF] [StateE RustHeap -< E] [StepE -< E] [Aeneas.Std.FailE -< E] [Aeneas.Std.ConcE -< E] [stateH heapInterp -<ₕ Hd] [stepH GF m -<ₕ Hd] [ConcH GF -<ₕ Hd] in
private theorem wpi_aupd_choose {A B V : Type}
    (Eo Ei Em : CoPset) (t : ITree E V)
    (α : A → IProp GF) (β Ψ : A → B → IProp GF) (Φ : Post GF V)
    (hsub : Eo ⊆ Em) :
    atomicUpdate Eo Ei α β Ψ ⊢
      iprop((∀ x, α x -∗ wpi_mask GF Hd m t
              (fun v => iprop((α x ∗ (atomicUpdate Eo Ei α β Ψ -∗ Φ v))
                              ∨ (∃ y, β x y ∗ (Ψ x y -∗ Φ v)))) Ei) -∗
            wpi_mask GF Hd m t Φ Em) := by
  iintro HAU Hbody
  iapply (AeneasIris.wpi_reduce_mask (H := Hd) t Φ Em Ei)
  imod (Iris.aupd_acc _ _ _ Eo Ei Em hsub) $$ HAU with ⟨%x, Hα, Hclose⟩
  imodintro
  iapply (AeneasIris.wpi_wand (H := Hd) t
            (fun v => iprop((α x ∗ (atomicUpdate Eo Ei α β Ψ -∗ Φ v))
                            ∨ (∃ y, β x y ∗ (Ψ x y -∗ Φ v))))
            (fun v => iprop(|={Ei, Em}=> Φ v)) Ei) $$ [Hclose]
  · iintro %v HH
    icases HH with (⟨Hα', Hret⟩ | ⟨%y, Hβ, Hret⟩)
    · icases Hclose with ⟨Habort, -⟩
      imod Habort $$ Hα' with HAU'
      imodintro
      iapply Hret $$ HAU'
    · icases Hclose with ⟨-, Hcommit⟩
      imod Hcommit $$ Hβ with HΨ
      imodintro
      iapply Hret $$ HΨ
  · iapply Hbody $$ Hα


omit [HeapGS GF] in
private theorem rwRelease_last (γ : GName) (c : Loc) (Y s : RwPos) :
    iprop(iOwn (F := RwSpinF) γ (● rwFragR c 1 Y) ∗ iOwn (F := RwSpinF) γ (◯ rwFragR c 1 s))
      ⊢@{IProp GF} iprop(|==> (⌜Y = s⌝ ∗ iOwn (F := RwSpinF) γ (● rwLocR c)
                  ∗ iOwn (F := RwSpinF) γ (◯ rwLocR c))) := by
  refine (BI.and_intro iOwn_cmraValid_op .rfl).trans (BI.persistent_and_sep_mp.trans ?_)
  iintro ⟨%hv, H⟩
  ihave Hupd : iprop(|==> iOwn (F := RwSpinF) γ ((● rwLocR c : Auth RwRes) • ◯ rwLocR c)) $$ [H]
  · iapply (BI.entails_wand (iOwn_update_op
      (rwAuth_release c (rwFragR c 1 Y) (rwFragR c 1 s) (rwLocR c) (rwLocR_valid c)
        (rwFrame_zero c 1 Y s))))
    iexact H
  imod Hupd with H2
  imodintro
  isplitr [H2]
  · ipureintro; exact rwIncl_last hv
  · iapply (BI.entails_wand iOwn_op.mp); iexact H2


omit [HeapGS GF] in
private theorem rwRelease_more (γ : GName) (c : Loc) (N Y s : RwPos) :
    iprop(iOwn (F := RwSpinF) γ (● rwFragR c (1 + N) Y)
        ∗ iOwn (F := RwSpinF) γ (◯ rwFragR c 1 s))
      ⊢@{IProp GF} iprop(|==> (∃ Q' : RwPos, ⌜Y = s + Q'⌝ ∗ iOwn (F := RwSpinF) γ (● rwFragR c N Q')
                  ∗ iOwn (F := RwSpinF) γ (◯ rwLocR c))) := by
  refine (BI.and_intro iOwn_cmraValid_op .rfl).trans (BI.persistent_and_sep_mp.trans ?_)
  iintro ⟨%hv, H⟩
  obtain ⟨Q', hQ⟩ := rwIncl_more hv
  subst hQ
  ihave Hupd : iprop(|==> iOwn (F := RwSpinF) γ
      ((● rwFragR c N Q' : Auth RwRes) • ◯ rwLocR c)) $$ [H]
  · iapply (BI.entails_wand (iOwn_update_op
      (rwAuth_release c (rwFragR c (1 + N) (s + Q')) (rwFragR c 1 s) (rwFragR c N Q')
        (rwFragR_valid c N Q') (rwFrame_succ c s N Q'))))
    iexact H
  imod Hupd with H2
  imodintro
  iexists Q'
  isplitr [H2]
  · ipureintro; rfl
  · iapply (BI.entails_wand iOwn_op.mp); iexact H2


private def rdFrag (γ : GName) (c : Loc) (sq : Qp) (v : T) : IProp GF :=
  iprop(iOwn (F := RwSpinF) γ (◯ rwFragR c 1 (RwPos.ofQp sq)) ∗ pointsTo c (DFrac.own sq) v)


private theorem rwAcquire_free (γ : GName) (c : Loc) (v : T) :
    iprop(rwCore γ c LockState.free v) ⊢@{IProp GF}
      iprop(|==> (∃ sq : Qp, rwCore γ c (LockState.read 0) v ∗ rdFrag γ c sq v)) := by
  iintro Hcore
  iunfold rwCore at Hcore
  icases Hcore with ⟨Hauth, #Hloc, Hdat⟩
  simp only [rwAuth_none]
  have hup : (● rwLocR c : Auth RwRes) ~~>
      ((● rwFragR c 1 (RwPos.ofQp (1 : Qp).half))
        • ◯ rwFragR c 1 (RwPos.ofQp (1 : Qp).half)) := by
    have h := rwAuth_alloc (rwLocR c) (rwFragR c 1 (RwPos.ofQp (1 : Qp).half))
      (by rw [rwFragR_op_locR]; exact rwFragR_valid _ _ _)
    rwa [rwFragR_op_locR] at h
  imod (iOwn_update (F := RwSpinF) (γ := γ) hup) $$ [Hauth] with Hnew
  · iexact Hauth
  imodintro
  ihave Hpair : iprop(iOwn (F := RwSpinF) γ (● rwFragR c 1 (RwPos.ofQp (1 : Qp).half))
      ∗ iOwn (F := RwSpinF) γ (◯ rwFragR c 1 (RwPos.ofQp (1 : Qp).half))) $$ [Hnew]
  · iapply (BI.entails_wand iOwn_op.mp); iexact Hnew
  icases Hpair with ⟨Hauth2, Hfrag⟩
  ihave Hd2 : iprop(pointsTo c (DFrac.own (1 : Qp).half) v
      ∗ pointsTo c (DFrac.own (1 : Qp).half) v) $$ [Hdat]
  · have hh := (pointsTo_split (GF := GF) c (1 : Qp).half (1 : Qp).half v).1
    rw [Qp.half_add_half] at hh
    iapply (BI.entails_wand hh); iexact Hdat
  icases Hd2 with ⟨Hd2a, Hd2b⟩
  iexists (1 : Qp).half
  isplitl [Hauth2 Hd2a]
  · iunfold rwCore
    simp only [rwAuth_some, RwPos.ofSucc_zero]
    iexists (1 : Qp).half
    iexists (1 : Qp).half
    isplitr [Hauth2 Hd2a]
    · ipureintro; exact Qp.half_add_half 1
    · isplitl [Hauth2]
      · iexact Hauth2
      · isplitr [Hd2a]
        · iexact Hloc
        · iexact Hd2a
  · iunfold rdFrag
    isplitl [Hfrag]
    · iexact Hfrag
    · iexact Hd2b


private theorem rwAcquire_read (γ : GName) (c : Loc) (m : Nat) (v : T) :
    iprop(rwCore γ c (LockState.read m) v) ⊢@{IProp GF}
      iprop(|==> (∃ sq : Qp, rwCore γ c (LockState.read (m + 1)) v ∗ rdFrag γ c sq v)) := by
  iintro Hcore
  iunfold rwCore at Hcore
  icases Hcore with ⟨%qout, %qrest, %hsum, Hauth, #Hloc, Hdat⟩
  simp only [rwAuth_some]
  have hb : rwFragR c 1 (RwPos.ofQp qrest.half) • rwFragR c (RwPos.ofSucc m) (RwPos.ofQp qout)
      = rwFragR c (RwPos.ofSucc (m + 1)) (RwPos.ofQp (qout + qrest.half)) := by
    rw [rwFragR_op]
    have h1 : (1 : RwPos) + RwPos.ofSucc m = RwPos.ofSucc (m + 1) := (RwPos.ofSucc_succ m).symm
    have h2 : RwPos.ofQp qrest.half + RwPos.ofQp qout = RwPos.ofQp (qout + qrest.half) :=
      RwPos.ext (by simp only [RwPos.val_add, RwPos.ofQp_val, Qp.val_add]; grind)
    rw [h1, h2]
  have hup : (● rwFragR c (RwPos.ofSucc m) (RwPos.ofQp qout) : Auth RwRes) ~~>
      ((● rwFragR c (RwPos.ofSucc (m + 1)) (RwPos.ofQp (qout + qrest.half)))
        • ◯ rwFragR c 1 (RwPos.ofQp qrest.half)) := by
    have h := rwAuth_alloc (rwFragR c (RwPos.ofSucc m) (RwPos.ofQp qout))
      (rwFragR c 1 (RwPos.ofQp qrest.half)) (by rw [hb]; exact rwFragR_valid _ _ _)
    rwa [hb] at h
  imod (iOwn_update (F := RwSpinF) (γ := γ) hup) $$ [Hauth] with Hnew
  · iexact Hauth
  imodintro
  ihave Hpair : iprop(iOwn (F := RwSpinF) γ
        (● rwFragR c (RwPos.ofSucc (m + 1)) (RwPos.ofQp (qout + qrest.half)))
      ∗ iOwn (F := RwSpinF) γ (◯ rwFragR c 1 (RwPos.ofQp qrest.half))) $$ [Hnew]
  · iapply (BI.entails_wand iOwn_op.mp); iexact Hnew
  icases Hpair with ⟨Hauth2, Hfrag⟩
  ihave Hd2 : iprop(pointsTo c (DFrac.own qrest.half) v
      ∗ pointsTo c (DFrac.own qrest.half) v) $$ [Hdat]
  · have hh := (pointsTo_split (GF := GF) c qrest.half qrest.half v).1
    rw [Qp.half_add_half] at hh
    iapply (BI.entails_wand hh); iexact Hdat
  icases Hd2 with ⟨Hd2a, Hd2b⟩
  have hsum2 : (qout + qrest.half) + qrest.half = (1 : Qp) := by
    simp only [Qp.ext_iff, Qp.val_add, Qp.val_one] at *
    grind
  iexists qrest.half
  isplitl [Hauth2 Hd2a]
  · iunfold rwCore
    simp only [rwAuth_some]
    iexists (qout + qrest.half)
    iexists qrest.half
    isplitr [Hauth2 Hd2a]
    · ipureintro; exact hsum2
    · isplitl [Hauth2]
      · iexact Hauth2
      · isplitr [Hd2a]
        · iexact Hloc
        · iexact Hd2a
  · iunfold rdFrag
    isplitl [Hfrag]
    · iexact Hfrag
    · iexact Hd2b


theorem new_spec (v : T) (M : CoPset) :
    ⦃ emp ⦄ (new (E := E) v) @ Hd ; m ; M
    ⦃ lk, ∃ γ, isRwLock γ lk .free v ⦄ :=
  RwLockImpl.new_spec v M

theorem write_release_spec (γ : GName) (g : WriteGuard T) (v₁ : T) :
    ⊢ writeGuard γ g v₁ -∗
      ⟪ ∀ v₀, isRwLock γ g.lock .write v₀ ⟫
        Hd m (write_release (E := E) g) @ (∅ : CoPset)
      ⟪ isRwLock γ g.lock .free v₁ | RET () ⟫ :=
  RwLockImpl.write_release_spec γ g v₁

omit [Aeneas.Std.FailE -< E] in
theorem try_write_acquire_spec (γ : GName) (lk : Handle T) :
    ⊢ ⟪ ∀ s v, isRwLock γ lk s v ⟫ Hd m (try_write_acquire (E := E) lk) @ (∅ : CoPset)
        ⟪ isRwLock γ lk (if s = .free then .write else s) v
        | RET (if s = .free then some (mkWriteGuard lk) else none)
        ; if s = .free then writeGuard γ ⟨lk⟩ v else emp ⟫ := by
  simp only [atomicWpi]
  iintro %Φ HAU
  simp only [try_write_acquire]
  ibind
  simp only [AtomicHeapAPI.cas]
  iapply Conc.wpi_sync
  iaupd_commit HAU as ⟨s, v⟩ with Hlock
  iunfold isRwLock at Hlock
  icases Hlock with ⟨Hst, Hcore⟩
  by_cases hs : s = LockState.free
  · subst hs
    simp only [LockState.word]
    istep
    iunfold rwCore at Hcore
    icases Hcore with ⟨Hauth, #Hloc, Hdata⟩
    iexists ()
    isplitl [Hst Hauth]
    · iunfold isRwLock
      isplitl [Hst]
      · simp only [if_true, LockState.word]; iexact Hst
      · simp only [if_true]; iunfold rwCore
        isplitl [Hauth]
        · iexact Hauth
        · iexact Hloc
    · iintro HΨ
      simp only [reduceIte, AtomicWpi.wandM_some]
      istep
      ihave HG : writeGuard γ ⟨lk⟩ v $$ [Hdata]
      · iunfold writeGuard
        isplitl [Hdata]
        · iexact Hdata
        · iexact Hloc
      have hite : (if LockState.free = LockState.free
                   then some (mkWriteGuard lk) else none) = some (mkWriteGuard lk) := rfl
      simp only [hite]
      simp only [mkWriteGuard]
      iapply HΨ $$ HG
      · exact ()
  · irule with HeapAPI.cas_fail_body_spec
    · iexists ()
      isplitl [Hst Hcore]
      · ihave HL : isRwLock γ lk s v $$ [Hst Hcore]
        · iunfold isRwLock
          isplitl [Hst]
          · iexact Hst
          · iexact Hcore
        have hite : (if s = LockState.free then LockState.write else s) = s :=
          if_neg hs
        have hEq : isRwLock (GF := GF) γ lk
            (if s = LockState.free then LockState.write else s) v
            = isRwLock γ lk s v := by rw [hite]
        simp only [hEq]
        iexact HL
      · iintro HΨ
        istep
        have hite : (if s = LockState.free then some (mkWriteGuard lk) else none)
                  = none := if_neg hs
        have hemp : (if s = LockState.free then writeGuard (GF := GF) γ (⟨lk⟩ : WriteGuard T) v
                     else iprop(emp)) = iprop(emp) := if_neg hs
        simp only [hite, hemp, AtomicWpi.wandM_some]
        iapply HΨ
        · first | itrivial | exact ()
        · itrivial
    · intro h
      have h2 := congrArg (fun w : Aeneas.Std.Val.{0} => Aeneas.Std.Val.unpackO Int w) h
      simp only [Aeneas.Std.Val.unpackO_pack, Option.some.injEq] at h2
      exact hs (LockState.word_injective (show s.word = LockState.free.word from h2))

theorem try_write_spec (γ : GName) (lk : Handle T) :
    ⊢ ⟪ ∀ s v, isRwLock γ lk s v ⟫ Hd m (try_write (E := E) lk) @ (∅ : CoPset)
        ⟪ isRwLock γ lk (if s = .free then .write else s) v
        | g rel, RET (if s = .free then some (g, rel) else none)
        ; if s = .free then
            writeGuard γ g v ∗
            □ (∀ v₁ : T, writeGuard γ g v₁ -∗
                 ⟪ ∀ v₀, isRwLock γ lk .write v₀ ⟫
                     Hd m (rel g) @ (∅ : CoPset)
                   ⟪ isRwLock γ lk .free v₁ | RET () ⟫)
          else emp ⟫ := by
  simp only [atomicWpi]
  iintro %Φ HAU
  simp only [try_write, try_write_acquire]
  ibind
  simp only [AtomicHeapAPI.cas, sync_bind]
  iapply Conc.wpi_sync
  iaupd_commit HAU as ⟨s, v⟩ with Hlock
  iunfold isRwLock at Hlock
  icases Hlock with ⟨Hst, Hcore⟩
  by_cases hs : s = LockState.free
  · subst hs
    simp only [LockState.word]
    istep
    simp only [if_true]
    iunfold rwCore at Hcore
    icases Hcore with ⟨Hauth, #Hloc, Hdata⟩
    istep
    iexists ()
    isplitl [Hst Hauth]
    · iunfold isRwLock
      isplitl [Hst]
      · simp only [if_true, LockState.word]; iexact Hst
      · simp only [if_true]; iunfold rwCore
        isplitl [Hauth]
        · iexact Hauth
        · iexact Hloc
    · iintro HΨ
      simp only [reduceIte, AtomicWpi.wandM_some]
      istep
      ihave HG : writeGuard γ ⟨lk⟩ v $$ [Hdata]
      · iunfold writeGuard
        isplitl [Hdata]
        · iexact Hdata
        · iexact Hloc
      have hite : ∀ (y : WriteGuard T) (z : WriteGuard T → ITree E Unit),
          (if LockState.free = LockState.free then some (y, z) else none)
            = some (y, z) := fun _ _ => rfl
      simp only [Option.map_some, hite]
      iapply HΨ $$ %((⟨lk⟩ : WriteGuard T), write_release (E := E))
      isplitl [HG]
      · iexact HG
      · iintro !> %v₁ HG₁
        have HR := write_release_spec (Hd := Hd) (m := m) γ (⟨lk⟩ : WriteGuard T) v₁
        simp only [atomicWpi] at HR
        iapply HR
        iexact HG₁
  · irule with HeapAPI.cas_fail_body_spec
    · simp only [Bool.false_eq_true, if_false]
      istep
      iexists ()
      isplitl [Hst Hcore]
      · ihave HL : isRwLock γ lk s v $$ [Hst Hcore]
        · iunfold isRwLock
          isplitl [Hst]
          · iexact Hst
          · iexact Hcore
        have hite : (if s = LockState.free then LockState.write else s) = s :=
          if_neg hs
        have hEq : isRwLock (GF := GF) γ lk
            (if s = LockState.free then LockState.write else s) v
            = isRwLock γ lk s v := by rw [hite]
        simp only [hEq]
        iexact HL
      · iintro HΨ
        simp only [AtomicWpi.wandM_some]
        istep
        have hite : ∀ (y : WriteGuard T) (z : WriteGuard T → ITree E Unit),
            (if s = LockState.free then some (y, z) else none) = none :=
          fun _ _ => if_neg hs
        simp only [Option.map_none, hite]
        iapply HΨ $$ %((⟨lk⟩ : WriteGuard T), write_release (E := E))
        simp only [if_neg hs]
        itrivial
    · intro h
      have h2 := congrArg (fun w : Aeneas.Std.Val.{0} => Aeneas.Std.Val.unpackO Int w) h
      simp only [Aeneas.Std.Val.unpackO_pack, Option.some.injEq] at h2
      exact hs (LockState.word_injective (show s.word = LockState.free.word from h2))


variable [AeneasIris.Step.stepH GF .part -<ₕ Hd]

theorem write_spec (γ : GName) (lk : Handle T) :
    ⊢ ⟪ ∀ s v, isRwLock γ lk s v ⟫ Hd .part (write (E := E) lk) @ (∅ : CoPset)
        ⟪ isRwLock γ lk .write v ∗ ⌜s = .free⌝
        | g rel, RET (g, rel)
        ; writeGuard γ g v ∗
          □ (∀ v₁ : T, writeGuard γ g v₁ -∗
               ⟪ ∀ v₀, isRwLock γ lk .write v₀ ⟫ Hd .part (rel g) @ (∅ : CoPset)
                   ⟪ isRwLock γ lk .free v₁ | RET () ⟫) ⟫ := by
  simp only [atomicWpi]
  iintro %Φ HAU
  simp only [write, write_acquire]
  iapply (wpi_bind (H := Hd)
    (AeneasIris.Conc.waitUntil (try_write_acquire (E := E) lk)) _ _ ⊤)
  iloeb as IH
  iunfold Conc.waitUntil
  simp only [try_write_acquire]
  ibind
  simp only [AtomicHeapAPI.cas, sync_bind]
  iapply Conc.wpi_sync
  iapply (wpi_aupd_choose (hsub := by aupd_mask)) $$ HAU
  iintro %iaupdPacked Hlock
  obtain ⟨s, v⟩ := iaupdPacked
  iunfold isRwLock at Hlock
  icases Hlock with ⟨Hst, Hcore⟩
  by_cases hs : s = LockState.free
  · subst hs
    simp only [LockState.word]
    istep
    simp only [if_true]
    iunfold rwCore at Hcore
    icases Hcore with ⟨Hauth, #Hloc, Hdata⟩
    istep
    iright
    iexists ()
    isplitl [Hst Hauth]
    · isplitl [Hst Hauth]
      · iunfold isRwLock
        isplitl [Hst]
        · simp only [LockState.word]; iexact Hst
        · iunfold rwCore
          isplitl [Hauth]
          · iexact Hauth
          · iexact Hloc
      · itrivial
    · iintro HΨ
      simp only [AtomicWpi.wandM_some]
      istep
      istep
      ihave HG : writeGuard γ ⟨lk⟩ v $$ [Hdata]
      · iunfold writeGuard
        isplitl [Hdata]
        · iexact Hdata
        · iexact Hloc
      iapply HΨ $$ %((⟨lk⟩ : WriteGuard T), write_release (E := E))
      isplitl [HG]
      · iexact HG
      · iintro !> %v₁ HG₁
        have HR := write_release_spec (Hd := Hd) (m := Mode.part) γ (⟨lk⟩ : WriteGuard T) v₁
        simp only [atomicWpi] at HR
        iapply HR
        iexact HG₁
  · irule with HeapAPI.cas_fail_body_spec
    · simp only [Bool.false_eq_true, if_false]
      istep
      ileft
      isplitl [Hst Hcore]
      · iunfold isRwLock
        isplitl [Hst]
        · iexact Hst
        · iexact Hcore
      · iintro HAU'
        iapply (wpi_bind (H := Hd) AeneasIris.Conc.yieldU _ _ ⊤)
        iapply (AeneasIris.Conc.wpi_yieldU (H := Hd) _)
        istep
        iapply IH $$ HAU'
    · intro h
      have h2 := congrArg (fun w : Aeneas.Std.Val.{0} => Aeneas.Std.Val.unpackO Int w) h
      simp only [Aeneas.Std.Val.unpackO_pack, Option.some.injEq] at h2
      exact hs (LockState.word_injective (show s.word = LockState.free.word from h2))


theorem read_release_spec (γ : GName) (g : ReadGuard T) (v : T) :
    ⊢ readGuardFrac γ g 1 v -∗
      ⟪ ∀ s, isRwLock γ g.lock s v ⟫
        Hd .part (read_release (E := E) g) @ (∅ : CoPset)
      ⟪ (isRwLock γ g.lock .free v ∗ ⌜s = .read 0⌝) ∨
        (∃ n : Nat, isRwLock γ g.lock (.read n) v ∗ ⌜s = .read (n + 1)⌝)
      | RET () ⟫ := by
  iintro HR
  simp only [atomicWpi]
  iintro %Φ HAU
  simp only [read_release, AtomicHeapAPI.faa, sync_bind]
  iapply Conc.wpi_sync
  iapply (wpi_aupd_choose (hsub := by aupd_mask)) $$ HAU
  iintro %s₁ Hlock
  rcases s₁ with _ | mm | _
  · ihave Hpair : iprop(isRwLock γ g.lock LockState.free v ∗ readGuardFrac γ g 1 v) $$ [Hlock HR]
    · isplitl [Hlock]
      · iexact Hlock
      · iexact HR
    ihave %hbad := readGuardFrac_state γ g.lock LockState.free g 1 v v $$ Hpair
    exact absurd hbad (by rintro ⟨k, hk⟩; cases hk)
  · iunfold isRwLock at Hlock
    icases Hlock with ⟨Hst, Hcore⟩
    iunfold rwCore at Hcore
    icases Hcore with ⟨%qout, %qrest, %hsum, Hauth, #Hloc, Hdat⟩
    iunfold readGuardFrac at HR
    icases HR with ⟨%sh, Hfrag, Hdr⟩
    istep
    rcases mm with _ | k
    · simp only [rwAuth_some, RwPos.ofSucc_zero, RwPos.ofQp_one] at *
      iapply (wpi_update (H := Hd) _ _ _).mp
      imod (rwRelease_last γ g.lock.data (RwPos.ofQp qout) (RwPos.ofQp sh)) $$ [Hauth Hfrag]
        with ⟨%hqs, Hauth2, Hloc2⟩
      · isplitl [Hauth]
        · iexact Hauth
        · iexact Hfrag
      imodintro
      have hq : qout = sh := RwPos.ofQp_inj hqs
      have hfr : qrest + sh = (1 : Qp) := by
        subst hq
        simp only [Qp.ext_iff, Qp.val_add, Qp.val_one] at *
        grind
      ihave Hfull : iprop(pointsTo g.lock.data (DFrac.own (1 : Qp)) v) $$ [Hdat Hdr]
      · simp only [← hfr]
        iapply (BI.entails_wand (pointsTo_split (GF := GF) g.lock.data qrest sh v).2)
        isplitl [Hdat]
        · iexact Hdat
        · iexact Hdr
      istep
      iright
      iexists ()
      isplitl [Hst Hauth2 Hloc2 Hfull]
      · ileft
        isplitl [Hst Hauth2 Hloc2 Hfull]
        · iunfold isRwLock
          isplitl [Hst]
          · simp only [LockState.word] at *
            have hw0 : ((0 : Nat) : Int) + 1 + -1 = (0 : Int) := by grind
            simp only [hw0]
            iexact Hst
          · iunfold rwCore
            simp only [rwAuth_none]
            isplitl [Hauth2]
            · iexact Hauth2
            · isplitl [Hloc2]
              · iexact Hloc2
              · iexact Hfull
        · itrivial
      · iintro HΨ
        simp only [AtomicWpi.wandM_none]
        iapply HΨ $$ %()
    · simp only [rwAuth_some, RwPos.ofSucc_succ, RwPos.ofQp_one] at *
      iapply (wpi_update (H := Hd) _ _ _).mp
      imod (rwRelease_more γ g.lock.data (RwPos.ofSucc k) (RwPos.ofQp qout) (RwPos.ofQp sh))
        $$ [Hauth Hfrag] with ⟨%Q', %hqs, Hauth2, Hloc2⟩
      · isplitl [Hauth]
        · iexact Hauth
        · iexact Hfrag
      imodintro
      have hQpos : (0 : Rat) < Q'.val := Q'.pos
      have hfr : (⟨Q'.val, hQpos⟩ : Qp) + (qrest + sh) = (1 : Qp) := by
        have h1 := congrArg RwPos.val hqs
        simp only [RwPos.ofQp_val, RwPos.val_add] at h1
        simp only [Qp.ext_iff, Qp.val_add, Qp.val_one] at *
        grind
      ihave Hrest : iprop(pointsTo g.lock.data (DFrac.own (qrest + sh)) v) $$ [Hdat Hdr]
      · iapply (BI.entails_wand (pointsTo_split (GF := GF) g.lock.data qrest sh v).2)
        isplitl [Hdat]
        · iexact Hdat
        · iexact Hdr
      istep
      iright
      iexists ()
      isplitl [Hst Hauth2 Hloc2 Hrest]
      · iright
        iexists k
        isplitl [Hst Hauth2 Hloc2 Hrest]
        · iunfold isRwLock
          isplitl [Hst]
          · simp only [LockState.word] at *
            push_cast at *
            have hwk : ((k : Nat) : Int) + 1 + 1 + -1 = ((k : Nat) : Int) + 1 := by grind
            simp only [hwk]
            iexact Hst
          · iunfold rwCore
            have hQ' : RwPos.ofQp (⟨Q'.val, hQpos⟩ : Qp) = Q' := RwPos.ext rfl
            simp only [rwAuth_some]
            iexists (⟨Q'.val, hQpos⟩ : Qp)
            iexists (qrest + sh)
            isplitr [Hauth2 Hloc2 Hrest]
            · ipureintro; exact hfr
            · isplitl [Hauth2]
              · simp only [hQ']
                iexact Hauth2
              · isplitl [Hloc2]
                · iexact Hloc2
                · iexact Hrest
        · itrivial
      · iintro HΨ
        simp only [AtomicWpi.wandM_none]
        iapply HΨ $$ %()
  · ihave Hpair : iprop(isRwLock γ g.lock LockState.write v ∗ readGuardFrac γ g 1 v) $$ [Hlock HR]
    · isplitl [Hlock]
      · iexact Hlock
      · iexact HR
    ihave %hbad := readGuardFrac_state γ g.lock LockState.write g 1 v v $$ Hpair
    exact absurd hbad (by rintro ⟨k, hk⟩; cases hk)
private theorem read_release_box (γ : GName) (lk : Handle T) (v : T) :
    ⊢@{IProp GF} □ (readGuardFrac γ (⟨lk⟩ : ReadGuard T) 1 v -∗
      ⟪ ∀ s', isRwLock γ lk s' v ⟫
          Hd .part (read_release (E := E) (⟨lk⟩ : ReadGuard T)) @ (∅ : CoPset)
        ⟪ (isRwLock γ lk .free v ∗ ⌜s' = .read 0⌝) ∨
          (∃ n : Nat, isRwLock γ lk (.read n) v ∗ ⌜s' = .read (n + 1)⌝)
        | RET () ⟫) := by
  iintro !> HRG
  have HRR := read_release_spec (Hd := Hd) γ (⟨lk⟩ : ReadGuard T) v
  iapply HRR
  iexact HRG


/-- The read acquisition on its own: it retries a lost swap and reports only a
lock held for writing.  Both `try_read` and the blocking `read` are this plus a
continuation. -/
private theorem try_read_acquire_spec (γ : GName) (lk : Handle T) :
    ⊢ ⟪ ∀ s v, isRwLock γ lk s v ⟫
        Hd Mode.part (try_read_acquire (E := E) lk) @ (∅ : CoPset)
      ⟪ isRwLock γ lk (match s with
                       | .free => .read 0
                       | .read n => .read (n + 1)
                       | .write => .write) v
      | g, RET (if s = LockState.write then none else some g)
      ; if s = LockState.write then emp else readGuardFrac γ g 1 v ⟫ := by
  simp only [atomicWpi]
  iintro %Φ HAU
  simp only [try_read_acquire]
  iloeb as IH
  iunfold ITree.iter
  ibind
  ibind
  simp only [AtomicHeapAPI.load]
  iapply Conc.wpi_sync
  iapply (wpi_aupd_choose (hsub := by aupd_mask)) $$ HAU
  iintro %sv Hlock
  obtain ⟨s₁, v₁⟩ := sv
  iunfold isRwLock at Hlock
  icases Hlock with ⟨Hst, Hcore⟩
  istep
  rcases s₁ with _ | mm | _
  · ileft
    isplitl [Hst Hcore]
    · iunfold isRwLock
      isplitl [Hst]
      · simp only [LockState.word]
        iexact Hst
      · iexact Hcore
    · iintro HAU
      simp only [LockState.word, if_neg (show ¬((0 : Int) < 0) from by grind)]
      ibind
      simp only [AtomicHeapAPI.cas]
      iapply Conc.wpi_sync
      iapply (wpi_aupd_choose (hsub := by aupd_mask)) $$ HAU
      iintro %sv2 Hlock2
      obtain ⟨s₂, v₂⟩ := sv2
      iunfold isRwLock at Hlock2
      icases Hlock2 with ⟨Hst2, Hcore2⟩
      by_cases hne : s₂ = LockState.free
      · subst hne
        simp only [LockState.word]
        iapply (HeapAPI.wpi_cas_succ (Hd := Hd) (m := Mode.part) (E := E) lk.state
          (0 : Int) ((0 : Int) + 1))
        iapply (AeneasIris.Step.lat_intro Mode.part _)
        isplitl [Hst2]
        · iexact Hst2
        · iintro Hst2
          imod (rwAcquire_free γ lk.data v₂) $$ [Hcore2] with ⟨%sq, Hcore3, Hfrag⟩
          · iexact Hcore2
          imodintro
          iright
          iexists ()
          isplitl [Hst2 Hcore3]
          · iunfold isRwLock
            simp only [LockState.word]
            isplitl [Hst2]
            · iexact Hst2
            · iexact Hcore3
          · iintro HΨ
            have hne1 : ∀ y : ReadGuard T,
                (if LockState.free = LockState.write then none else some y) = some y :=
              fun _ => if_neg (by intro h; cases h)
            have hne2 : ∀ P : IProp GF,
                (if LockState.free = LockState.write then iprop(emp) else P) = P :=
              fun _ => if_neg (by intro h; cases h)
            simp only [hne1, hne2, AtomicWpi.wandM_some]
            iret
            iret
            iapply HΨ $$ %(⟨lk⟩ : ReadGuard T)
            iunfold readGuardFrac
            iexists sq
            simp only [RwPos.ofQp_one]
            iunfold rdFrag at Hfrag
            iexact Hfrag
      · iapply (HeapAPI.wpi_cas_fail (Hd := Hd) (m := Mode.part) (E := E) lk.state
          s₂.word (0 : Int) ((0 : Int) + 1) (DFrac.own 1)
          (by intro h; exact hne (LockState.word_injective h)))
        iapply (AeneasIris.Step.lat_intro Mode.part _)
        isplitl [Hst2]
        · iexact Hst2
        · iintro Hst2
          imodintro
          ileft
          isplitl [Hst2 Hcore2]
          · iunfold isRwLock
            isplitl [Hst2]
            · iexact Hst2
            · iexact Hcore2
          · iintro HAU
            simp only [Bool.false_eq_true, if_false]
            iret
            dsimp only
            iapply IH $$ HAU
  · ileft
    isplitl [Hst Hcore]
    · iunfold isRwLock
      isplitl [Hst]
      · simp only [LockState.word]
        iexact Hst
      · iexact Hcore
    · iintro HAU
      simp only [LockState.word,
        if_neg (show ¬(((mm : Nat) : Int) + 1 < 0) from by grind)]
      ibind
      simp only [AtomicHeapAPI.cas]
      iapply Conc.wpi_sync
      iapply (wpi_aupd_choose (hsub := by aupd_mask)) $$ HAU
      iintro %sv2 Hlock2
      obtain ⟨s₂, v₂⟩ := sv2
      iunfold isRwLock at Hlock2
      icases Hlock2 with ⟨Hst2, Hcore2⟩
      by_cases hne : s₂ = LockState.read mm
      · subst hne
        simp only [LockState.word]
        iapply (HeapAPI.wpi_cas_succ (Hd := Hd) (m := Mode.part) (E := E) lk.state
          (((mm : Nat) : Int) + 1) ((((mm : Nat) : Int) + 1) + 1))
        iapply (AeneasIris.Step.lat_intro Mode.part _)
        isplitl [Hst2]
        · iexact Hst2
        · iintro Hst2
          imod (rwAcquire_read γ lk.data mm v₂) $$ [Hcore2] with ⟨%sq, Hcore3, Hfrag⟩
          · iexact Hcore2
          imodintro
          iright
          iexists ()
          isplitl [Hst2 Hcore3]
          · iunfold isRwLock
            have hcast : ((mm : Nat) : Int) + 1 + 1 = ((mm + 1 : Nat) : Int) + 1 := by
              push_cast; ring
            rw [hcast]
            dsimp only [LockState.word]
            isplitl [Hst2]
            · iexact Hst2
            · iexact Hcore3
          · iintro HΨ
            have hne1 : ∀ y : ReadGuard T,
                (if LockState.read mm = LockState.write then none else some y) = some y :=
              fun _ => if_neg (by intro h; cases h)
            have hne2 : ∀ P : IProp GF,
                (if LockState.read mm = LockState.write then iprop(emp) else P) = P :=
              fun _ => if_neg (by intro h; cases h)
            simp only [hne1, hne2, AtomicWpi.wandM_some]
            iret
            iret
            iapply HΨ $$ %(⟨lk⟩ : ReadGuard T)
            iunfold readGuardFrac
            iexists sq
            simp only [RwPos.ofQp_one]
            iunfold rdFrag at Hfrag
            iexact Hfrag
      · iapply (HeapAPI.wpi_cas_fail (Hd := Hd) (m := Mode.part) (E := E) lk.state
          s₂.word (((mm : Nat) : Int) + 1) ((((mm : Nat) : Int) + 1) + 1) (DFrac.own 1)
          (by intro h; exact hne (LockState.word_injective h)))
        iapply (AeneasIris.Step.lat_intro Mode.part _)
        isplitl [Hst2]
        · iexact Hst2
        · iintro Hst2
          imodintro
          ileft
          isplitl [Hst2 Hcore2]
          · iunfold isRwLock
            isplitl [Hst2]
            · iexact Hst2
            · iexact Hcore2
          · iintro HAU
            simp only [Bool.false_eq_true, if_false]
            iret
            dsimp only
            iapply IH $$ HAU
  · simp only [LockState.word]
    have hprog : ∀ A B : ITree E (Unit ⊕ Option (ReadGuard T)),
        (if (-1 : Int) < 0 then A else B) = A := fun _ _ => if_pos (by grind)
    have hret : ∀ z : ReadGuard T,
        (if LockState.write = LockState.write then none else some z) = none :=
      fun _ => if_pos rfl
    iright
    iexists ()
    isplitl [Hst Hcore]
    · iunfold isRwLock
      isplitl [Hst]
      · simp only [LockState.word]
        iexact Hst
      · iexact Hcore
    · iintro HΨ
      simp only [hprog]
      iret
      simp only [hret, AtomicWpi.wandM_some]
      iret
      iapply HΨ $$ %(⟨lk⟩ : ReadGuard T)
      itrivial
theorem try_read_spec (γ : GName) (lk : Handle T) :
    ⊢ ⟪ ∀ s v, isRwLock γ lk s v ⟫ Hd Mode.part (try_read (E := E) lk) @ (∅ : CoPset)
        ⟪ isRwLock γ lk (match s with
                         | .free => .read 0
                         | .read n => .read (n + 1)
                         | .write => .write) v
        | g rel, RET (if s = .write then none else some (g, rel))
        ; if s = .write then emp else
            readGuardFrac γ g 1 v ∗
            □ (readGuardFrac γ g 1 v -∗
                 ⟪ ∀ s', isRwLock γ lk s' v ⟫
                     Hd .part (rel g) @ (∅ : CoPset)
                   ⟪ (isRwLock γ lk .free v ∗ ⌜s' = .read 0⌝) ∨
                     (∃ n : Nat, isRwLock γ lk (.read n) v ∗ ⌜s' = .read (n + 1)⌝)
                   | RET () ⟫) ⟫ := by
  simp only [atomicWpi]
  iintro %Φ HAU
  simp only [try_read, try_read_acquire]
  ibind
  iloeb as IH
  iunfold ITree.iter
  ibind
  ibind
  simp only [AtomicHeapAPI.load]
  iapply Conc.wpi_sync
  iapply (wpi_aupd_choose (hsub := by aupd_mask)) $$ HAU
  iintro %sv Hlock
  obtain ⟨s₁, v₁⟩ := sv
  iunfold isRwLock at Hlock
  icases Hlock with ⟨Hst, Hcore⟩
  istep
  rcases s₁ with _ | mm | _
  · ileft
    isplitl [Hst Hcore]
    · iunfold isRwLock
      isplitl [Hst]
      · simp only [LockState.word]
        iexact Hst
      · iexact Hcore
    · iintro HAU
      simp only [LockState.word, if_neg (show ¬((0 : Int) < 0) from by grind)]
      ibind
      simp only [AtomicHeapAPI.cas]
      iapply Conc.wpi_sync
      iapply (wpi_aupd_choose (hsub := by aupd_mask)) $$ HAU
      iintro %sv2 Hlock2
      obtain ⟨s₂, v₂⟩ := sv2
      iunfold isRwLock at Hlock2
      icases Hlock2 with ⟨Hst2, Hcore2⟩
      by_cases hne : s₂ = LockState.free
      · subst hne
        simp only [LockState.word]
        iapply (HeapAPI.wpi_cas_succ (Hd := Hd) (m := Mode.part) (E := E) lk.state
          (0 : Int) ((0 : Int) + 1))
        iapply (AeneasIris.Step.lat_intro Mode.part _)
        isplitl [Hst2]
        · iexact Hst2
        · iintro Hst2
          imod (rwAcquire_free γ lk.data v₂) $$ [Hcore2] with ⟨%sq, Hcore3, Hfrag⟩
          · iexact Hcore2
          imodintro
          iright
          iexists ()
          isplitl [Hst2 Hcore3]
          · iunfold isRwLock
            simp only [LockState.word]
            isplitl [Hst2]
            · iexact Hst2
            · iexact Hcore3
          · iintro HΨ
            have hne1 : ∀ (y : ReadGuard T) (z : ReadGuard T → ITree E Unit),
                (if LockState.free = LockState.write then none else some (y, z)) = some (y, z) :=
              fun _ _ => if_neg (by intro h; cases h)
            have hne2 : ∀ P : IProp GF,
                (if LockState.free = LockState.write then iprop(emp) else P) = P :=
              fun _ => if_neg (by intro h; cases h)
            simp only [hne1, hne2, AtomicWpi.wandM_some, Option.map]
            iret
            iret
            iret
            iapply HΨ $$ %((⟨lk⟩ : ReadGuard T), read_release (E := E))
            isplitl [Hfrag]
            · iunfold readGuardFrac
              iexists sq
              simp only [RwPos.ofQp_one]
              iunfold rdFrag at Hfrag
              iexact Hfrag
            · have hproj :
                  ((((⟨lk⟩ : ReadGuard T), read_release (E := E)) :
                      ReadGuard T × (ReadGuard T → ITree E Unit)).2
                    (((⟨lk⟩ : ReadGuard T), read_release (E := E)) :
                      ReadGuard T × (ReadGuard T → ITree E Unit)).1)
                  = read_release (E := E) (⟨lk⟩ : ReadGuard T) := rfl
              iintro !> HRG
              rw [hproj]
              have HRR := read_release_spec (Hd := Hd) γ (⟨lk⟩ : ReadGuard T) v₂
              simp only [atomicWpi] at HRR
              iapply HRR
              iexact HRG
      · iapply (HeapAPI.wpi_cas_fail (Hd := Hd) (m := Mode.part) (E := E) lk.state
          s₂.word (0 : Int) ((0 : Int) + 1) (DFrac.own 1)
          (by intro h; exact hne (LockState.word_injective h)))
        iapply (AeneasIris.Step.lat_intro Mode.part _)
        isplitl [Hst2]
        · iexact Hst2
        · iintro Hst2
          imodintro
          ileft
          isplitl [Hst2 Hcore2]
          · iunfold isRwLock
            isplitl [Hst2]
            · iexact Hst2
            · iexact Hcore2
          · iintro HAU
            simp only [Bool.false_eq_true, if_false]
            iret
            dsimp only
            iapply IH $$ HAU
  · ileft
    isplitl [Hst Hcore]
    · iunfold isRwLock
      isplitl [Hst]
      · simp only [LockState.word]
        iexact Hst
      · iexact Hcore
    · iintro HAU
      simp only [LockState.word,
        if_neg (show ¬(((mm : Nat) : Int) + 1 < 0) from by grind)]
      ibind
      simp only [AtomicHeapAPI.cas]
      iapply Conc.wpi_sync
      iapply (wpi_aupd_choose (hsub := by aupd_mask)) $$ HAU
      iintro %sv2 Hlock2
      obtain ⟨s₂, v₂⟩ := sv2
      iunfold isRwLock at Hlock2
      icases Hlock2 with ⟨Hst2, Hcore2⟩
      by_cases hne : s₂ = LockState.read mm
      · subst hne
        simp only [LockState.word]
        iapply (HeapAPI.wpi_cas_succ (Hd := Hd) (m := Mode.part) (E := E) lk.state
          (((mm : Nat) : Int) + 1) ((((mm : Nat) : Int) + 1) + 1))
        iapply (AeneasIris.Step.lat_intro Mode.part _)
        isplitl [Hst2]
        · iexact Hst2
        · iintro Hst2
          imod (rwAcquire_read γ lk.data mm v₂) $$ [Hcore2] with ⟨%sq, Hcore3, Hfrag⟩
          · iexact Hcore2
          imodintro
          iright
          iexists ()
          isplitl [Hst2 Hcore3]
          · iunfold isRwLock
            have hcast : ((mm : Nat) : Int) + 1 + 1 = ((mm + 1 : Nat) : Int) + 1 := by
              push_cast; ring
            rw [hcast]
            dsimp only [LockState.word]
            isplitl [Hst2]
            · iexact Hst2
            · iexact Hcore3
          · iintro HΨ
            have hne1 : ∀ (y : ReadGuard T) (z : ReadGuard T → ITree E Unit),
                (if LockState.read mm = LockState.write then none else some (y, z)) = some (y, z) :=
              fun _ _ => if_neg (by intro h; cases h)
            have hne2 : ∀ P : IProp GF,
                (if LockState.read mm = LockState.write then iprop(emp) else P) = P :=
              fun _ => if_neg (by intro h; cases h)
            simp only [hne1, hne2, AtomicWpi.wandM_some, Option.map]
            iret
            iret
            iret
            iapply HΨ $$ %((⟨lk⟩ : ReadGuard T), read_release (E := E))
            isplitl [Hfrag]
            · iunfold readGuardFrac
              iexists sq
              simp only [RwPos.ofQp_one]
              iunfold rdFrag at Hfrag
              iexact Hfrag
            · have hproj :
                  ((((⟨lk⟩ : ReadGuard T), read_release (E := E)) :
                      ReadGuard T × (ReadGuard T → ITree E Unit)).2
                    (((⟨lk⟩ : ReadGuard T), read_release (E := E)) :
                      ReadGuard T × (ReadGuard T → ITree E Unit)).1)
                  = read_release (E := E) (⟨lk⟩ : ReadGuard T) := rfl
              iintro !> HRG
              rw [hproj]
              have HRR := read_release_spec (Hd := Hd) γ (⟨lk⟩ : ReadGuard T) v₂
              simp only [atomicWpi] at HRR
              iapply HRR
              iexact HRG
      · iapply (HeapAPI.wpi_cas_fail (Hd := Hd) (m := Mode.part) (E := E) lk.state
          s₂.word (((mm : Nat) : Int) + 1) ((((mm : Nat) : Int) + 1) + 1) (DFrac.own 1)
          (by intro h; exact hne (LockState.word_injective h)))
        iapply (AeneasIris.Step.lat_intro Mode.part _)
        isplitl [Hst2]
        · iexact Hst2
        · iintro Hst2
          imodintro
          ileft
          isplitl [Hst2 Hcore2]
          · iunfold isRwLock
            isplitl [Hst2]
            · iexact Hst2
            · iexact Hcore2
          · iintro HAU
            simp only [Bool.false_eq_true, if_false]
            iret
            dsimp only
            iapply IH $$ HAU
  · simp only [LockState.word]
    have hprog : ∀ A B : ITree E (Unit ⊕ Option (ReadGuard T)),
        (if (-1 : Int) < 0 then A else B) = A := fun _ _ => if_pos (by grind)
    have hret : ∀ z : ReadGuard T × (ReadGuard T → ITree E Unit),
        (if LockState.write = LockState.write then none else some z) = none :=
      fun _ => if_pos rfl
    iright
    iexists ()
    isplitl [Hst Hcore]
    · iunfold isRwLock
      isplitl [Hst]
      · simp only [LockState.word]
        iexact Hst
      · iexact Hcore
    · iintro HΨ
      simp only [hprog]
      iret
      iret
      simp only [hret, AtomicWpi.wandM_some, Option.map_none]
      iret
      iapply HΨ $$ %((⟨lk⟩, read_release) : ReadGuard T × (ReadGuard T → ITree E Unit))
      itrivial
theorem read_spec (γ : GName) (lk : Handle T) :
    ⊢ ⟪ ∀ s v, isRwLock γ lk s v ⟫ Hd .part (read (E := E) lk) @ (∅ : CoPset)
        ⟪ (isRwLock γ lk (.read 0) v ∗ ⌜s = .free⌝) ∨
          (∃ k : Nat, isRwLock γ lk (.read (k + 1)) v ∗ ⌜s = .read k⌝)
        | g rel, RET (g, rel)
        ; readGuardFrac γ g 1 v ∗
          □ (readGuardFrac γ g 1 v -∗
               ⟪ ∀ s', isRwLock γ lk s' v ⟫ Hd .part (rel g) @ (∅ : CoPset)
                   ⟪ (isRwLock γ lk .free v ∗ ⌜s' = .read 0⌝) ∨
                     (∃ n : Nat, isRwLock γ lk (.read n) v ∗ ⌜s' = .read (n + 1)⌝)
                   | RET () ⟫) ⟫ := by
  rw [atomicWpi]
  iintro %Φ HAU
  simp only [read, read_acquire]
  ibind
  iloeb as IH
  iunfold ITree.iter
  ibind
  ibind
  simp only [AtomicHeapAPI.load]
  iapply Conc.wpi_sync
  iapply (wpi_aupd_choose (hsub := by aupd_mask)) $$ HAU
  iintro %sv Hlock
  obtain ⟨s₁, v₁⟩ := sv
  iunfold isRwLock at Hlock
  icases Hlock with ⟨Hst, Hcore⟩
  istep
  rcases s₁ with _ | mm | _
  · ileft
    isplitl [Hst Hcore]
    · iunfold isRwLock
      isplitl [Hst]
      · simp only [LockState.word]
        iexact Hst
      · iexact Hcore
    · iintro HAU
      simp only [LockState.word, if_neg (show ¬((0 : Int) < 0) from by grind)]
      ibind
      simp only [AtomicHeapAPI.cas]
      iapply Conc.wpi_sync
      iapply (wpi_aupd_choose (hsub := by aupd_mask)) $$ HAU
      iintro %sv2 Hlock2
      obtain ⟨s₂, v₂⟩ := sv2
      iunfold isRwLock at Hlock2
      icases Hlock2 with ⟨Hst2, Hcore2⟩
      by_cases hne : s₂ = LockState.free
      · subst hne
        simp only [LockState.word]
        iapply (HeapAPI.wpi_cas_succ (Hd := Hd) (m := Mode.part) (E := E) lk.state
          (0 : Int) ((0 : Int) + 1))
        iapply (AeneasIris.Step.lat_intro Mode.part _)
        isplitl [Hst2]
        · iexact Hst2
        · iintro Hst2
          imod (rwAcquire_free γ lk.data v₂) $$ [Hcore2] with ⟨%sq, Hcore3, Hfrag⟩
          · iexact Hcore2
          imodintro
          iright
          iexists ()
          isplitl [Hst2 Hcore3]
          · ileft
            isplitl [Hst2 Hcore3]
            · iunfold isRwLock
              simp only [LockState.word]
              isplitl [Hst2]
              · iexact Hst2
              · iexact Hcore3
            · itrivial
          · iintro HΨ
            simp only [AtomicWpi.wandM_some]
            iret
            iret
            iret
            iapply HΨ $$ %((⟨lk⟩ : ReadGuard T), read_release (E := E))
            isplitl [Hfrag]
            · iunfold readGuardFrac
              iexists sq
              simp only [RwPos.ofQp_one]
              iunfold rdFrag at Hfrag
              iexact Hfrag
            · iintro !> HRG
              dsimp only
              have HRR := read_release_spec (Hd := Hd) γ (⟨lk⟩ : ReadGuard T) v₂
              iapply HRR
              iexact HRG
      · iapply (HeapAPI.wpi_cas_fail (Hd := Hd) (m := Mode.part) (E := E) lk.state
          s₂.word (0 : Int) ((0 : Int) + 1) (DFrac.own 1)
          (by intro h; exact hne (LockState.word_injective h)))
        iapply (AeneasIris.Step.lat_intro Mode.part _)
        isplitl [Hst2]
        · iexact Hst2
        · iintro Hst2
          imodintro
          ileft
          isplitl [Hst2 Hcore2]
          · iunfold isRwLock
            isplitl [Hst2]
            · iexact Hst2
            · iexact Hcore2
          · iintro HAU
            simp only [Bool.false_eq_true, if_false]
            iret
            dsimp only
            iapply IH $$ HAU
  · ileft
    isplitl [Hst Hcore]
    · iunfold isRwLock
      isplitl [Hst]
      · simp only [LockState.word]
        iexact Hst
      · iexact Hcore
    · iintro HAU
      simp only [LockState.word,
        if_neg (show ¬(((mm : Nat) : Int) + 1 < 0) from by grind)]
      ibind
      simp only [AtomicHeapAPI.cas]
      iapply Conc.wpi_sync
      iapply (wpi_aupd_choose (hsub := by aupd_mask)) $$ HAU
      iintro %sv2 Hlock2
      obtain ⟨s₂, v₂⟩ := sv2
      iunfold isRwLock at Hlock2
      icases Hlock2 with ⟨Hst2, Hcore2⟩
      by_cases hne : s₂ = LockState.read mm
      · subst hne
        simp only [LockState.word]
        iapply (HeapAPI.wpi_cas_succ (Hd := Hd) (m := Mode.part) (E := E) lk.state
          (((mm : Nat) : Int) + 1) ((((mm : Nat) : Int) + 1) + 1))
        iapply (AeneasIris.Step.lat_intro Mode.part _)
        isplitl [Hst2]
        · iexact Hst2
        · iintro Hst2
          imod (rwAcquire_read γ lk.data mm v₂) $$ [Hcore2] with ⟨%sq, Hcore3, Hfrag⟩
          · iexact Hcore2
          imodintro
          iright
          iexists ()
          isplitl [Hst2 Hcore3]
          · iright
            iexists mm
            isplitl [Hst2 Hcore3]
            · iunfold isRwLock
              have hcast : ((mm : Nat) : Int) + 1 + 1 = ((mm + 1 : Nat) : Int) + 1 := by
                push_cast; ring
              rw [hcast]
              dsimp only [LockState.word]
              isplitl [Hst2]
              · iexact Hst2
              · iexact Hcore3
            · itrivial
          · iintro HΨ
            simp only [AtomicWpi.wandM_some]
            iret
            iret
            iret
            iapply HΨ $$ %((⟨lk⟩ : ReadGuard T), read_release (E := E))
            isplitl [Hfrag]
            · iunfold readGuardFrac
              iexists sq
              simp only [RwPos.ofQp_one]
              iunfold rdFrag at Hfrag
              iexact Hfrag
            · iintro !> HRG
              dsimp only
              have HRR := read_release_spec (Hd := Hd) γ (⟨lk⟩ : ReadGuard T) v₂
              iapply HRR
              iexact HRG
      · iapply (HeapAPI.wpi_cas_fail (Hd := Hd) (m := Mode.part) (E := E) lk.state
          s₂.word (((mm : Nat) : Int) + 1) ((((mm : Nat) : Int) + 1) + 1) (DFrac.own 1)
          (by intro h; exact hne (LockState.word_injective h)))
        iapply (AeneasIris.Step.lat_intro Mode.part _)
        isplitl [Hst2]
        · iexact Hst2
        · iintro Hst2
          imodintro
          ileft
          isplitl [Hst2 Hcore2]
          · iunfold isRwLock
            isplitl [Hst2]
            · iexact Hst2
            · iexact Hcore2
          · iintro HAU
            simp only [Bool.false_eq_true, if_false]
            iret
            dsimp only
            iapply IH $$ HAU
  · simp only [LockState.word]
    ileft
    isplitl [Hst Hcore]
    · iunfold isRwLock
      simp only [LockState.word]
      isplitl [Hst]
      · iexact Hst
      · iexact Hcore
    · iintro HAU
      simp only [if_pos (show ((-1 : Int) < 0) from by grind)]
      iret
      dsimp only
      iapply IH $$ HAU
theorem write_deref_spec (γ : GName) (g : WriteGuard T) (v : T) (M : CoPset) :
    ⦃ writeGuard γ g v ⦄ (write_deref (E := E) g) @ Hd ; m ; M
    ⦃ r, ⌜r = v⌝ ∗ writeGuard γ g v ⦄ :=
  RwLockImpl.write_deref_spec γ g v M

theorem read_deref_spec (γ : GName) (g : ReadGuard T) (q : Qp) (v : T) (M : CoPset) :
    ⦃ readGuardFrac γ g q v ⦄ (read_deref (E := E) g) @ Hd ; m ; M
    ⦃ r, ⌜r = v⌝ ∗ readGuardFrac γ g q v ⦄ :=
  RwLockImpl.read_deref_spec γ g q v M

theorem write_deref_mut_spec (γ : GName) (g : WriteGuard T) (v : T) (M : CoPset) :
    ⦃ writeGuard γ g v ⦄ (write_deref_mut (E := E) g) @ Hd ; m ; M
    ⦃ r, ∃ st bk, ⌜r = (v, st, bk)⌝ ∗
        writeGuard γ g v ∗
        □ (∀ v₀ : T, ∀ v' : T, writeGuard γ g v₀ -∗
             wpi_mask GF Hd m (st v')
               (fun g' => iprop(⌜g' = g⌝ ∗ writeGuard γ g v')) ⊤) ⦄ :=
  RwLockImpl.write_deref_mut_spec γ g v M

theorem drop_spec (γ : GName) (lk : Handle T) (v : T) (M : CoPset) :
    ⦃ isRwLock γ lk .free v ⦄ (drop (E := E) lk) @ Hd ; m ; M
    ⦃ r, ⌜r = ()⌝ ⦄ :=
  RwLockImpl.drop_spec γ lk v M

/-- The interface is met over the atomic heap as well, at partial mode.

A `def` and not an `instance`: `RwLockImpl` already supplies one at the same
`GF` and `Hd`, and search would have no way to choose.  Partial because
`try_read` retries, which is what reading the state and swapping it separately
costs once something may happen in between. -/
@[reducible] noncomputable def atomicRwLockAPI : RwLockAPI GF Hd Mode.part where
  RwLock := Handle
  ReadGuard := ReadGuard
  WriteGuard := WriteGuard

  new := new
  drop := drop
  try_read := try_read
  try_write := try_write
  read := read
  write := write
  read_deref := read_deref
  write_deref := write_deref
  write_deref_mut := write_deref_mut

  isRwLock := isRwLock
  writeGuard := writeGuard
  readGuardFrac := readGuardFrac

  isRwLock_timeless := by infer_instance
  writeGuard_timeless := by infer_instance
  readGuardFrac_timeless := by infer_instance

  isRwLock_exclusive := isRwLock_exclusive
  readGuardFrac_split := readGuardFrac_split
  readGuardFrac_state := readGuardFrac_state
  readGuardFrac_agree := readGuardFrac_agree
  writeGuard_state := writeGuard_state

  new_spec := new_spec
  drop_spec := drop_spec
  try_write_spec := try_write_spec
  write_spec := write_spec
  try_read_spec := try_read_spec
  read_spec := read_spec
  write_deref_spec := write_deref_spec
  read_deref_spec := read_deref_spec
  write_deref_mut_spec := write_deref_mut_spec

end Specs

end AeneasIris.AtomicRwLockImpl
