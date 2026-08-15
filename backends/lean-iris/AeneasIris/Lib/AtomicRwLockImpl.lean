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

noncomputable def try_read_acquire (lk : Handle T) : ITree E (Option (ReadGuard T)) := do
  let n : Int ← load lk.state
  if n < 0 then
    return none
  else
    let ok ← cas lk.state n (n + 1)
    if ok then return some ⟨lk⟩ else return none

noncomputable def try_write_acquire (lk : Handle T) : ITree E (Option (WriteGuard T)) := do
  let ok ← cas lk.state (0 : Int) (-1)
  if ok then return some ⟨lk⟩ else return none

/-- No `Conc.sync`: the retry already yields, because the load it retries on is
an atomic access. -/
noncomputable def read_acquire (lk : Handle T) : ITree E (ReadGuard T) :=
  AeneasIris.Conc.waitUntil (try_read_acquire (E := E) lk)

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
theorem try_read_spec (γ : GName) (lk : Handle T) :
    ⊢ ⟪ ∀ s v, isRwLock γ lk s v ⟫ Hd m (try_read (E := E) lk) @ (∅ : CoPset)
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
  sorry
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
  sorry
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

end Specs

end AeneasIris.AtomicRwLockImpl
