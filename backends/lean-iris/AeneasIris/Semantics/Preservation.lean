import AeneasIris.Semantics.Invariant

/-!
# Preservation: the machine steps, the invariant survives

The four lemmas the soundness proof needs. They are the only place where the
handlers of `rustH` are actually opened, and between them they are the whole
mathematical content of adequacy; `Semantics/Soundness.lean` is plumbing on top.

## Proof sketches

**`sysInv_not_faulty`.** Unfold `wpi` once at the scheduled thread
(`wpi_unfold_emp`). If the focus is `vis (fail e) k` the handler contributes
`failH.run e _ _ = False`, so the goal follows by `iexfalso`. If it is
`vis (modify f) k` the handler contributes
`∀ s, heapInterp s ={∅}=∗ ∃ s', ⌜f s = some s'⌝ ∗ …`; instantiate at `s := c.heap`
using the `heapInterp c.heap` of `SysInv`, and the `⌜f c.heap = some s'⌝` it
returns contradicts `f c.heap = none`. Every other focus is not `Faulty`.

**`sysInv_step`.** Case on the `Step` derivation; in each case unfold `wpi` once
and read off the matching clause of `rustH`:

* `tick` — `stepH.run .step Ψ _ = lat m (Ψ ())`. At `.part` that *is* the `▷` of
  the goal; at `.total` introduce one with `later_intro`.
* `heap` — `stateH.run`, instantiated at `c.heap`; it returns the new
  `heapInterp s'` (with `⌜f c.heap = some s'⌝` pinning `s' = σ'`) and `Ψ c.heap`,
  which is the new `runObl`. Note the continuation is applied to the **old** heap.
* `yield` — `ConcH.run .yield = |={∅,⊤}=> |={⊤,∅}=> Ψ ()`. Consume the first
  half: that is where `ownE ⊤` comes back into the ambient. The scheduled
  thread's remainder `|={⊤,∅}=> Ψ ()` becomes `readyObl` of the old thread; the
  newly scheduled thread `j`'s `readyObl` — an `|={⊤,∅}=> …` — then consumes the
  token again and becomes its `runObl`.
* `fork` — `ConcH.run .fork = Ψ .cur ∗ Ψs .new` where `wpiAcc` fixes
  `Ψs a = |={⊤,∅}=> wpi (k a) (fun _ => False)`. The left conjunct is the
  parent's new `runObl`; the right is exactly `readyObl` of the appended child
  at postcondition `threadPost Φ i = fun _ => False` (its index is nonzero, since
  the pool is nonempty). `BigSepL.bigSepL_snoc` splits the big operator.
* `endthread` — `ConcH.run .endthread = |={∅,⊤}=> True`. Consuming it returns
  `ownE ⊤` to the ambient, which the newly scheduled thread's `readyObl`
  consumes; the dying thread contributes `emp` afterwards.

**`sysInv_init`.** `init t` has a one-element pool, so the big operator is `emp`
(`BigSepL.bigSepL_singleton` on the tombstoned pool) and `focusObl` is the head.
`readyObl_alive` turns the hypothesis's `wpi_mask … ⊤` into `|={⊤,∅}=> runObl`,
which is the goal's mask-changing update.

**`sysInv_return`.** `threadPost Φ 0 = Φ` by `if_pos`, and
`runObl m Φ 0 (ret v) = wpi (ret v) (fun v => |={∅,⊤}=> Φ v)`, which
`wpi_ret_emp'` collapses to `|={∅}=> |={∅,⊤}=> Φ v`. This is the one place the
big lock is handed back to the caller, which is why `MayReturn` insists the main
thread be scheduled.
-/

namespace AeneasIris.Semantics

open Iris BI Aeneas.Data.Coinductive
open AeneasIris.Heap (HeapGS heapInterp)
open Aeneas.Std (Result RustEffect RustHeap)

unseal Aeneas.Std.Result

section

/-! ## Pure facts about configurations

These are ordinary Lean lemmas about `Config`; none of them mention Iris. -/

section Pure

variable {α : Type}

/-- Reading `Config.focus` backwards. -/
private theorem focus_getElem? {c : Config α} {t : Result α} (h : c.focus = some t) :
    c.threads[c.current]? = some (Thread.alive t) := by
  unfold Config.focus at h
  split at h
  · rename_i heq; simp only [Option.some.injEq] at h; subst h; exact heq
  · exact absurd h (by simp)

private theorem focus_lt {c : Config α} {t : Result α} (h : c.focus = some t) :
    c.current < c.threads.length :=
  (List.getElem?_eq_some_iff.mp (focus_getElem? h)).1

/-- `Config.focus` from a `getElem?` fact. -/
private theorem focus_of_getElem? {c : Config α} {t : Result α}
    (h : c.threads[c.current]? = some (Thread.alive t)) : c.focus = some t := by
  unfold Config.focus; rw [h]

private theorem setFocus_focus {c : Config α} {t₀ : Result α} (h : c.focus = some t₀)
    (t : Result α) : (c.setFocus t).focus = some t := by
  refine focus_of_getElem? ?_
  simp only [Config.setFocus]
  simp [focus_lt h]

/-- Indexing the parent slot of a forked pool. -/
private theorem getElem?_set_append {L M : List (Thread α)} {i : Nat} (a : Thread α)
    (hi : i < L.length) : ((L.set i a) ++ M)[i]? = some a := by
  rw [List.getElem?_append_left (by simpa using hi)]
  simp [hi]

/-- Tombstoning the parent slot of a forked pool. -/
private theorem set_append_dead {L M : List (Thread α)} {i : Nat} (a : Thread α)
    (hi : i < L.length) :
    ((L.set i a) ++ M).set i Thread.dead = L.set i Thread.dead ++ M := by
  rw [List.set_append_left i Thread.dead (by simpa using hi), List.set_set]

private theorem kill_threads (c : Config α) :
    c.kill.threads = c.threads.set c.current Thread.dead := rfl

end Pure

variable {hlc : Iris.HasLC} {GF : BundledGFunctors} [Iris.InvGS_gen hlc GF]
variable [HeapGS.{0} GF] {α : Type}

/-! ## Opening `rustH`

One equation per summand of `rustH = failH ⊕ₕ ConcH ⊕ₕ stepH m ⊕ₕ stateH`. All
of them hold by `rfl`: the sum handler dispatches on a literal `Sum` injection,
and the four `*Ev` abbreviations are `@[match_pattern]`, so the projection
reduces. -/

private theorem rustH_fail (m : Mode) (e : Aeneas.Std.Error)
    (Ψ B : RustEffect.O (Aeneas.Std.RustEffect.fail e) → IProp GF) :
    (Rust.rustH (GF := GF) m).run (Aeneas.Std.RustEffect.fail e) Ψ B = iprop(False) := rfl

private theorem rustH_step (m : Mode) (Ψ B : RustEffect.O stepEv → IProp GF) :
    (Rust.rustH (GF := GF) m).run stepEv Ψ B = Step.lat m (Ψ PUnit.unit) := rfl

private theorem rustH_modify (m : Mode) (f : RustHeap.{0} → Option RustHeap.{0})
    (Ψ B : RustEffect.O (modifyEv f) → IProp GF) :
    (Rust.rustH (GF := GF) m).run (modifyEv f) Ψ B =
      iprop(∀ s, heapInterp s ={∅}=∗ ∃ s', ⌜f s = some s'⌝ ∗ heapInterp s' ∗ Ψ s) := rfl

private theorem rustH_fork (m : Mode) (Ψ B : RustEffect.O forkEv → IProp GF) :
    (Rust.rustH (GF := GF) m).run forkEv Ψ B =
      iprop(Ψ Aeneas.Std.ConcE.Tags.cur ∗ B Aeneas.Std.ConcE.Tags.new) := rfl

private theorem rustH_yield (m : Mode) (Ψ B : RustEffect.O yieldEv → IProp GF) :
    (Rust.rustH (GF := GF) m).run yieldEv Ψ B =
      iprop(|={∅, ⊤}=> |={⊤, ∅}=> Ψ PUnit.unit) := rfl

private theorem rustH_endthread (m : Mode) (Ψ B : RustEffect.O endthreadEv → IProp GF) :
    (Rust.rustH (GF := GF) m).run endthreadEv Ψ B = iprop(|={∅, ⊤}=> True) := rfl

/-- Unfolding the scheduled thread's obligation at a `vis` node. -/
private theorem runObl_vis (m : Mode) (Φ : α → IProp GF) (i : Nat)
    (e : RustEffect.I) (k : RustEffect.O e → Result α) :
    runObl m Φ i (Result.vis e k) ⊢
      iprop(|={∅}=> (Rust.rustH m).run e
        (fun a => runObl m Φ i (k a))
        (fun a => iprop(|={⊤, ∅}=>
          wpi GF (Rust.rustH m) m (k a) (fun _ => iprop(False))))) := by
  simp only [runObl, Result.vis]
  exact (wpi_vis_emp' (H := Rust.rustH m) e k _).mpr

/-- **The invariant rules out both faults.** No reachable configuration is about
to panic or to perform an undefined heap operation. -/
theorem sysInv_not_faulty (m : Mode) (Φ : α → IProp GF) (c : Config α) :
    SysInv m Φ c ⊢ iprop(|={∅}=> ⌜¬ c.Faulty⌝) := by
  by_cases hf : c.Faulty
  case neg => exact (BI.pure_intro hf).trans Iris.fupd_intro
  obtain ⟨t, hfoc, hbad⟩ := hf
  refine .trans ?_ (BIFUpdate.mono BI.false_elim)
  rcases hbad with ⟨e, k, rfl⟩ | ⟨f, k, rfl, hnone⟩
  · /- A panic: `failH` contributes `False`. -/
    simp only [SysInv, focusObl, hfoc]
    iintro ⟨Hheap, Hwp, Hrest⟩
    ihave Hwp := BI.entails_wand
      (runObl_vis m Φ c.current (Aeneas.Std.RustEffect.fail e) k) $$ Hwp
    imod Hwp with Hwp
    simp only [rustH_fail]
    iexact Hwp
  · /- An undefined heap operation: `stateH` returns `⌜f c.heap = some s'⌝`. -/
    simp only [SysInv, focusObl, hfoc]
    iintro ⟨Hheap, Hwp, Hrest⟩
    ihave Hwp := BI.entails_wand (runObl_vis m Φ c.current (modifyEv f) k) $$ Hwp
    imod Hwp with Hwp
    simp only [rustH_modify]
    imod Hwp $$ %c.heap Hheap with ⟨%s', %hfs, Hheap', Hcont⟩
    rw [hnone] at hfs
    simp at hfs

/-! ## Moving obligations in and out of the big operator -/

/-- **Park.** Put a ready obligation back into the slot the big operator has
tombstoned. Used when a thread gives up the big lock. -/
private theorem bigOp_park (m : Mode) (Φ : α → IProp GF) (L : List (Thread α))
    (i : Nat) (t : Result α) (hi : i < L.length) :
    ⊢ iprop(([∗list] n ↦ th ∈ L.set i Thread.dead, readyObl m Φ n th) -∗
            (|={⊤, ∅}=> runObl m Φ i t) -∗
            [∗list] n ↦ th ∈ L.set i (Thread.alive t), readyObl m Φ n th) := by
  have hget : (L.set i Thread.dead)[i]? = some Thread.dead := by simp [hi]
  have hset : (L.set i Thread.dead).set i (Thread.alive t) = L.set i (Thread.alive t) := by
    simp only [List.set_set]
  rw [← hset]
  iintro Hbig Hr
  ihave ⟨_, Hacc⟩ := BI.entails_wand
    (BigSepL.bigSepL_lookup_acc (Φ := readyObl m Φ) hget).mp $$ Hbig
  iapply Hacc $$ %(Thread.alive t)
  simp only [readyObl_alive]
  iexact Hr

/-- **Unpark.** Take the ready obligation of a live thread out of the big
operator, leaving its slot tombstoned. Used when a thread takes the big lock. -/
private theorem bigOp_unpark (m : Mode) (Φ : α → IProp GF) (L : List (Thread α))
    (j : Nat) (t : Result α) (hj : L[j]? = some (Thread.alive t)) :
    iprop([∗list] n ↦ th ∈ L, readyObl m Φ n th)
      ⊢ iprop((|={⊤, ∅}=> runObl m Φ j t) ∗
              [∗list] n ↦ th ∈ L.set j Thread.dead, readyObl m Φ n th) := by
  refine .trans (BigSepL.bigSepL_lookup_acc (Φ := readyObl m Φ) hj).mp ?_
  iintro ⟨Hr, Hacc⟩
  isplitl [Hr]
  · simp only [readyObl_alive]
    iexact Hr
  · iapply Hacc $$ %Thread.dead
    simp only [readyObl]
    iempintro

/-- The obligation a freshly forked child inherits. Its index is nonzero, so its
postcondition is `False` and the `|={∅,⊤}=>` the `readyObl` carries is vacuous. -/
private theorem forkChild (m : Mode) (Φ : α → IProp GF) (i : Nat) (hi : i ≠ 0)
    (t : Result α) :
    iprop(|={⊤, ∅}=> wpi GF (Rust.rustH m) m t (fun _ => iprop(False)))
      ⊢ readyObl m Φ i (Thread.alive t) := by
  simp only [readyObl, wpi_mask, threadPost, if_neg hi]
  exact BIFUpdate.mono (wpi_mono_emp _ (fun _ => BI.false_elim))

/-! ## `SysInv`, opened at a live focus

Stated as two entailments rather than as an equation so that the projections of
`c` are left to unification: in `sysInv_step` the successor configuration is a
record literal, and asking `simp` to normalise inside it is fragile. -/

private theorem sysInv_elim (m : Mode) (Φ : α → IProp GF) (c : Config α)
    {t : Result α} (h : c.focus = some t) :
    SysInv m Φ c ⊢ iprop(heapInterp c.heap ∗ runObl m Φ c.current t ∗
      [∗list] i ↦ th ∈ c.threads.set c.current Thread.dead, readyObl m Φ i th) := by
  simp only [SysInv, focusObl, h, kill_threads]
  exact .rfl

private theorem sysInv_intro (m : Mode) (Φ : α → IProp GF) (c : Config α)
    {t : Result α} (h : c.focus = some t) :
    iprop(heapInterp c.heap ∗ runObl m Φ c.current t ∗
      [∗list] i ↦ th ∈ c.threads.set c.current Thread.dead, readyObl m Φ i th)
      ⊢ SysInv m Φ c := by
  simp only [SysInv, focusObl, h, kill_threads]
  exact .rfl

/-! ## Modalities -/

omit [HeapGS.{0} GF] in
/-- Whatever `lat` is, it is at most a `▷`. -/
private theorem lat_later (m : Mode) (P : IProp GF) : Step.lat m P ⊢ iprop(▷ P) := by
  cases m
  · exact BI.later_intro
  · exact .rfl

omit [HeapGS.{0} GF] in
/-- A step that needs no `▷` still proves the `|={∅}▷=>` goal. -/
private theorem stepFupd_of_fupd {P Q : IProp GF} (h : P ⊢ iprop(|={∅}=> Q)) :
    P ⊢ iprop(|={∅}▷=> Q) :=
  h.trans (BIFUpdate.mono (Iris.fupd_intro.trans BI.later_intro))

/-! ## Preservation, one machine rule at a time

Each rule gets its own lemma, stated at the **`▷`-free** strength it actually
has. Only `tick` needs a modality, and only because `stepH` chooses to issue one
at `.part`; the other four are `|={∅}=>` for every `m`. Keeping them apart is
what lets `sysInv_step_total` exist: at `.total` there is no `▷` anywhere, and
that is the only well-foundedness the termination proof has. -/

/-- `Step.tick`. The one rule whose strength depends on `m`: `stepH` answers
with `lat m`, which is a `▷` at `.part` and nothing at all at `.total`. -/
private theorem step_tick_total (Φ : α → IProp GF) {c : Config α}
    {k : RustEffect.O stepEv → Result α}
    (hfoc : c.focus = some (Result.vis stepEv k)) :
    SysInv Mode.total Φ c
      ⊢ iprop(|={∅}=> SysInv Mode.total Φ (c.setFocus (k PUnit.unit))) := by
  refine .trans (sysInv_elim _ Φ c hfoc) ?_
  refine .trans ?_ (BIFUpdate.mono
    (sysInv_intro _ Φ _ (setFocus_focus hfoc (k PUnit.unit))))
  dsimp only [Config.setFocus]
  simp only [List.set_set]
  iintro ⟨Hheap, Hwp, Hrest⟩
  ihave Hwp := BI.entails_wand (runObl_vis .total Φ c.current stepEv k) $$ Hwp
  imod Hwp with Hwp
  simp only [rustH_step, Step.lat_identity]
  imodintro
  iframe Hheap
  iframe Hwp
  iexact Hrest

/-- `Step.tick` at an arbitrary mode: the `lat m` becomes the goal's `▷`. -/
private theorem step_tick (m : Mode) (Φ : α → IProp GF) {c : Config α}
    {k : RustEffect.O stepEv → Result α}
    (hfoc : c.focus = some (Result.vis stepEv k)) :
    SysInv m Φ c ⊢ iprop(|={∅}▷=> SysInv m Φ (c.setFocus (k PUnit.unit))) := by
  refine .trans (sysInv_elim m Φ c hfoc) ?_
  refine .trans ?_ (BIFUpdate.mono (BI.later_mono (BIFUpdate.mono
    (sysInv_intro m Φ _ (setFocus_focus hfoc (k PUnit.unit))))))
  dsimp only [Config.setFocus]
  simp only [List.set_set]
  iintro ⟨Hheap, Hwp, Hrest⟩
  ihave Hwp := BI.entails_wand (runObl_vis m Φ c.current stepEv k) $$ Hwp
  imod Hwp with Hwp
  simp only [rustH_step]
  ihave Hwp := BI.entails_wand (lat_later m _) $$ Hwp
  imodintro
  inext
  imodintro
  iframe Hheap
  iframe Hwp
  iexact Hrest

/-- `Step.heap`. `stateH` hands back the new heap interpretation together with
`⌜f c.heap = some s'⌝`, which pins `s' = σ'`. The continuation receives the
**old** heap. No modality. -/
private theorem step_heap (m : Mode) (Φ : α → IProp GF) {c : Config α}
    {f : RustHeap.{0} → Option RustHeap.{0}}
    {k : RustEffect.O (modifyEv f) → Result α} {σ' : RustHeap.{0}}
    (hfoc : c.focus = some (Result.vis (modifyEv f) k)) (hf : f c.heap = some σ') :
    SysInv m Φ c
      ⊢ iprop(|={∅}=> SysInv m Φ { c.setFocus (k c.heap) with heap := σ' }) := by
  refine .trans (sysInv_elim m Φ c hfoc) ?_
  refine .trans ?_ (BIFUpdate.mono
    (sysInv_intro m Φ _ (setFocus_focus hfoc (k c.heap))))
  dsimp only [Config.setFocus]
  simp only [List.set_set]
  iintro ⟨Hheap, Hwp, Hrest⟩
  ihave Hwp := BI.entails_wand (runObl_vis m Φ c.current (modifyEv f) k) $$ Hwp
  imod Hwp with Hwp
  simp only [rustH_modify]
  imod Hwp $$ %(c.heap) Hheap with ⟨%s', %hfs, Hheap, Hcont⟩
  have hs' : s' = σ' := by rw [hf] at hfs; exact (Option.some.inj hfs).symm
  subst hs'
  imodintro
  iframe Hheap
  iframe Hcont
  iexact Hrest

/-- `Step.yield`. `ConcH` answers `|={∅,⊤}=> |={⊤,∅}=> Ψ ()`. The first half
releases `ownE ⊤` into the ambient; what is left, `|={⊤,∅}=> runObl …`, is
literally the `readyObl` of the thread that is stepping down, and goes back into
the big operator. The newly scheduled thread's `readyObl` then consumes the
token again and becomes the new `runObl`. No modality. -/
private theorem step_yield (m : Mode) (Φ : α → IProp GF) {c : Config α}
    {k : RustEffect.O yieldEv → Result α} {j : Nat}
    (hfoc : c.focus = some (Result.vis yieldEv k))
    (halive : (c.setFocus (k PUnit.unit)).Alive j) :
    SysInv m Φ c
      ⊢ iprop(|={∅}=> SysInv m Φ { c.setFocus (k PUnit.unit) with current := j }) := by
  obtain ⟨tj, hj⟩ := halive
  refine .trans (sysInv_elim m Φ c hfoc) ?_
  refine .trans ?_ (BIFUpdate.mono (sysInv_intro m Φ _ (focus_of_getElem? hj)))
  dsimp only [Config.setFocus]
  iintro ⟨Hheap, Hwp, Hrest⟩
  ihave Hwp := BI.entails_wand (runObl_vis m Φ c.current yieldEv k) $$ Hwp
  imod Hwp with Hwp
  simp only [rustH_yield]
  imod Hwp with Hwp
  ihave Hrest :=
    bigOp_park m Φ c.threads c.current (k PUnit.unit) (focus_lt hfoc) $$ Hrest Hwp
  ihave ⟨Hj, Hrest⟩ := BI.entails_wand (bigOp_unpark m Φ
    (c.threads.set c.current (Thread.alive (k PUnit.unit))) j tj hj) $$ Hrest
  imod Hj with Hj
  imodintro
  iframe Hheap
  iframe Hj
  iexact Hrest

/-- `Step.fork`. `ConcH` answers `Ψ .cur ∗ Ψs .new`. The parent keeps the big
lock; the child is appended to the pool as a `readyObl` at a nonzero index, so
its postcondition is `False`. No modality. -/
private theorem step_fork (m : Mode) (Φ : α → IProp GF) {c : Config α}
    {k : RustEffect.O forkEv → Result α}
    (hfoc : c.focus = some (Result.vis forkEv k)) :
    SysInv m Φ c
      ⊢ iprop(|={∅}=> SysInv m Φ
          { threads := c.threads.set c.current (Thread.alive (k Aeneas.Std.ConcE.Tags.cur))
                         ++ [Thread.alive (k Aeneas.Std.ConcE.Tags.new)],
            current := c.current, heap := c.heap }) := by
  have hlt : c.current < c.threads.length := focus_lt hfoc
  have hfocF : (⟨c.threads.set c.current (Thread.alive (k Aeneas.Std.ConcE.Tags.cur))
                  ++ [Thread.alive (k Aeneas.Std.ConcE.Tags.new)],
                c.current, c.heap⟩ : Config α).focus
      = some (k Aeneas.Std.ConcE.Tags.cur) :=
    focus_of_getElem? (getElem?_set_append _ hlt)
  have hsetF :
      (c.threads.set c.current (Thread.alive (k Aeneas.Std.ConcE.Tags.cur))
          ++ [Thread.alive (k Aeneas.Std.ConcE.Tags.new)]).set c.current Thread.dead
        = c.threads.set c.current Thread.dead
            ++ [Thread.alive (k Aeneas.Std.ConcE.Tags.new)] :=
    set_append_dead _ hlt
  have hlen0 : (c.threads.set c.current Thread.dead).length ≠ 0 := by
    simp only [List.length_set]; grind
  refine .trans (sysInv_elim m Φ c hfoc) ?_
  refine .trans ?_ (BIFUpdate.mono (sysInv_intro m Φ _ hfocF))
  dsimp only
  rw [hsetF]
  iintro ⟨Hheap, Hwp, Hrest⟩
  ihave Hwp := BI.entails_wand (runObl_vis m Φ c.current forkEv k) $$ Hwp
  simp only [rustH_fork]
  imod Hwp with ⟨Hcur, Hnew⟩
  imodintro
  iframe Hheap
  iframe Hcur
  ihave Hnew := BI.entails_wand (forkChild m Φ _ hlen0 (k Aeneas.Std.ConcE.Tags.new))
    $$ Hnew
  iapply BI.entails_wand (BigSepL.bigSepL_snoc (Φ := readyObl m Φ)).mpr
  iframe Hrest
  iexact Hnew

/-- `Step.endthread`. `ConcH` answers `|={∅,⊤}=> True`: the token is released
and never taken back. The newly scheduled thread's `readyObl` consumes it. No
modality. -/
private theorem step_endthread (m : Mode) (Φ : α → IProp GF) {c : Config α}
    {k : RustEffect.O endthreadEv → Result α} {j : Nat}
    (hfoc : c.focus = some (Result.vis endthreadEv k))
    (halive : c.kill.Alive j) :
    SysInv m Φ c ⊢ iprop(|={∅}=> SysInv m Φ { c.kill with current := j }) := by
  obtain ⟨tj, hj⟩ := halive
  refine .trans (sysInv_elim m Φ c hfoc) ?_
  refine .trans ?_ (BIFUpdate.mono (sysInv_intro m Φ _ (focus_of_getElem? hj)))
  dsimp only [Config.kill]
  iintro ⟨Hheap, Hwp, Hrest⟩
  ihave Hwp := BI.entails_wand (runObl_vis m Φ c.current endthreadEv k) $$ Hwp
  imod Hwp with Hwp
  simp only [rustH_endthread]
  imod Hwp with _
  ihave ⟨Hj, Hrest⟩ := BI.entails_wand (bigOp_unpark m Φ
    (c.threads.set c.current Thread.dead) j tj hj) $$ Hrest
  imod Hj with Hj
  imodintro
  iframe Hheap
  iframe Hj
  iexact Hrest

/-- **The invariant is preserved by every machine step**, at the cost of one
`▷`. The `▷` is genuinely needed only for `Step.tick` at `.part`; everywhere
else it is introduced by `BI.later_intro`.

⚠️ At `.total` this statement is *strictly weaker* than the truth — see
`sysInv_step_total`, which is the one the termination proof must use. -/
theorem sysInv_step (m : Mode) (Φ : α → IProp GF) {c c' : Config α} (h : Step c c') :
    SysInv m Φ c ⊢ iprop(|={∅}▷=> SysInv m Φ c') := by
  cases h
  case tick k hfoc => exact step_tick m Φ hfoc
  case heap f k σ' hfoc hf => exact stepFupd_of_fupd (step_heap m Φ hfoc hf)
  case yield k j hfoc halive => exact stepFupd_of_fupd (step_yield m Φ hfoc halive)
  case fork k hfoc => exact stepFupd_of_fupd (step_fork m Φ hfoc)
  case endthread k j hfoc halive =>
    exact stepFupd_of_fupd (step_endthread m Φ hfoc halive)

/-- **Preservation at `.total` costs no `▷` at all.**

`stepH.run .step Ψ _ = lat .total (Ψ ()) = Ψ ()`, and the other four rules never
issue a modality for any mode, so the whole step relation is `▷`-free here.

This is not a cosmetic strengthening. `sysInv_step` at `.total` would let the
adequacy proof only reach `|={∅}▷=>^[n]`, and `step_fupdN_soundness` on that
says no more than "every `n`-step prefix is safe" — which is equally true of a
machine that runs forever. Well-foundedness of the least fixpoint `wpi` is the
*only* source of termination, and it survives only if no `▷` is inserted between
the machine step and the obligation of the successor configuration. Hence
`Terminates` must be derived from this lemma, never from `sysInv_step`. -/
theorem sysInv_step_total (Φ : α → IProp GF) {c c' : Config α} (h : Step c c') :
    SysInv Mode.total Φ c ⊢ iprop(|={∅}=> SysInv Mode.total Φ c') := by
  cases h
  case tick k hfoc => exact step_tick_total Φ hfoc
  case heap f k σ' hfoc hf => exact step_heap _ Φ hfoc hf
  case yield k j hfoc halive => exact step_yield _ Φ hfoc halive
  case fork k hfoc => exact step_fork _ Φ hfoc
  case endthread k j hfoc halive => exact step_endthread _ Φ hfoc halive

/-- **The invariant holds initially.** Consuming the `|={⊤,∅}=>` is what hands
the big lock to the main thread. -/
theorem sysInv_init (m : Mode) (Φ : α → IProp GF) (t : Result α) :
    iprop(heapInterp (∅ : RustHeap.{0}) ∗ wpi_mask GF (Rust.rustH m) m t Φ ⊤)
      ⊢ iprop(|={⊤,∅}=> SysInv m Φ (init t)) := by
  have hfoc : (init t).focus = some t := rfl
  have hkill : (init t).kill.threads = [Thread.dead] := rfl
  have hheap : (init t).heap = (∅ : RustHeap.{0}) := rfl
  have hcur : (init t).current = 0 := rfl
  simp only [SysInv, focusObl, hfoc, hkill, hheap, hcur, runObl, threadPost, reduceIte, wpi_mask]
  iintro ⟨Hheap, Hwp⟩
  imod Hwp with Hwp
  imodintro
  iframe Hheap
  iframe Hwp
  exact (BigSepL.bigSepL_singleton (PROP := IProp GF) (Φ := readyObl m Φ) (x := Thread.dead)).mpr


/-- **The postcondition can be read off when the main thread is scheduled and
has returned.** The result is stated at `|={∅,⊤}=>` because collecting it hands
the big lock back; for a `Plain` postcondition the caller closes the mask again
with `fupd_plain_mask`. -/
theorem sysInv_return (m : Mode) (Φ : α → IProp GF) {c : Config α} {v : α}
    (hcur : c.current = 0) (hfoc : c.focus = some (Result.ok v)) :
    SysInv m Φ c ⊢ iprop(|={∅, ⊤}=> Φ v) := by
  simp only [SysInv, focusObl, hfoc, hcur, runObl, threadPost, reduceIte, Result.ok]
  iintro ⟨Hheap, Hwp, Hrest⟩
  ihave Hwp := BI.entails_wand
    (wpi_ret_emp' (GF := GF) (H := Rust.rustH m) (m := m) v
      (fun v => iprop(|={∅, ⊤}=> Φ v))).mpr $$ Hwp
  imod Hwp with Hwp
  iexact Hwp

end

end AeneasIris.Semantics

