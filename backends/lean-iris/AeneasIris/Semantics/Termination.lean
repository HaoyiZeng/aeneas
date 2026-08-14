import AeneasIris.Semantics.Invariant

/-!
# Termination: the `.total` half of adequacy

`adequacy_total` has three conjuncts. The first two — safety and the
postcondition — are free: `ProvableSpec.total_to_part` transports the hypothesis
down to `.part`, and `adequacy_part` applies. Only `Terminates` is new work, and
it splits in two:

* **no silent divergence** (`¬ Config.Diverging`) — immediate, because
  `divOK .total = False`: a thread sitting on `div` has an unsatisfiable
  obligation. Proved below.
* **no infinite execution** (`SN`) — a transcription of Iris's `twp_total`,
  decomposed into named lemmas. The chain is

    `wpi_TPf_step` → `wpi_TPf`   (over `Frag`)
      →  `TPf_app` → `TPf_singleton` → `TPf_parked` → `pool_TPf`
      →  `TPf_TP` → `pool_TP` → `sysInv_TP` → `sysInv_snInv` → `sysInv_sn`

  and every link is proved, so the decomposition is *checked*, not merely
  asserted. In order: `snPre`/`SNInv` is the
  configuration-level least fixpoint and `snInv_sn` cashes it out as `⌜SN c⌝`;
  `PConfig`/`PoolStep`/`treeView` is the **index-free pool view** and
  `poolStep_of_step` is the simulation that justifies it; `tpPre`/`TP` is the
  pool-level least fixpoint, `Relabel`/`fragStep_relabel`/`TPf_perm` is its
  closure under renumbering (Iris's `twptp_permutation`), and `tp_snInv`
  transports it to `SNInv`; `oblView`/`sysInv_pool` restates `SysInv` on the
  view; and `Frag`/`FragStep`/`TPf` is the **fragment** refinement of `TP` that
  records where the big lock is — without it the merge is unprovable, see the
  note above `TPf_app`'s section. The hole is stated purely in pool terms
  — no `Config`, no `threadPost`, no thread index.
-/

namespace AeneasIris.Semantics

open Iris BI Aeneas.Data.Coinductive
open AeneasIris.Heap (HeapGS heapInterp)
open Aeneas.Std (Result RustEffect RustHeap)

unseal Aeneas.Std.Result

section

variable {hlc : Iris.HasLC} {GF : BundledGFunctors} [Iris.InvGS_gen hlc GF]
variable [HeapGS.{0} GF] {α : Type}

/-- `Config.Diverging` is just "the scheduled thread is `div`". -/
theorem diverging_iff {c : Config α} :
    c.Diverging ↔ c.focus = some Result.div := by
  constructor
  · rintro ⟨t, hf, ht⟩
    simp only [Diverges] at ht
    exact ht ▸ hf
  · intro h
    exact ⟨Result.div, h, rfl⟩

/-- **At `.total`, no reachable configuration silently diverges.**

This is `divOK .total = False` and nothing else: `wpi` of `div` is
`|={∅}=> divOK m`, so at `.total` a thread on `div` owes `False`. It is the
counterpart of `sysInv_not_faulty`, and together they are why the `.total`
reading of the invariant is strictly stronger. -/
theorem sysInv_not_diverging (Φ : α → IProp GF) (c : Config α) :
    SysInv .total Φ c ⊢ iprop(|={∅}=> ⌜¬ c.Diverging⌝) := by
  by_cases hd : c.focus = some Result.div
  · -- The scheduled thread is `div`, so its obligation is `False`.
    refine .trans ?_ (BIFUpdate.mono BI.false_elim)
    have hdiv :
        wpi GF (Rust.rustH (GF := GF) .total) .total (Result.div : Result α)
            (fun v => iprop(|={∅, ⊤}=> threadPost Φ c.current v))
          ⊢ iprop(|={∅}=> False) :=
      (wpi_div_emp (H := Rust.rustH (GF := GF) .total) (m := .total) _).mp
    simp only [SysInv, focusObl, hd, runObl]
    iintro ⟨-, Hwp, -⟩
    iapply (BI.entails_wand hdiv)
    iexact Hwp
  · -- It is not, so the goal is a true pure fact.
    refine .trans (BI.true_intro (P := SysInv .total Φ c)) ?_
    refine .trans ?_ Iris.fupd_intro
    refine BI.pure_intro ?_
    exact fun h => hd (diverging_iff.mp h)

/-! ## What remains: `SN`

`SN c = Acc (fun c₂ c₁ => Step c₁ c₂) c`, i.e. no infinite execution. The
argument cannot be the one used for safety, because safety is proved *per
reachable configuration* with the step count fixed in advance, whereas `SN`
quantifies over all continuations at once. So the induction has to happen
*inside* the logic, on the `wpi` least fixpoint — which is sound at `.total`
precisely because `lat .total = id`, so `wpi` there is a genuine well-founded
least fixpoint and not one that step-indexing has flattened.

Following Iris's `iris/program_logic/total_adequacy.v` (`twp_total`), the proof
is in two halves, both of which are proved below.

* `snPre` / `SNInv` below is the configuration-level least fixpoint: `SNInv c`
  says "every `Step` successor of `c` is again in the relation", with the `wpi`
  well-foundedness supplying the descent. `snInv_sn` turns it into the pure
  `⌜SN c⌝`, by `least_fixpoint_iter` at the motive `⌜SN ·⌝`. **Proved.**
* `sysInv_snInv`, that `SysInv .total Φ c` entails it. **Proved**, via the pool
  and fragment fixpoints below. -/

/-- The functional whose least fixpoint is "this configuration cannot step
forever".

The `|={∅}=>` sits *inside* the `∀ c'`, not outside. That is deliberate and it
is what makes `snInv_sn` go through: the resources have to be spent separately
in each successor branch, because `∀` is additive, whereas a single `|={∅}=>`
in front of the `∀` would have to be commuted past it, which needs
`fupd_plain_forall_2` and is not available in that direction. -/
private def snPre (F : LeibnizO (Config α) → IProp GF) (c : LeibnizO (Config α)) :
    IProp GF :=
  iprop(∀ c' : Config α, ⌜Step c.car c'⌝ → |={∅}=> F ⟨c'⟩)

omit [HeapGS.{0} GF] in
/-- `LeibnizO` is discrete, so every predicate on it is non-expansive. -/
private theorem leibnizO_ne {β : Type _} {P : LeibnizO β → IProp GF} :
    OFE.NonExpansive P :=
  ⟨fun {_ x y} h => by
    obtain ⟨x⟩ := x; obtain ⟨y⟩ := y
    cases LeibnizO.dist_inj h
    exact .rfl⟩

omit [HeapGS.{0} GF] in
/-- Reading one successor out of `snPre` (stated unfolded, so that it matches the
hypothesis the proof mode produces). -/
private theorem snPre_elim (F : LeibnizO (Config α) → IProp GF) {c c' : Config α}
    (h : Step c c') :
    iprop(∀ c'' : Config α, ⌜Step c c''⌝ → |={∅}=> F ⟨c''⟩) ⊢ iprop(|={∅}=> F ⟨c'⟩) :=
  (BI.forall_elim c').trans (BI.imp_mp .rfl (BI.pure_intro h))

private instance snPre_mono : Iris.BIMonoPred (snPre (GF := GF) (α := α)) where
  mono_pred := by
    intro F G _ _
    iintro #Hmono %c HF
    simp only [snPre]
    iintro %c' %hstep
    ihave HF := BI.entails_wand (snPre_elim F hstep) $$ HF
    imod HF with HF
    imodintro
    iapply Hmono $$ HF
  mono_pred_ne := leibnizO_ne

/-- **The configuration-level least fixpoint.** -/
private def SNInv (c : Config α) : IProp GF :=
  Iris.bi_least_fixpoint (snPre (GF := GF) (α := α)) ⟨c⟩

omit [HeapGS.{0} GF] in
/-- One unfolding of `Acc`, in the logic.

`∀` is additive, so each successor branch may spend the whole context; the only
non-trivial step is commuting the `|={∅}=>` out of the `∀`, which is legitimate
here because the body is pure (`fupd_pure_forall`). -/
private theorem sn_of_succ (c : Config α) :
    iprop(∀ c' : Config α, ⌜Step c c'⌝ → |={∅}=> ⌜SN c'⌝)
      ⊢ (iprop(|={∅}=> ⌜SN c⌝) : IProp GF) := by
  refine .trans (BI.forall_mono
    (Ψ := fun c' => iprop(|={∅}=> ⌜Step c c' → SN c'⌝)) (fun c' => ?_)) ?_
  · -- `⌜Step c c'⌝ → |={∅}=> ⌜SN c'⌝ ⊢ |={∅}=> ⌜Step c c' → SN c'⌝`, by cases on
    -- whether the step is possible at all — a meta-level case split, since `c'`
    -- has already been fixed.
    by_cases hstep : Step c c'
    · refine .trans (BI.imp_mp .rfl (BI.pure_intro hstep)) ?_
      exact BIFUpdate.mono (BI.pure_mono (fun h _ => h))
    · exact .trans (BI.pure_intro (fun h => absurd h hstep)) Iris.fupd_intro
  · refine .trans (Iris.fupd_pure_forall (GF := GF) ∅ ∅
      (fun c' => Step c c' → SN c') (subset_refl ..)).mpr ?_
    exact BIFUpdate.mono (BI.pure_forall.mpr.trans
      (BI.pure_mono (Acc.intro (r := fun c₂ c₁ => Step c₁ c₂) c)))

omit [HeapGS.{0} GF] in
/-- The premise of `least_fixpoint_iter` at the motive `⌜SN ·⌝`. -/
private theorem snPre_sn (y : LeibnizO (Config α)) :
    snPre (GF := GF) (fun x => iprop(|={∅}=> ⌜SN x.car⌝)) y
      ⊢ iprop(|={∅}=> ⌜SN y.car⌝) := by
  refine .trans (BI.forall_mono (fun _ => BI.imp_mono_right BIFUpdate.trans))
    (sn_of_succ y.car)

omit [HeapGS.{0} GF] in
/-- **The fixpoint delivers the pure fact.** -/
private theorem snInv_sn (c : Config α) :
    SNInv (GF := GF) (α := α) c ⊢ iprop(|={∅}=> ⌜SN c⌝) := by
  letI : OFE.NonExpansive (fun x : LeibnizO (Config α) => iprop(|={∅}=> ⌜SN x.car⌝)) :=
    leibnizO_ne (GF := GF)
  unfold SNInv
  iintro Hfix
  iapply (Iris.least_fixpoint_iter (F := snPre (GF := GF) (α := α))
      (Φ := fun x => iprop(|={∅}=> ⌜SN x.car⌝))) $$ [] %(⟨c⟩ : LeibnizO (Config α)) Hfix
  iintro !> %y HF
  iapply (BI.entails_wand (snPre_sn y)) $$ HF

/-! ## The index-free pool view

`SNInv` is indexed by a `Config`, and `Config` is *index-dependent*: `current` is
an index into `threads`, and `threadPost Φ i` singles out `i = 0`. That is fatal
for the merge lemma the pool induction needs (Iris's `twptp_app`), which lines
its two halves up only because `twptp` is closed under permutation of the pool.

So the machine is replayed on a pool that carries **no indices in its
obligations**. Two separate views are needed, and keeping them apart is the
point:

* `PConfig` — what the *fixpoint* is indexed by: the remaining trees, the
  current index, the heap. **No postconditions.** Termination does not depend on
  them, and Iris's `twptp` likewise ranges over `list expr`.
* `OThread` — what the *resources* are: a tree together with **its own**
  postcondition. This is where index-freedom actually matters, and it is a
  `Config`-free notion, so a pool of `OThread`s may be permuted freely.

⚠️ The postconditions must be kept **out of the fixpoint's index**, and not
merely for tidiness. `wpi_ind_emp` demands `∀ t, OFE.NonExpansive (G t)` of its
motive `G : ITree → Post → IProp`. The motive for `wpi_TP` is
`G t Ψ = TP (pool containing t)`; if the pool carried `Ψ` the index would be a
`LeibnizO` containing it, whose `dist` is *equality*, so `Ψ ≡{n}≡ Ψ'` would not
give `G t Ψ ≡{n}≡ G t Ψ'` and the induction would not typecheck. With the
postconditions removed the motive is constant in `Ψ` and the obligation is
trivial — which is also the honest statement of the fact that a thread's
postcondition has nothing to do with whether it terminates.

`Machine.lean` is untouched throughout: `treeView` is a derived view and
`poolStep_of_step` says the machine's five rules are mirrored under it.
Tombstones are kept, so the view is index-preserving and the simulation is an
exact one-to-one correspondence rather than an embedding.
-/

/-- A pool thread, for the purpose of *stepping*: just its remaining tree.
`none` is a tombstone, exactly as `Thread.dead` is. -/
abbrev PThread (α : Type) := Option (Result α)

/-- What `TP` is indexed by. No postconditions, no `GF`, no Iris. -/
structure PConfig (α : Type) where
  threads : List (PThread α)
  current : Nat
  heap : RustHeap.{0}

namespace PConfig

variable {α : Type}

def focus (p : PConfig α) : Option (Result α) :=
  match p.threads[p.current]? with
  | some (some t) => some t
  | _ => none

def setFocus (p : PConfig α) (t : Result α) : PConfig α :=
  { p with threads := p.threads.set p.current (some t) }

def kill (p : PConfig α) : PConfig α :=
  { p with threads := p.threads.set p.current none }

def Alive (p : PConfig α) (j : Nat) : Prop := ∃ t, p.threads[j]? = some (some t)

/-- The heap-free part: `TP`'s actual index. `tpPre` quantifies over the heap at
every step, exactly as `twptp_pre` does over `state_interp`, because the merge
lemma has to combine two pools that have already seen different heaps. -/
abbrev pool (p : PConfig α) : List (PThread α) × Nat := (p.threads, p.current)

end PConfig

/-- **The step relation on the pool view.** Literally `Step` with `Thread α`
replaced by `Option (Result α)`; in particular it mentions no postconditions, so
it is a pure `Prop` with no Iris in it at all. -/
inductive PoolStep {α : Type} : PConfig α → PConfig α → Prop where
  | tick {p : PConfig α} {k} :
      p.focus = some (Result.vis stepEv k) →
      PoolStep p (p.setFocus (k PUnit.unit))
  | heap {p : PConfig α} {f k σ'} :
      p.focus = some (Result.vis (modifyEv f) k) →
      f p.heap = some σ' →
      PoolStep p { p.setFocus (k p.heap) with heap := σ' }
  | yield {p : PConfig α} {k j} :
      p.focus = some (Result.vis yieldEv k) →
      (p.setFocus (k PUnit.unit)).Alive j →
      PoolStep p { p.setFocus (k PUnit.unit) with current := j }
  | fork {p : PConfig α} {k} :
      p.focus = some (Result.vis forkEv k) →
      PoolStep p
        { threads := (p.threads.set p.current (some (k Aeneas.Std.ConcE.Tags.cur)))
                       ++ [some (k Aeneas.Std.ConcE.Tags.new)],
          current := p.current,
          heap := p.heap }
  | endthread {p : PConfig α} {k j} :
      p.focus = some (Result.vis endthreadEv k) →
      p.kill.Alive j →
      PoolStep p { p.kill with current := j }

section View

variable {α : Type}

def treeThread : Thread α → PThread α
  | .dead => none
  | .alive t => some t

/-- **The view.** Index-preserving: tombstones stay, `current` and the heap are
copied across. -/
def treeView (c : Config α) : PConfig α :=
  ⟨c.threads.map treeThread, c.current, c.heap⟩

@[simp] theorem treeView_heap (c : Config α) : (treeView c).heap = c.heap := rfl

/-- `PConfig.pool` loses only the heap, and the heap is put straight back. -/
theorem treeView_conf (c : Config α) :
    (⟨(treeView c).pool.1, (treeView c).pool.2, c.heap⟩ : PConfig α) = treeView c := rfl

theorem treeView_focus {c : Config α} {t : Result α} (h : c.focus = some t) :
    (treeView c).focus = some t := by
  have hg : c.threads[c.current]? = some (Thread.alive t) := by
    unfold Config.focus at h
    split at h
    · rename_i heq; simp only [Option.some.injEq] at h; subst h; exact heq
    · exact absurd h (by simp)
  simp only [PConfig.focus, treeView, List.getElem?_map, hg, Option.map_some, treeThread]

theorem treeView_focus_none {c : Config α} (h : c.focus = none) :
    (treeView c).focus = none := by
  rcases hg : c.threads[c.current]? with _ | th
  · simp [PConfig.focus, treeView, List.getElem?_map, hg]
  · cases th with
    | dead => simp [PConfig.focus, treeView, List.getElem?_map, hg, treeThread]
    | alive t =>
      exfalso; unfold Config.focus at h; rw [hg] at h; simp at h

theorem treeView_setFocus (c : Config α) (t : Result α) :
    treeView (c.setFocus t) = (treeView c).setFocus t := by
  simp only [treeView, Config.setFocus, PConfig.setFocus, List.map_set, treeThread]

theorem treeView_kill (c : Config α) : treeView c.kill = (treeView c).kill := by
  simp only [treeView, Config.kill, PConfig.kill, List.map_set, treeThread]

theorem treeView_alive {c : Config α} {j : Nat} (h : c.Alive j) : (treeView c).Alive j := by
  obtain ⟨t, ht⟩ := h
  exact ⟨t, by simp [treeView, List.getElem?_map, ht, treeThread]⟩

/-- **The simulation lemma.** Every machine step is mirrored, one-to-one, by a
`PoolStep` between the views. Nothing in `Machine.lean` changes: the pool is a
derived view, and this is the only fact about it the logic side needs. -/
theorem poolStep_of_step {c c' : Config α} (h : Step c c') :
    PoolStep (treeView c) (treeView c') := by
  cases h
  case tick k hfoc =>
    rw [treeView_setFocus]; exact .tick (treeView_focus hfoc)
  case heap f k σ' hfoc hf =>
    have : treeView { c.setFocus (k c.heap) with heap := σ' }
        = { (treeView c).setFocus (k c.heap) with heap := σ' } := by
      simp only [treeView, Config.setFocus, PConfig.setFocus, List.map_set, treeThread]
    rw [this]; exact .heap (treeView_focus hfoc) hf
  case yield k j hfoc halive =>
    have : treeView { c.setFocus (k PUnit.unit) with current := j }
        = { (treeView c).setFocus (k PUnit.unit) with current := j } := by
      simp only [treeView, Config.setFocus, PConfig.setFocus, List.map_set, treeThread]
    rw [this]
    refine .yield (treeView_focus hfoc) ?_
    rw [← treeView_setFocus]; exact treeView_alive halive
  case fork k hfoc =>
    have : treeView
        { threads := (c.threads.set c.current (.alive (k Aeneas.Std.ConcE.Tags.cur)))
                       ++ [.alive (k Aeneas.Std.ConcE.Tags.new)],
          current := c.current, heap := c.heap }
        = { threads := ((treeView c).threads.set c.current
                          (some (k Aeneas.Std.ConcE.Tags.cur)))
                         ++ [some (k Aeneas.Std.ConcE.Tags.new)],
            current := c.current, heap := c.heap } := by
      simp only [treeView, List.map_append, List.map_set, List.map_cons, List.map_nil, treeThread]
    rw [this]; exact .fork (treeView_focus hfoc)
  case endthread k j hfoc halive =>
    have : treeView { c.kill with current := j } = { (treeView c).kill with current := j } := by
      simp only [treeView, Config.kill, PConfig.kill, List.map_set, treeThread]
    rw [this]
    refine .endthread (treeView_focus hfoc) ?_
    rw [← treeView_kill]; exact treeView_alive halive

end View

/-! ## The pool fixpoint

`TP p` is the analogue of Iris's `twptp`: "the pool `p`, handed the physical
heap, cannot step forever". The heap is quantified inside the unfolding rather
than being part of the index — `twptp_pre` does the same with `state_interp` —
because the merge lemma has to combine two pools that have already seen
different heaps. -/

/-- The functional whose least fixpoint is `TP`. -/
private def tpPre (F : LeibnizO (List (PThread α) × Nat) → IProp GF)
    (p : LeibnizO (List (PThread α) × Nat)) : IProp GF :=
  iprop(∀ (σ : RustHeap.{0}) (r : PConfig α),
          ⌜PoolStep ⟨p.car.1, p.car.2, σ⟩ r⌝ →
          heapInterp σ -∗ |={∅}=> heapInterp r.heap ∗ F ⟨r.pool⟩)

/-- Reading one successor out of `tpPre` (stated unfolded, to match the
hypothesis the proof mode produces). -/
private theorem tpPre_elim (F : LeibnizO (List (PThread α) × Nat) → IProp GF)
    {L : List (PThread α)} {i : Nat} {σ : RustHeap.{0}} {r : PConfig α}
    (h : PoolStep ⟨L, i, σ⟩ r) :
    iprop(∀ (σ₀ : RustHeap.{0}) (q : PConfig α), ⌜PoolStep ⟨L, i, σ₀⟩ q⌝ →
            heapInterp σ₀ -∗ |={∅}=> heapInterp q.heap ∗ F ⟨q.pool⟩)
      ⊢ iprop(heapInterp σ -∗ |={∅}=> heapInterp r.heap ∗ F ⟨r.pool⟩) :=
  ((BI.forall_elim σ).trans (BI.forall_elim r)).trans (BI.imp_mp .rfl (BI.pure_intro h))

private instance tpPre_mono : Iris.BIMonoPred (tpPre (GF := GF) (α := α)) where
  mono_pred := by
    intro F G _ _
    iintro #Hmono %p HF
    simp only [tpPre]
    iintro %σ %r %hstep Hheap
    ihave HF := BI.entails_wand (tpPre_elim F hstep) $$ HF
    imod HF $$ Hheap with ⟨Hh, HFp⟩
    imodintro
    iframe Hh
    iapply Hmono $$ HFp
  mono_pred_ne := leibnizO_ne

/-- **The pool-level least fixpoint.** -/
private def TP (p : List (PThread α) × Nat) : IProp GF :=
  Iris.bi_least_fixpoint (tpPre (GF := GF) (α := α)) ⟨p⟩

/-- **A pool whose scheduled slot is dead or out of range is trivially `TP`.**
No `PoolStep` fires, so the fixpoint's unfolding is vacuous. This is the
`KillLastThread` case, and it is also every index of a singleton pool other than
`0`. -/
private theorem tp_stuck {L : List (PThread α)} {i : Nat}
    (h : ∀ σ : RustHeap.{0}, (⟨L, i, σ⟩ : PConfig α).focus = none) :
    iprop(emp) ⊢ TP (GF := GF) (L, i) := by
  refine .trans ?_ (Iris.least_fixpoint_unfold_mpr (tpPre (GF := GF) (α := α)) (x := ⟨(L, i)⟩))
  simp only [tpPre]
  refine BI.forall_intro fun σ => BI.forall_intro fun r => BI.imp_intro ?_
  refine BI.pure_elim _ BI.and_elim_r fun hstep => ?_
  exact absurd (h σ) (by cases hstep <;> simp_all)

/-! ### From `TP` to `SNInv` -/

omit [HeapGS.{0} GF] in
/-- One `Acc` step of `SNInv`, as a plain entailment: this is
`least_fixpoint_unfold_mpr` with both sides already unfolded, so that it can be
composed with `.trans` instead of being `iapply`d (the proof mode unfolds
`bi_least_fixpoint`'s leading `∀` and then cannot match). -/
private theorem snInv_intro (c : Config α) :
    iprop(∀ c' : Config α, ⌜Step c c'⌝ → |={∅}=> SNInv c')
      ⊢ SNInv (GF := GF) (α := α) c :=
  Iris.least_fixpoint_unfold_mpr (snPre (GF := GF) (α := α)) (x := ⟨c⟩)

/-- `tpPre_elim` along a machine step, with the heap projections already
normalised — they are definitionally equal, but the proof mode matches
syntactically. -/
private theorem tpPre_elim_step (F : LeibnizO (List (PThread α) × Nat) → IProp GF)
    {c c' : Config α} (h : Step c c') :
    iprop(∀ (σ₀ : RustHeap.{0}) (q : PConfig α),
            ⌜PoolStep ⟨(treeView c).pool.1, (treeView c).pool.2, σ₀⟩ q⌝ →
            heapInterp σ₀ -∗ |={∅}=> heapInterp q.heap ∗ F ⟨q.pool⟩)
      ⊢ iprop(heapInterp c.heap -∗ |={∅}=> heapInterp c'.heap ∗ F ⟨(treeView c').pool⟩) :=
  tpPre_elim (σ := c.heap) (r := treeView c') F (poolStep_of_step h)

private def snMotive (q : LeibnizO (List (PThread α) × Nat)) : IProp GF :=
  iprop(∀ c : Config α, ⌜(treeView c).pool = q.car⌝ → (heapInterp c.heap -∗ SNInv c))

private theorem snMotive_elim (c : Config α) :
    snMotive (GF := GF) ⟨(treeView c).pool⟩ ⊢ iprop(heapInterp c.heap -∗ SNInv c) :=
  (BI.forall_elim c).trans (BI.imp_mp .rfl (BI.pure_intro rfl))

/-- The premise of `least_fixpoint_iter`. One `PoolStep` is produced from one
`Step` by `poolStep_of_step`, and `SNInv` is rebuilt one machine step at a time
with `snInv_intro`. -/
private theorem tpPre_snMotive (p : LeibnizO (List (PThread α) × Nat)) :
    tpPre (snMotive (GF := GF)) p ⊢ snMotive (GF := GF) p := by
  refine BI.forall_intro fun c => BI.imp_intro ?_
  refine BI.pure_elim _ BI.and_elim_r fun hview => BI.and_elim_l.trans ?_
  simp only [tpPre]
  rw [← hview]
  refine .trans ?_ (BI.wand_mono_right (snInv_intro c))
  iintro H Hheap %c' %hstep
  ihave H := BI.entails_wand (tpPre_elim_step (snMotive (GF := GF)) hstep) $$ H
  imod H $$ Hheap with ⟨Hh, HΨ⟩
  imodintro
  ihave HΨ := BI.entails_wand (snMotive_elim c') $$ HΨ
  iapply HΨ $$ Hh

/-- **The pool fixpoint delivers the configuration fixpoint.** -/
private theorem tp_snInv (c : Config α) :
    TP (treeView c).pool ⊢ iprop(heapInterp c.heap -∗ SNInv (GF := GF) c) := by
  letI : OFE.NonExpansive (snMotive (GF := GF) (α := α)) := leibnizO_ne (GF := GF)
  unfold TP
  iintro Hfix
  iapply (BI.entails_wand (snMotive_elim c))
  iapply (Iris.least_fixpoint_iter (F := tpPre (GF := GF) (α := α)) (Φ := snMotive))
    $$ [] %(⟨(treeView c).pool⟩ : LeibnizO (List (PThread α) × Nat)) Hfix
  iintro !> %q HF
  iapply (BI.entails_wand (tpPre_snMotive q)) $$ HF

/-! ### The obligations

`SysInv`'s components, restated on a pool of `OThread`s. They are
*definitionally* `runObl` / `readyObl` / `focusObl` at `.total` — the only change
is that the postcondition is read off the thread instead of being computed from
its index, which is what makes the pool permutable. -/

/-- A pool thread together with **its own** postcondition. -/
abbrev OThread (GF : BundledGFunctors) (α : Type) := Option (Result α × Post GF α)

def OThread.tree (x : OThread GF α) : PThread α := x.map Prod.fst

/-- The obligation of a thread that holds the big lock. -/
private def runOb (x : Result α × Post GF α) : IProp GF :=
  wpi GF (Rust.rustH (GF := GF) .total) .total x.1 x.2

/-- The obligation of a parked thread: it still owes the mask-opening update. -/
private def parkOb : OThread GF α → IProp GF
  | none => iprop(emp)
  | some x => iprop(|={⊤, ∅}=> runOb x)

/-- The obligation of the scheduled thread, or `emp` if there is none. -/
private def oFocusObl (L : List (OThread GF α)) (i : Nat) : IProp GF :=
  match L[i]? with
  | some (some x) => runOb x
  | _ => iprop(emp)

def oblThread (Φ : α → IProp GF) (i : Nat) : Thread α → OThread GF α
  | .dead => none
  | .alive t => some (t, fun v => iprop(|={∅, ⊤}=> threadPost Φ i v))

def oblView (Φ : α → IProp GF) (c : Config α) : List (OThread GF α) :=
  c.threads.mapIdx (oblThread Φ)

omit [HeapGS.{0} GF] in
/-- `[∗list]` commutes with `List.mapIdx`. -/
private theorem bigSepL_mapIdx {A B : Type _} :
    ∀ (l : List A) (f : Nat → A → B) (Ψ : Nat → B → IProp GF),
      iprop([∗list] k ↦ y ∈ l.mapIdx f, Ψ k y) ⊣⊢ iprop([∗list] k ↦ x ∈ l, Ψ k (f k x)) := by
  intro l
  induction l with
  | nil => intro f Ψ; simp only [List.mapIdx_nil]; exact .rfl
  | cons x xs ih =>
    intro f Ψ
    simp only [List.mapIdx_cons]
    exact ⟨BI.sep_mono_right (ih (fun i => f (i + 1)) (fun k y => Ψ (k + 1) y)).mp,
           BI.sep_mono_right (ih (fun i => f (i + 1)) (fun k y => Ψ (k + 1) y)).mpr⟩

/-- `List.map` after `List.mapIdx`, when the composite ignores the index. -/
private theorem mapIdx_map_eq {A B C : Type _} (g : B → C) (h : A → C) :
    ∀ (l : List A) (f : Nat → A → B), (∀ i x, g (f i x) = h x) →
      (l.mapIdx f).map g = l.map h := by
  intro l
  induction l with
  | nil => intro f _; simp
  | cons x xs ih =>
    intro f hf
    simp only [List.mapIdx_cons, List.map_cons, hf,
      ih (fun i => f (i + 1)) (fun i y => hf (i + 1) y)]

omit [HeapGS.{0} GF] in
/-- Erasing the postconditions from the obligation view gives the tree view. -/
theorem oblView_tree (Φ : α → IProp GF) (c : Config α) :
    (oblView Φ c).map OThread.tree = (treeView c).threads :=
  mapIdx_map_eq OThread.tree treeThread c.threads (oblThread Φ)
    (fun _ th => by cases th <;> rfl)

/-- The pool obligations really are `SysInv`'s, thread by thread. -/
private theorem parkOb_oblThread (Φ : α → IProp GF) (i : Nat) (th : Thread α) :
    parkOb (oblThread Φ i th) = readyObl .total Φ i th := by
  cases th <;> rfl

private theorem oFocusObl_eq (Φ : α → IProp GF) (c : Config α) :
    oFocusObl (oblView Φ c) c.current = focusObl .total Φ c := by
  rcases h : c.threads[c.current]? with _ | th
  · have : c.focus = none := by unfold Config.focus; rw [h]
    simp only [oFocusObl, focusObl, oblView, List.getElem?_mapIdx, h, this, Option.map_none]
  · cases th with
    | dead =>
      have : c.focus = none := by unfold Config.focus; rw [h]
      simp only [oFocusObl, focusObl, oblView, List.getElem?_mapIdx, h, this,
        Option.map_some, oblThread]
    | alive t =>
      have : c.focus = some t := by unfold Config.focus; rw [h]
      simp only [oFocusObl, focusObl, oblView, List.getElem?_mapIdx, h, this,
        Option.map_some, oblThread]
      rfl

omit [HeapGS.{0} GF] in
private theorem oblView_kill (Φ : α → IProp GF) (c : Config α) :
    (oblView Φ c).set c.current none = oblView Φ c.kill := by
  simp only [oblView, Config.kill, List.mapIdx_set, oblThread]

/-- **`SysInv`, restated on the obligation pool.** This is where the
index-dependence of `threadPost Φ i` is discharged once and for all. -/
private theorem sysInv_pool (Φ : α → IProp GF) (c : Config α) :
    SysInv .total Φ c ⊢
      iprop(heapInterp c.heap ∗ oFocusObl (oblView Φ c) c.current ∗
            [∗list] x ∈ (oblView Φ c).set c.current none, parkOb x) := by
  have h1 : oFocusObl (oblView Φ c) c.current = focusObl .total Φ c := oFocusObl_eq Φ c
  have h2 : (oblView Φ c).set c.current none = oblView Φ c.kill := oblView_kill Φ c
  simp only [SysInv, h1, h2]
  refine BI.sep_mono_right (BI.sep_mono_right ?_)
  simp only [oblView]
  refine .trans ?_ (bigSepL_mapIdx c.kill.threads (oblThread Φ) (fun _ y => parkOb y)).mpr
  simp only [parkOb_oblThread]
  exact .rfl

/-! ### The last piece of `Terminates`

`pool_TPf` is Iris's `twp_twptp` **plus** `twptp_app`
(`iris/program_logic/total_adequacy.v`), and it is the last piece of
`Terminates`. It is decomposed here into named declarations, so that each step
of the argument is separately checkable rather than hidden in one monolith.

The dependency order is

    `TPf_perm`/`TPf_rot`  →  `TPf_app`  →  `wpi_TPf`

— `wpi_TPf` is *not* independent of the merge, because its `fork` branch turns a
one-element pool into a two-element one. All three are proved below.

**The mathematical argument.** Give each live thread the ordinal rank `ρ t` of
its `wpi` derivation — well defined at `.total`, where `wpi` is a `▷`-free least
fixpoint — and rank a pool by the *multiset* `{ρ t | t live}`. Every one of the
five rules strictly decreases it in the Dershowitz–Manna order:

* `tick`, `heap` — the scheduled thread is replaced by `k …`, whose obligation
  is the `Ψ` branch of `wpiAcc`, so `ρ` drops; every other thread is untouched.
* `yield` — likewise `ρ` drops for the *yielding* thread. Control moving to `j`
  changes `current`, not the multiset.
* `endthread` — a thread is removed outright.
* `fork` — one element `ρ t` is replaced by *two*, the parent's `Ψ .cur` and the
  child's `B .new` branch of `wpiAcc`; both are strictly below `ρ t`, so this is
  exactly a multiset decrease. The child is covered because `wpi_ind_emp` hands
  out an induction hypothesis for the `B` branch too.

The descent comes from `wpi`, never from preservation: `sysInv_step_total` says
`SysInv` is a *post*-fixpoint of the step relation, which gives membership in the
**greatest** fixpoint, not the least. It is still needed — it is the `▷`-free
form the pool induction has to consume, and `tpPre` must not carry a `▷` or the
fixpoint would stop being well-founded — but it is a lemma *inside* the argument,
not the argument.

Multiset induction is not a single application of `least_fixpoint_ind`, which is
why the merge below is separate: inducting on the scheduled thread's `runOb`
gets `tick`, `heap` and `fork`, but breaks at `yield` and `endthread`, where the
new focus is *another* thread whose `parkOb` carries no induction hypothesis.
Iris's answer is a nested induction, outer on one half of the pool and inner on
the other. -/

/-! ### The fragment fixpoint

A *fragment* is a slice of the pool together with the location of the big lock
**relative to it**: `none` says the lock is somewhere else, so the fragment is
entirely parked and simply waits. This is what `TP` lacks — `TP (L, i)` describes
executions that *start* with the lock at `i` and carries nothing about the lock
leaving and coming back. See the note below for why that is fatal. -/

/-- A pool fragment: its threads, and where the big lock is — `none` if the lock
is outside this fragment. -/
abbrev Frag (α : Type) := List (PThread α) × Option Nat

/-- The mask a fragment sits at: it owns `ownE ⊤` exactly when it does *not*
hold the lock, because a scheduled thread has already spent the token inside its
`wpi` (see `Invariant.lean`'s "Where `ownE ⊤` lives"). -/
def curMask : Option Nat → CoPset
  | none => ⊤
  | some _ => ∅

def fragFocus {α : Type} (L : List (PThread α)) (i : Nat) : Option (Result α) :=
  match L[i]? with
  | some (some t) => some t
  | _ => none

def fragAlive {α : Type} (L : List (PThread α)) (j : Nat) : Prop :=
  ∃ t, L[j]? = some (some t)

/-- **Steps of a fragment that holds the lock.**

`PoolStep`'s `yield` and `endthread` are split into a *release*, which hands
`ownE ⊤` back to the ambient and leaves the fragment parked, and — on the
receiving side — the *acquire* built into `tpfPre`'s parked branch. Splitting
them is the whole point: a `yield` that moves the lock to another fragment is
then a step of the fragment that owns it, which is exactly what the merge's
induction needs and what `PoolStep` could not express. A `yield` back into the
same fragment is a release followed by an acquire. -/
inductive FragStep {α : Type} :
    List (PThread α) → Nat → RustHeap.{0} → Frag α → RustHeap.{0} → Prop where
  | tick {L i k σ} :
      fragFocus L i = some (Result.vis stepEv k) →
      FragStep L i σ (L.set i (some (k PUnit.unit)), some i) σ
  | heap {L i f k σ σ'} :
      fragFocus L i = some (Result.vis (modifyEv f) k) → f σ = some σ' →
      FragStep L i σ (L.set i (some (k σ)), some i) σ'
  | fork {L i k σ} :
      fragFocus L i = some (Result.vis forkEv k) →
      FragStep L i σ
        (L.set i (some (k Aeneas.Std.ConcE.Tags.cur))
           ++ [some (k Aeneas.Std.ConcE.Tags.new)], some i) σ
  | releaseYield {L i k σ} :
      fragFocus L i = some (Result.vis yieldEv k) →
      FragStep L i σ (L.set i (some (k PUnit.unit)), none) σ
  | releaseEnd {L i k σ} :
      fragFocus L i = some (Result.vis endthreadEv k) →
      FragStep L i σ (L.set i none, none) σ

/-- The functional whose least fixpoint is `TPf`.

The two branches are the two states a fragment can be in. A parked fragment
(`none`) takes no machine step at all; it only waits to *acquire* the lock, at
the `|={⊤,∅}=>` that spends the token. A running fragment steps at `∅` and lands
at `curMask` of wherever the lock ends up — `∅` for an internal step, `⊤` for a
release, which is precisely `ConcH`'s `yield ↦ |={∅,⊤}=> |={⊤,∅}=> Ψ ()` cut in
half. -/
private def tpfPre (F : LeibnizO (Frag α) → IProp GF) (p : LeibnizO (Frag α)) :
    IProp GF :=
  match p.car.2 with
  | none => iprop(∀ j : Nat, ⌜fragAlive p.car.1 j⌝ → |={⊤, ∅}=> F ⟨(p.car.1, some j)⟩)
  | some i =>
    iprop(∀ (σ : RustHeap.{0}) (q : Frag α) (σ' : RustHeap.{0}),
            ⌜FragStep p.car.1 i σ q σ'⌝ →
            heapInterp σ -∗ |={∅, curMask q.2}=> heapInterp σ' ∗ F ⟨q⟩)

omit [HeapGS.{0} GF] in
private theorem forall_imp_elim {β : Type _} {ψ : β → Prop} {P : β → IProp GF}
    (b : β) (h : ψ b) : iprop(∀ x, ⌜ψ x⌝ → P x) ⊢ P b :=
  (BI.forall_elim b).trans (BI.imp_mp .rfl (BI.pure_intro h))

omit [HeapGS.{0} GF] in
private theorem forall3_imp_elim {β γ δ : Type _} {ψ : β → γ → δ → Prop}
    {P : β → γ → δ → IProp GF} (b : β) (c : γ) (d : δ) (h : ψ b c d) :
    iprop(∀ x y z, ⌜ψ x y z⌝ → P x y z) ⊢ P b c d :=
  (((BI.forall_elim b).trans (BI.forall_elim c)).trans (BI.forall_elim d)).trans
    (BI.imp_mp .rfl (BI.pure_intro h))

private instance tpfPre_mono : Iris.BIMonoPred (tpfPre (GF := GF) (α := α)) where
  mono_pred := by
    intro F G _ _
    iintro #Hmono %p
    rcases hc : p.car.2 with _ | i
    · simp only [tpfPre, hc]
      iintro HF %j %hal
      ihave HF := BI.entails_wand (forall_imp_elim
        (P := fun j => iprop(|={⊤, ∅}=> F ⟨(p.car.1, some j)⟩)) j hal) $$ HF
      imod HF with HF
      imodintro
      iapply Hmono $$ HF
    · simp only [tpfPre, hc]
      iintro HF %σ %q %σ' %hstep Hheap
      ihave HF := BI.entails_wand (forall3_imp_elim
        (P := fun σ q σ' =>
          iprop(heapInterp σ -∗ |={∅, curMask q.2}=> heapInterp σ' ∗ F ⟨q⟩))
        σ q σ' hstep) $$ HF
      imod HF $$ Hheap with ⟨Hh, HFq⟩
      imodintro
      iframe Hh
      iapply Hmono $$ HFq
  mono_pred_ne := leibnizO_ne

/-- **The fragment fixpoint.** `TPf (L, some i)` is "this fragment holds the lock
at `i` and cannot run forever"; `TPf (L, none)` is "this fragment is parked and,
whenever the lock arrives, cannot run forever" — the notion the old `TPall` was
trying to express as a derived `∀`, now a fixpoint in its own right. -/
private def TPf (p : Frag α) : IProp GF :=
  Iris.bi_least_fixpoint (tpfPre (GF := GF) (α := α)) ⟨p⟩

/-- A fragment whose scheduled slot is dead or out of range is trivially `TPf`:
no `FragStep` fires. -/
private theorem tpf_stuck {L : List (PThread α)} {i : Nat} (h : fragFocus L i = none) :
    iprop(emp) ⊢ TPf (GF := GF) (L, some i) := by
  refine .trans ?_ (Iris.least_fixpoint_unfold_mpr (tpfPre (GF := GF) (α := α))
    (x := ⟨(L, some i)⟩))
  simp only [tpfPre]
  refine BI.forall_intro fun σ => BI.forall_intro fun q => BI.forall_intro fun σ' =>
    BI.imp_intro ?_
  refine BI.pure_elim _ BI.and_elim_r fun hstep => ?_
  exact absurd h (by cases hstep <;> simp_all)

/-! ### `TPf` implies `TP`

A fragment that holds the whole pool is `TP` of it. The only interesting case is
`yield`/`endthread`: one `PoolStep` is a *release* followed by an *acquire*, and
their masks compose, `|={∅,⊤}=>` then `|={⊤,∅}=>`, back into the single
`|={∅}=>` that `tpPre` asks for — literally `ConcH`'s clause for `yield` put back
together. -/

/-- One internal `FragStep`, with `curMask` already reduced. -/
private theorem tpf_run_int (F : LeibnizO (Frag α) → IProp GF)
    {L L' : List (PThread α)} {i i' : Nat} {σ σ' : RustHeap.{0}}
    (h : FragStep L i σ (L', some i') σ') :
    iprop(∀ (σ₀ : RustHeap.{0}) (q : Frag α) (σ₁ : RustHeap.{0}),
            ⌜FragStep L i σ₀ q σ₁⌝ →
            heapInterp σ₀ -∗ |={∅, curMask q.2}=> heapInterp σ₁ ∗ F ⟨q⟩)
      ⊢ iprop(heapInterp σ -∗ |={∅}=> heapInterp σ' ∗ F ⟨((L', some i') : Frag α)⟩) :=
  forall3_imp_elim σ ((L', some i') : Frag α) σ' h

/-- One releasing `FragStep`: it ends at mask `⊤`, the token back in the ambient. -/
private theorem tpf_run_rel (F : LeibnizO (Frag α) → IProp GF)
    {L L' : List (PThread α)} {i : Nat} {σ σ' : RustHeap.{0}}
    (h : FragStep L i σ (L', none) σ') :
    iprop(∀ (σ₀ : RustHeap.{0}) (q : Frag α) (σ₁ : RustHeap.{0}),
            ⌜FragStep L i σ₀ q σ₁⌝ →
            heapInterp σ₀ -∗ |={∅, curMask q.2}=> heapInterp σ₁ ∗ F ⟨q⟩)
      ⊢ iprop(heapInterp σ -∗ |={∅, ⊤}=> heapInterp σ' ∗ F ⟨((L', none) : Frag α)⟩) :=
  forall3_imp_elim σ ((L', none) : Frag α) σ' h

private def tpfMotive (q : LeibnizO (Frag α)) : IProp GF :=
  match q.car.2 with
  | none => iprop(∀ j : Nat, |={⊤, ∅}=> TP (q.car.1, j))
  | some i => TP (q.car.1, i)

private theorem tpfMotive_run (L : List (PThread α)) (i : Nat) :
    tpfMotive (GF := GF) ⟨((L, some i) : Frag α)⟩
      ⊢ Iris.bi_least_fixpoint (tpPre (GF := GF) (α := α)) ⟨(L, i)⟩ := .rfl

private theorem tp_unfold (p : List (PThread α) × Nat) :
    TP (GF := GF) p ⊢ Iris.bi_least_fixpoint (tpPre (GF := GF) (α := α)) ⟨p⟩ := .rfl

private theorem tpfMotive_park (L : List (PThread α)) (j : Nat) :
    tpfMotive (GF := GF) ⟨((L, none) : Frag α)⟩ ⊢ iprop(|={⊤, ∅}=> TP (L, j)) :=
  BI.forall_elim j

private theorem fragFocus_of_not_alive {L : List (PThread α)} {j : Nat}
    (h : ¬ fragAlive L j) : fragFocus L j = none := by
  simp only [fragFocus]
  rcases hg : L[j]? with _ | th
  · rfl
  · cases th with
    | none => rfl
    | some t => exact absurd ⟨t, hg⟩ h

private theorem tpfPre_tpfMotive (q : LeibnizO (Frag α)) :
    tpfPre (tpfMotive (GF := GF)) q ⊢ tpfMotive (GF := GF) q := by
  rcases hc : q.car.2 with _ | i
  · simp only [tpfMotive, tpfPre, hc]
    refine BI.forall_intro fun j => ?_
    by_cases hal : fragAlive q.car.1 j
    · exact forall_imp_elim
        (P := fun j => iprop(|={⊤, ∅}=>
          tpfMotive (GF := GF) ⟨((q.car.1, some j) : Frag α)⟩)) j hal
    · refine BI.affine.trans ?_
      exact (tp_stuck (fun _ => fragFocus_of_not_alive hal)).trans
        (Iris.fupd_mask_intro_discard Iris.Std.LawfulSet.empty_subset)
  · simp only [tpfMotive, hc]
    refine .trans ?_ (Iris.least_fixpoint_unfold_mpr (tpPre (GF := GF) (α := α))
      (x := ⟨(q.car.1, i)⟩))
    simp only [tpPre, tpfPre, hc]
    refine BI.forall_intro fun σ => BI.forall_intro fun r => BI.imp_intro ?_
    refine BI.pure_elim _ BI.and_elim_r fun hstep => BI.and_elim_l.trans ?_
    cases hstep
    case tick k hf =>
      simp only [PConfig.setFocus]
      iintro H Hheap
      ihave H := BI.entails_wand
        (tpf_run_int (tpfMotive (GF := GF))
          (FragStep.tick (L := q.car.1) (i := i) (σ := σ) hf)) $$ H
      imod H $$ Hheap with ⟨Hh, HT⟩
      imodintro
      iframe Hh
      ihave HT := BI.entails_wand (tpfMotive_run _ _) $$ HT
      iexact HT
    case heap f k σ' hf hfσ =>
      simp only [PConfig.setFocus]
      iintro H Hheap
      ihave H := BI.entails_wand
        (tpf_run_int (tpfMotive (GF := GF))
          (FragStep.heap (L := q.car.1) (i := i) (σ := σ) hf hfσ)) $$ H
      imod H $$ Hheap with ⟨Hh, HT⟩
      imodintro
      iframe Hh
      ihave HT := BI.entails_wand (tpfMotive_run _ _) $$ HT
      iexact HT
    case fork k hf =>
      iintro H Hheap
      ihave H := BI.entails_wand
        (tpf_run_int (tpfMotive (GF := GF))
          (FragStep.fork (L := q.car.1) (i := i) (σ := σ) hf)) $$ H
      imod H $$ Hheap with ⟨Hh, HT⟩
      imodintro
      iframe Hh
      ihave HT := BI.entails_wand (tpfMotive_run _ _) $$ HT
      iexact HT
    case yield k j hf hal =>
      simp only [PConfig.setFocus]
      iintro H Hheap
      ihave H := BI.entails_wand
        (tpf_run_rel (tpfMotive (GF := GF))
          (FragStep.releaseYield (L := q.car.1) (i := i) (σ := σ) hf)) $$ H
      imod H $$ Hheap with ⟨Hh, HT⟩
      ihave HT := BI.entails_wand (tpfMotive_park _ j) $$ HT
      imod HT with HT
      imodintro
      iframe Hh
      ihave HT := BI.entails_wand (tp_unfold _) $$ HT
      iexact HT
    case endthread k j hf hal =>
      simp only [PConfig.kill]
      iintro H Hheap
      ihave H := BI.entails_wand
        (tpf_run_rel (tpfMotive (GF := GF))
          (FragStep.releaseEnd (L := q.car.1) (i := i) (σ := σ) hf)) $$ H
      imod H $$ Hheap with ⟨Hh, HT⟩
      ihave HT := BI.entails_wand (tpfMotive_park _ j) $$ HT
      imod HT with HT
      imodintro
      iframe Hh
      ihave HT := BI.entails_wand (tp_unfold _) $$ HT
      iexact HT

/-- **A fragment holding the whole pool gives `TP`.** -/
private theorem TPf_TP (L : List (PThread α)) (i : Nat) :
    TPf (GF := GF) (L, some i) ⊢ TP (L, i) := by
  letI : OFE.NonExpansive (tpfMotive (GF := GF) (α := α)) := leibnizO_ne (GF := GF)
  refine .trans ?_ (show tpfMotive (GF := GF) ⟨((L, some i) : Frag α)⟩ ⊢ TP (L, i) from .rfl)
  show Iris.bi_least_fixpoint (tpfPre (GF := GF) (α := α)) ⟨((L, some i) : Frag α)⟩ ⊢ _
  iintro Hfix
  iapply (Iris.least_fixpoint_iter (F := tpfPre (GF := GF) (α := α)) (Φ := tpfMotive))
    $$ [] %(⟨((L, some i) : Frag α)⟩ : LeibnizO (Frag α)) Hfix
  iintro !> %p HF
  iapply (BI.entails_wand (tpfPre_tpfMotive p)) $$ HF

/-! ### Singleton fragments

Three small facts about one-slot fragments, used by `wpi_TPf` below. They are
stated here because they need only `tpfPre`/`TPf`, not the merge. -/

/-- `fragFocus` of a one-slot fragment at its only index. -/
private theorem fragFocus_singleton (t : Result α) :
    fragFocus ([some t] : List (PThread α)) 0 = some t := rfl

/-- **Parking a singleton.** `TPf ([some u], none)` is exactly "when the lock
arrives, `[some u]` cannot run forever", and slot `0` is the only one that can
receive it — so the parked branch is one `|={⊤,∅}=>` away from the running one.
This is the shape a freshly forked child, and a released thread, come in. -/
private theorem TPf_park_singleton (u : Result α) :
    iprop(|={⊤, ∅}=> TPf (GF := GF) ([some u], some 0))
      ⊢ TPf (GF := GF) ([some u], none) := by
  refine .trans ?_ (Iris.least_fixpoint_unfold_mpr (tpfPre (GF := GF) (α := α))
    (x := ⟨(([some u], none) : Frag α)⟩))
  simp only [tpfPre]
  refine BI.forall_intro fun j => BI.imp_intro ?_
  refine BI.pure_elim _ BI.and_elim_r fun hal => BI.and_elim_l.trans ?_
  obtain ⟨w, hw⟩ := hal
  rcases j with _ | j
  · exact .rfl
  · exact absurd hw (by simp)

/-- **A tombstoned singleton is parked for ever.** Nothing is alive in `[none]`,
so the parked branch is vacuous. This is `endthread` on the last thread — the
paper's `KillLastThread`. -/
private theorem TPf_dead_singleton :
    iprop(emp) ⊢ TPf (GF := GF) (([none] : List (PThread α)), none) := by
  refine .trans ?_ (Iris.least_fixpoint_unfold_mpr (tpfPre (GF := GF) (α := α))
    (x := ⟨((([none] : List (PThread α)), none) : Frag α)⟩))
  simp only [tpfPre]
  refine BI.forall_intro fun j => BI.imp_intro ?_
  refine BI.pure_elim _ BI.and_elim_r fun hal => ?_
  exact absurd hal (by rcases j with _ | j <;> simp [fragAlive])

/-! ### Opening `rustH`

One equation per summand of `rustH = failH ⊕ₕ ConcH ⊕ₕ stepH m ⊕ₕ stateH`, as in
`Semantics/Preservation.lean` (they are `private` there, and this file does not
import it). All hold by `rfl`: the sum handler dispatches on a literal `Sum`
injection and the `*Ev` abbreviations are `@[match_pattern]`. -/

private theorem tRustH_step (Ψ B : RustEffect.O stepEv → IProp GF) :
    (Rust.rustH (GF := GF) .total).run stepEv Ψ B = Ψ PUnit.unit := rfl

private theorem tRustH_modify (f : RustHeap.{0} → Option RustHeap.{0})
    (Ψ B : RustEffect.O (modifyEv f) → IProp GF) :
    (Rust.rustH (GF := GF) .total).run (modifyEv f) Ψ B =
      iprop(∀ s, heapInterp s ={∅}=∗ ∃ s', ⌜f s = some s'⌝ ∗ heapInterp s' ∗ Ψ s) := rfl

private theorem tRustH_fork (Ψ B : RustEffect.O forkEv → IProp GF) :
    (Rust.rustH (GF := GF) .total).run forkEv Ψ B =
      iprop(Ψ Aeneas.Std.ConcE.Tags.cur ∗ B Aeneas.Std.ConcE.Tags.new) := rfl

private theorem tRustH_yield (Ψ B : RustEffect.O yieldEv → IProp GF) :
    (Rust.rustH (GF := GF) .total).run yieldEv Ψ B =
      iprop(|={∅, ⊤}=> |={⊤, ∅}=> Ψ PUnit.unit) := rfl

private theorem tRustH_endthread (Ψ B : RustEffect.O endthreadEv → IProp GF) :
    (Rust.rustH (GF := GF) .total).run endthreadEv Ψ B = iprop(|={∅, ⊤}=> True) := rfl

/-- `stateH`'s answer, resolved against the `f σ = some σ'` that `FragStep.heap`
carries. The existential is single-valued, so the successor heap in the goal and
the one the handler produces are the same; doing the elimination here keeps the
pure equation out of the proof-mode context. -/
private theorem tRustH_modify_out {f : RustHeap.{0} → Option RustHeap.{0}}
    {σ σ' : RustHeap.{0}} (hfσ : f σ = some σ') (X : RustHeap.{0} → IProp GF) :
    iprop(∀ s, heapInterp s ={∅}=∗ ∃ s', ⌜f s = some s'⌝ ∗ heapInterp s' ∗ X s)
      ⊢ iprop(heapInterp σ ={∅}=∗ heapInterp σ' ∗ X σ) := by
  refine (BI.forall_elim σ).trans (BI.wand_mono_right (BIFUpdate.mono ?_))
  refine BI.exists_elim fun s => ?_
  by_cases h : s = σ'
  · subst h
    iintro ⟨%_hc, Hh, HX⟩
    iframe Hh
    iexact HX
  · iintro ⟨%hc, _Hh, _HX⟩
    rw [hfσ] at hc
    exact absurd (Option.some.inj hc).symm h

/-! ### The last link: one thread, holding the lock, terminates -/

/-- Where the lock ends up in a merged pool. At most one side may hold it. -/
private def joinCur (n₁ : Nat) : Option Nat → Option Nat → Option Nat
  | some i, _ => some i
  | none, some j => some (n₁ + j)
  | none, none => none

/-! ### Relabelling a pool

`TPf_rot` further below is *not* provable by a direct induction: its own `fork`
case appends the fresh slot after `z` on one side and before it on the other, so
the successor is no longer a rotation of the form it speaks about. The induction
has to be run on the general statement — a pool is `TPf` up to any bijective
renumbering of its slots — which *is* closed under `fork`, because `fork`
extends both pools by one slot at the same index. This is precisely Iris's
`twptp_permutation`, and `unrotIdx` is then one instance of it. -/

/-- A relabelling of a pool's slots: a bijection of indices under which the two
pools agree. Requiring it to fix every index at or beyond the (common) length is
what makes it survive `PoolStep.fork`, which appends a fresh slot to both at the
same position. -/
structure Relabel {α : Type} (N M : List (PThread α)) where
  fwd : Nat → Nat
  bwd : Nat → Nat
  bwd_fwd : ∀ n, bwd (fwd n) = n
  fwd_bwd : ∀ n, fwd (bwd n) = n
  len : M.length = N.length
  get : ∀ n, M[fwd n]? = N[n]?
  fix : ∀ n, N.length ≤ n → fwd n = n

namespace Relabel

variable {α : Type} {N M : List (PThread α)}

theorem fwd_inj (R : Relabel N M) {m n : Nat} (h : R.fwd m = R.fwd n) : m = n := by
  rw [← R.bwd_fwd m, ← R.bwd_fwd n, h]

theorem lt_iff (R : Relabel N M) (n : Nat) : R.fwd n < M.length ↔ n < N.length := by
  constructor
  · intro h
    by_contra hn
    have := R.get n
    rw [List.getElem?_eq_none (Nat.le_of_not_lt hn)] at this
    exact absurd this (by
      rw [List.getElem?_eq_some_iff.mpr ⟨h, rfl⟩]; simp)
  · intro h
    by_contra hn
    have := R.get n
    rw [List.getElem?_eq_none (Nat.le_of_not_lt hn)] at this
    exact absurd this.symm (by
      rw [List.getElem?_eq_some_iff.mpr ⟨h, rfl⟩]; simp)

/-- Transport a relabelling along a write to the scheduled slot. -/
def set (R : Relabel N M) (i : Nat) (x : PThread α) :
    Relabel (N.set i x) (M.set (R.fwd i) x) where
  fwd := R.fwd
  bwd := R.bwd
  bwd_fwd := R.bwd_fwd
  fwd_bwd := R.fwd_bwd
  len := by simp only [List.length_set, R.len]
  get := by
    intro n
    by_cases h : n = i
    · subst h
      rw [List.getElem?_set, List.getElem?_set, if_pos rfl, if_pos rfl]
      by_cases hn : n < N.length
      · rw [if_pos hn, if_pos ((R.lt_iff n).mpr hn)]
      · rw [if_neg hn, if_neg (fun hc => hn ((R.lt_iff n).mp hc))]
    · rw [List.getElem?_set_ne (fun hc => h (R.fwd_inj hc).symm),
          List.getElem?_set_ne (fun hc => h hc.symm)]
      exact R.get n
  fix := by
    intro n hn
    exact R.fix n (by simpa only [List.length_set] using hn)

/-- Transport a relabelling along `fork`'s fresh slot. -/
def snoc (R : Relabel N M) (w : PThread α) : Relabel (N ++ [w]) (M ++ [w]) where
  fwd := R.fwd
  bwd := R.bwd
  bwd_fwd := R.bwd_fwd
  fwd_bwd := R.fwd_bwd
  len := by simp only [List.length_append, R.len]
  get := by
    intro n
    by_cases h : n < N.length
    · rw [List.getElem?_append_left ((R.lt_iff n).mpr h |>.trans_le (Nat.le_refl _)),
          List.getElem?_append_left h]
      exact R.get n
    · have hn : N.length ≤ n := Nat.le_of_not_lt h
      rw [R.fix n hn]
      rw [List.getElem?_append_right (by rw [R.len]; exact hn),
          List.getElem?_append_right hn, R.len]
  fix := by
    intro n hn
    exact R.fix n (Nat.le_trans (by simp) hn)

end Relabel

/-- The renumbering that moves a fragment's last slot forward past a suffix: the
`(L₁ ++ [z]) ++ L₂` numbering, read in the `(L₁ ++ L₂) ++ [z]` numbering. -/
private def unrotIdx (n₁ n₂ : Nat) (i : Nat) : Nat :=
  if i < n₁ then i else if i = n₁ then n₁ + n₂ else if i ≤ n₁ + n₂ then i - 1 else i

/-- The inverse renumbering. -/
private def rotIdx (n₁ n₂ : Nat) (m : Nat) : Nat :=
  if m < n₁ then m else if m < n₁ + n₂ then m + 1 else if m = n₁ + n₂ then n₁ else m

private theorem rot_unrot (n₁ n₂ n : Nat) : rotIdx n₁ n₂ (unrotIdx n₁ n₂ n) = n := by
  unfold unrotIdx rotIdx
  split_ifs <;> grind

private theorem unrot_rot (n₁ n₂ m : Nat) : unrotIdx n₁ n₂ (rotIdx n₁ n₂ m) = m := by
  unfold unrotIdx rotIdx
  split_ifs <;> grind

/-- The relabelling that moves a fragment's last slot forward past a suffix. -/
private def rotRelabel (L₁ L₂ : List (PThread α)) (z : PThread α) :
    Relabel ((L₁ ++ [z]) ++ L₂) ((L₁ ++ L₂) ++ [z]) where
  fwd := unrotIdx L₁.length L₂.length
  bwd := rotIdx L₁.length L₂.length
  bwd_fwd n := rot_unrot _ _ n
  fwd_bwd n := unrot_rot _ _ n
  len := by simp only [List.length_append, List.length_cons, List.length_nil]; grind
  get := by
    intro n
    simp only [List.getElem?_append, List.length_append, List.length_cons, List.length_nil,
      unrotIdx]
    split_ifs <;> grind
  fix := by
    intro n hn
    simp only [List.length_append, List.length_cons, List.length_nil] at hn
    unfold unrotIdx
    split_ifs <;> grind

/-! ### Relabelling a fragment

`Relabel` never mentions the lock, so it transports to `TPf` unchanged; only the
lock's *location* has to be carried along, through `Option.map R.fwd`. This is
the form `TPf_app`'s `fork` case needs, since `FragStep.fork` appends the fresh
slot at the end of the fragment while the merge wants it after the left half. -/

/-- **Every `FragStep` of a relabelled fragment is a `FragStep` of the original.**

The witness is always the same bijection — `set`
transports it across the write to the scheduled slot, `snoc` across `fork`'s
fresh slot — and the lock's new location corresponds through `Option.map`. The
releases are the easy cases: both sides land at `none`. -/
private theorem fragStep_relabel {N M : List (PThread α)} (R : Relabel N M)
    {i : Nat} {σ σ' : RustHeap.{0}} {r : Frag α}
    (h : FragStep M (R.fwd i) σ r σ') :
    ∃ (N' : List (PThread α)) (c : Option Nat) (R' : Relabel N' r.1),
      FragStep N i σ (N', c) σ' ∧ r.2 = Option.map R'.fwd c := by
  have hfoc : fragFocus M (R.fwd i) = fragFocus N i := by
    simp only [fragFocus, R.get i]
  cases h
  case tick k hf =>
    exact ⟨N.set i (some (k PUnit.unit)), some i, R.set i (some (k PUnit.unit)),
      .tick (hfoc ▸ hf), rfl⟩
  case heap f k hf hfσ =>
    exact ⟨N.set i (some (k σ)), some i, R.set i (some (k σ)),
      .heap (hfoc ▸ hf) hfσ, rfl⟩
  case fork k hf =>
    exact ⟨N.set i (some (k Aeneas.Std.ConcE.Tags.cur))
             ++ [some (k Aeneas.Std.ConcE.Tags.new)], some i,
      (R.set i (some (k Aeneas.Std.ConcE.Tags.cur))).snoc
        (some (k Aeneas.Std.ConcE.Tags.new)),
      .fork (hfoc ▸ hf), rfl⟩
  case releaseYield k hf =>
    exact ⟨N.set i (some (k PUnit.unit)), none, R.set i (some (k PUnit.unit)),
      .releaseYield (hfoc ▸ hf), rfl⟩
  case releaseEnd k hf =>
    exact ⟨N.set i none, none, R.set i none, .releaseEnd (hfoc ▸ hf), rfl⟩

private def permfMotive (q : LeibnizO (Frag α)) : IProp GF :=
  iprop(∀ (M : List (PThread α)) (R : Relabel q.car.1 M),
          TPf (M, Option.map R.fwd q.car.2))

private theorem permfMotive_elim {N M : List (PThread α)} (R : Relabel N M)
    (c : Option Nat) :
    permfMotive (GF := GF) ⟨((N, c) : Frag α)⟩ ⊢ TPf (M, Option.map R.fwd c) :=
  (BI.forall_elim M).trans (BI.forall_elim R)

/-- `permfMotive_elim` with the lock's new location supplied by an equation and
the conclusion left unfolded, to match what `least_fixpoint_unfold_mpr` wants. -/
private theorem permfMotive_elim' {N : List (PThread α)} {c : Option Nat} {r : Frag α}
    (R' : Relabel N r.1) (h : r.2 = Option.map R'.fwd c) :
    permfMotive (GF := GF) ⟨((N, c) : Frag α)⟩
      ⊢ Iris.bi_least_fixpoint (tpfPre (GF := GF) (α := α)) ⟨r⟩ := by
  refine .trans (permfMotive_elim R' c) ?_
  rw [← h]
  exact .rfl

private theorem tpfPre_permfMotive (q : LeibnizO (Frag α)) :
    tpfPre (permfMotive (GF := GF)) q ⊢ permfMotive (GF := GF) q := by
  refine BI.forall_intro fun M => BI.forall_intro fun R => ?_
  rcases hc : q.car.2 with _ | i
  · -- parked: the lock may arrive at any live slot of `M`, i.e. at `R.bwd` of it in `N`
    simp only [Option.map_none]
    refine .trans ?_ (Iris.least_fixpoint_unfold_mpr (tpfPre (GF := GF) (α := α))
      (x := ⟨((M, none) : Frag α)⟩))
    simp only [tpfPre, hc]
    refine BI.forall_intro fun j => BI.imp_intro ?_
    refine BI.pure_elim _ BI.and_elim_r fun hal => BI.and_elim_l.trans ?_
    have hal' : fragAlive q.car.1 (R.bwd j) := by
      obtain ⟨t, ht⟩ := hal
      refine ⟨t, ?_⟩
      have hg : M[R.fwd (R.bwd j)]? = q.car.1[R.bwd j]? := R.get (R.bwd j)
      rw [R.fwd_bwd] at hg
      exact hg.symm.trans ht
    refine .trans (forall_imp_elim
      (P := fun j => iprop(|={⊤, ∅}=>
        permfMotive (GF := GF) ⟨((q.car.1, some j) : Frag α)⟩)) (R.bwd j) hal') ?_
    exact BIFUpdate.mono (permfMotive_elim' (r := ((M, some j) : Frag α)) R
      (by simp only [R.fwd_bwd, Option.map_some]))
  · -- running: replay each `FragStep` of `M` on `N`
    simp only [Option.map_some]
    refine .trans ?_ (Iris.least_fixpoint_unfold_mpr (tpfPre (GF := GF) (α := α))
      (x := ⟨((M, some (R.fwd i)) : Frag α)⟩))
    simp only [tpfPre, hc]
    refine BI.forall_intro fun σ => BI.forall_intro fun r => BI.forall_intro fun σ' =>
      BI.imp_intro ?_
    refine BI.pure_elim _ BI.and_elim_r fun hstep => BI.and_elim_l.trans ?_
    obtain ⟨N', c, R', hstep₀, hcur⟩ := fragStep_relabel R hstep
    have hmask : curMask r.2 = curMask c := by
      cases c <;> simp only [hcur, Option.map_none, Option.map_some, curMask]
    rw [hmask]
    iintro H Hheap
    ihave H := BI.entails_wand (forall3_imp_elim
      (P := fun σ q σ' => iprop(heapInterp σ -∗ |={∅, curMask q.2}=>
        heapInterp σ' ∗ permfMotive (GF := GF) ⟨q⟩))
      σ ((N', c) : Frag α) σ' hstep₀) $$ H
    imod H $$ Hheap with ⟨Hh, HT⟩
    imodintro
    iframe Hh
    ihave HT := BI.entails_wand (permfMotive_elim' R' hcur) $$ HT
    iexact HT

/-- **`TPf` is invariant under any relabelling of the fragment's slots**, the
lock moving with them. Iris's `twptp_permutation`, at the fragment index. -/
private theorem TPf_perm {N M : List (PThread α)} (R : Relabel N M) (c : Option Nat) :
    TPf (GF := GF) (N, c) ⊢ TPf (M, Option.map R.fwd c) := by
  letI : OFE.NonExpansive (permfMotive (GF := GF) (α := α)) := leibnizO_ne (GF := GF)
  refine .trans ?_ (permfMotive_elim R c)
  show Iris.bi_least_fixpoint (tpfPre (GF := GF) (α := α)) ⟨((N, c) : Frag α)⟩ ⊢ _
  iintro Hfix
  iapply (Iris.least_fixpoint_iter (F := tpfPre (GF := GF) (α := α)) (Φ := permfMotive))
    $$ [] %(⟨((N, c) : Frag α)⟩ : LeibnizO (Frag α)) Hfix
  iintro !> %p HF
  iapply (BI.entails_wand (tpfPre_permfMotive p)) $$ HF

/-- **`TPf` is invariant under moving the fragment's last slot forward past a
suffix.** The form `TPf_app`'s `fork` case needs. -/
private theorem TPf_rot (L₁ L₂ : List (PThread α)) (z : PThread α) (c : Option Nat) :
    TPf (GF := GF) ((L₁ ++ [z]) ++ L₂, c)
      ⊢ TPf ((L₁ ++ L₂) ++ [z], Option.map (unrotIdx L₁.length L₂.length) c) :=
  TPf_perm (rotRelabel L₁ L₂ z) c

/-- `TPf_rot` at a lock that sits in the *left* half, where the renumbering is
the identity. This is the exact form `TPf_app`'s `fork` case needs. -/
private theorem TPf_rot_lt (L₁ L₂ : List (PThread α)) (z : PThread α) (i : Nat)
    (h : i < L₁.length) :
    TPf (GF := GF) ((L₁ ++ [z]) ++ L₂, some i)
      ⊢ TPf ((L₁ ++ L₂) ++ [z], some i) := by
  have hu : Option.map (unrotIdx L₁.length L₂.length) (some i) = some i := by
    simp only [Option.map_some, unrotIdx, if_pos h]
  have hrot := TPf_rot (GF := GF) L₁ L₂ z (some i)
  rwa [hu] at hrot

/-! ### The merge

#### Index bookkeeping

`fragFocus`, `fragAlive` and `List.set` on a concatenation, split by which half
the index lands in. Only the *left* half needs a side condition: an index at or
beyond `|L₁|` reads out of `L₂` on both sides, and one at or beyond `|L₁| + |L₂|`
is out of range on both sides. -/

private theorem fragFocus_append_left {L₁ L₂ : List (PThread α)} {i : Nat}
    (h : i < L₁.length) : fragFocus (L₁ ++ L₂) i = fragFocus L₁ i := by
  simp only [fragFocus, List.getElem?_append_left h]

private theorem fragFocus_append_add (L₁ L₂ : List (PThread α)) (j : Nat) :
    fragFocus (L₁ ++ L₂) (L₁.length + j) = fragFocus L₂ j := by
  simp only [fragFocus, List.getElem?_append_right (Nat.le_add_right _ _),
    Nat.add_sub_cancel_left]

private theorem fragAlive_append_left {L₁ L₂ : List (PThread α)} {j : Nat}
    (h : j < L₁.length) (ha : fragAlive (L₁ ++ L₂) j) : fragAlive L₁ j := by
  obtain ⟨t, ht⟩ := ha
  exact ⟨t, by rwa [List.getElem?_append_left h] at ht⟩

private theorem fragAlive_append_add {L₁ L₂ : List (PThread α)} {j : Nat}
    (ha : fragAlive (L₁ ++ L₂) (L₁.length + j)) : fragAlive L₂ j := by
  obtain ⟨t, ht⟩ := ha
  refine ⟨t, ?_⟩
  rwa [List.getElem?_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left] at ht

private theorem set_append_add (L₁ L₂ : List (PThread α)) (j : Nat) (x : PThread α) :
    (L₁ ++ L₂).set (L₁.length + j) x = L₁ ++ L₂.set j x := by
  rw [List.set_append_right _ _ (Nat.le_add_right _ _), Nat.add_sub_cancel_left]

/-- The `i < |L₁|` side condition, transported across `fork`'s fresh slot. -/
private theorem lock_lt_snoc (L : List (PThread α)) (i : Nat) (x z : PThread α)
    (h : i < L.length) :
    ∀ i', (some i : Option Nat) = some i' → i' < (L.set i x ++ [z]).length := by
  intro i' h'
  simp only [Option.some.injEq] at h'
  subst h'
  simp only [List.length_append, List.length_set, List.length_cons, List.length_nil]
  grind

/-- A parked fragment has no lock, so the side condition is vacuous. -/
private theorem lock_lt_none (L : List (PThread α)) :
    ∀ i, (none : Option Nat) = some i → i < L.length := by
  intro i h
  exact absurd h (by simp)

/-- `curMask` at a *concrete* successor. Stated on an explicit pair so that
rewriting with it leaves the still-quantified `curMask q.2` of the induction
hypotheses alone — `simp only [curMask]` would unfold those too and stop them
matching `tpf_run_int` / `tpf_run_rel`. -/
private theorem curMask_some (L : List (PThread α)) (i : Nat) :
    curMask ((L, some i) : Frag α).2 = ∅ := rfl

private theorem curMask_none (L : List (PThread α)) :
    curMask ((L, none) : Frag α).2 = (⊤ : CoPset) := rfl

/-- `TPf` is the fixpoint, unfolded to the form `least_fixpoint_unfold_mpr`
produces. -/
private theorem TPf_unfold (p : Frag α) :
    TPf (GF := GF) p ⊢ Iris.bi_least_fixpoint (tpfPre (GF := GF) (α := α)) ⟨p⟩ := .rfl

/-! #### Recovering the fixpoint from a strengthened induction hypothesis

`least_fixpoint_ind` hands out `Φ ∧ TPf` at each successor, so the *hypothesis*
it gives at a parked fragment still contains a full `TPf` of that fragment. This
is what lets the outer half of the merge use `TPf (L₂, none)` even though the
inner induction has already consumed it — Iris's `twptp_app` uses the same
strengthening. -/

private theorem tpfPre_parked_TPf (F : LeibnizO (Frag α) → IProp GF)
    (h : ∀ x, F x ⊢ Iris.bi_least_fixpoint (tpfPre (GF := GF) (α := α)) x)
    (L : List (PThread α)) :
    iprop(∀ j : Nat, ⌜fragAlive L j⌝ → |={⊤, ∅}=> F ⟨((L, some j) : Frag α)⟩)
      ⊢ TPf (GF := GF) (L, none) :=
  (BI.forall_mono fun _ => BI.imp_mono_right (BIFUpdate.mono (h _))).trans
    (Iris.least_fixpoint_unfold_mpr (tpfPre (GF := GF) (α := α))
      (x := ⟨((L, none) : Frag α)⟩))

/-! #### The two motives

The outer induction runs on `TPf (L₁, c₁)` with the right fragment still
universally quantified; the inner one runs on `TPf (L₂, c₂)` with `L₁`, `c₁` and
the outer induction hypothesis fixed. Both side conditions travel in the motive:
`hc` because the merged fragment has one lock, and `i < |L₁|` because
`joinCur _ (some i) none = some i` reads that index in the *merged* pool. -/

/-- The **outer** induction motive. -/
private def appMotive (p : LeibnizO (Frag α)) : IProp GF :=
  iprop(∀ (L₂ : List (PThread α)) (c₂ : Option Nat),
          ⌜(p.car.2 = none ∨ c₂ = none) ∧
            ∀ i, p.car.2 = some i → i < p.car.1.length⌝ →
          TPf (L₂, c₂) -∗ TPf (p.car.1 ++ L₂, joinCur p.car.1.length p.car.2 c₂))

private theorem appMotive_elim (L₁ L₂ : List (PThread α)) (c₁ c₂ : Option Nat)
    (h : (c₁ = none ∨ c₂ = none) ∧ ∀ i, c₁ = some i → i < L₁.length) :
    appMotive (GF := GF) ⟨((L₁, c₁) : Frag α)⟩
      ⊢ iprop(TPf (L₂, c₂) -∗ TPf (L₁ ++ L₂, joinCur L₁.length c₁ c₂)) :=
  ((BI.forall_elim L₂).trans (BI.forall_elim c₂)).trans
    (BI.imp_mp .rfl (BI.pure_intro h))

/-- `appMotive_elim` with `joinCur` already reduced, at a left fragment that
holds the lock. -/
private theorem appMotive_elim_run (L₁ L₂ : List (PThread α)) (i : Nat)
    (h : i < L₁.length) :
    appMotive (GF := GF) ⟨((L₁, some i) : Frag α)⟩
      ⊢ iprop(TPf (L₂, none) -∗ TPf (L₁ ++ L₂, some i)) :=
  appMotive_elim L₁ L₂ (some i) none ⟨Or.inr rfl, fun _ h' => by
    simp only [Option.some.injEq] at h'; subst h'; exact h⟩

/-- The same, at a left fragment that has released the lock. -/
private theorem appMotive_elim_rel (L₁ L₂ : List (PThread α)) :
    appMotive (GF := GF) ⟨((L₁, none) : Frag α)⟩
      ⊢ iprop(TPf (L₂, none) -∗ TPf (L₁ ++ L₂, none)) :=
  appMotive_elim L₁ L₂ none none ⟨Or.inl rfl, lock_lt_none L₁⟩

/-- The **inner** induction motive: `L₁`, `c₁` and the outer induction
hypothesis are fixed; only the right fragment moves. -/
private def appMotive2 (L₁ : List (PThread α)) (c₁ : Option Nat)
    (q : LeibnizO (Frag α)) : IProp GF :=
  iprop(⌜(c₁ = none ∨ q.car.2 = none) ∧ ∀ i, c₁ = some i → i < L₁.length⌝ →
        tpfPre (appMotive (GF := GF)) ⟨((L₁, c₁) : Frag α)⟩ -∗
          TPf (L₁ ++ q.car.1, joinCur L₁.length c₁ q.car.2))

/-- `appMotive2` at a right fragment that holds the lock; the merged index is
`|L₁| + j`. -/
private theorem appMotive2_elim_run (L₁ L₂ : List (PThread α)) (j : Nat) :
    appMotive2 (GF := GF) L₁ none ⟨((L₂, some j) : Frag α)⟩
      ⊢ iprop((∀ j' : Nat, ⌜fragAlive L₁ j'⌝ → |={⊤, ∅}=>
                appMotive (GF := GF) ⟨((L₁, some j') : Frag α)⟩) -∗
              TPf (L₁ ++ L₂, some (L₁.length + j))) :=
  BI.imp_mp .rfl (BI.pure_intro ⟨Or.inl rfl, lock_lt_none L₁⟩)

/-- `appMotive2` at a right fragment that has released the lock. -/
private theorem appMotive2_elim_rel (L₁ L₂ : List (PThread α)) :
    appMotive2 (GF := GF) L₁ none ⟨((L₂, none) : Frag α)⟩
      ⊢ iprop((∀ j' : Nat, ⌜fragAlive L₁ j'⌝ → |={⊤, ∅}=>
                appMotive (GF := GF) ⟨((L₁, some j') : Frag α)⟩) -∗
              TPf (L₁ ++ L₂, none)) :=
  BI.imp_mp .rfl (BI.pure_intro ⟨Or.inl rfl, lock_lt_none L₁⟩)

/-- Introducing the inner motive without unfolding it: `simp only [appMotive2]`
would also rewrite the copies buried in the induction hypothesis. -/
private theorem appMotive2_intro (L₁ L₂ : List (PThread α)) (c₁ c₂ : Option Nat)
    (P : IProp GF)
    (h : ((c₁ = none ∨ c₂ = none) ∧ ∀ i, c₁ = some i → i < L₁.length) →
      (P ⊢ iprop(tpfPre (appMotive (GF := GF)) ⟨((L₁, c₁) : Frag α)⟩ -∗
        TPf (L₁ ++ L₂, joinCur L₁.length c₁ c₂)))) :
    P ⊢ appMotive2 (GF := GF) L₁ c₁ ⟨((L₂, c₂) : Frag α)⟩ :=
  BI.imp_intro (BI.pure_elim _ BI.and_elim_r fun hcond => BI.and_elim_l.trans (h hcond))

/-- **The body of the nested induction.**

`q` is the right fragment, `L₁`/`c₁` the left one; the hypothesis is the
*strengthened* inner induction hypothesis of `least_fixpoint_ind`, and the
conclusion is the inner motive. Three cases, by which side holds the lock. -/
private theorem tpfPre_appMotive2 (L₁ : List (PThread α)) (c₁ : Option Nat)
    (q : LeibnizO (Frag α)) :
    tpfPre (fun x => iprop(appMotive2 (GF := GF) L₁ c₁ x ∧
        Iris.bi_least_fixpoint (tpfPre (GF := GF) (α := α)) x)) q
      ⊢ appMotive2 L₁ c₁ q := by
  obtain ⟨⟨L₂, c₂⟩⟩ := q
  refine appMotive2_intro L₁ L₂ c₁ c₂ _ ?_
  rintro ⟨hc, hi⟩
  rcases c₁ with _ | i
  · rcases c₂ with _ | j
    · /- **Case C**: neither side holds the lock, so the merged fragment is
         parked and must serve *every* live slot. `j < |L₁|` is the left half's
         own acquire, covered by the outer induction hypothesis; `j ≥ |L₁|` is
         the right half's, and is exactly why the induction has to be nested. -/
      refine .trans ?_ (BI.wand_mono_right (Iris.least_fixpoint_unfold_mpr
        (tpfPre (GF := GF) (α := α)) (x := ⟨((L₁ ++ L₂, none) : Frag α)⟩)))
      simp only [tpfPre]
      refine BI.wand_intro_left ?_
      refine BI.forall_intro fun j => BI.imp_intro ?_
      refine BI.pure_elim _ BI.and_elim_r fun hal => BI.and_elim_l.trans ?_
      by_cases hj : j < L₁.length
      · iintro ⟨HA, HB⟩
        ihave HB := BI.entails_wand (tpfPre_parked_TPf
          (fun x => iprop(appMotive2 (GF := GF) L₁ none x ∧
            Iris.bi_least_fixpoint (tpfPre (GF := GF) (α := α)) x))
          (fun _ => BI.and_elim_r) L₂) $$ HB
        ihave HA := BI.entails_wand (forall_imp_elim
          (P := fun j' => iprop(|={⊤, ∅}=> appMotive (GF := GF) ⟨((L₁, some j') : Frag α)⟩))
          j (fragAlive_append_left hj hal)) $$ HA
        imod HA with HA
        ihave HA := BI.entails_wand (appMotive_elim_run L₁ L₂ j hj) $$ HA HB
        ihave HA := BI.entails_wand (TPf_unfold ((L₁ ++ L₂, some j) : Frag α)) $$ HA
        imodintro
        iexact HA
      · obtain ⟨j', rfl⟩ : ∃ j', j = L₁.length + j' := ⟨j - L₁.length, by grind⟩
        iintro ⟨HA, HB⟩
        ihave HB := BI.entails_wand (forall_imp_elim
          (P := fun j'' => iprop(|={⊤, ∅}=>
            (appMotive2 (GF := GF) L₁ none ⟨((L₂, some j'') : Frag α)⟩ ∧
              Iris.bi_least_fixpoint (tpfPre (GF := GF) (α := α))
                ⟨((L₂, some j'') : Frag α)⟩)))
          j' (fragAlive_append_add hal)) $$ HB
        imod HB with HB
        icases HB with ⟨HB, -⟩
        ihave HB := BI.entails_wand (appMotive2_elim_run L₁ L₂ j') $$ HB HA
        ihave HB := BI.entails_wand
          (TPf_unfold ((L₁ ++ L₂, some (L₁.length + j')) : Frag α)) $$ HB
        imodintro
        iexact HB
    · /- **Case B**: the right fragment holds the lock, at `j`. Every `FragStep`
         of the merged pool at `|L₁| + j` is one of `L₂` at `j`, and `fork` needs
         no rotation: the fresh slot is already last on both sides. -/
      refine .trans ?_ (BI.wand_mono_right (Iris.least_fixpoint_unfold_mpr
        (tpfPre (GF := GF) (α := α))
        (x := ⟨((L₁ ++ L₂, some (L₁.length + j)) : Frag α)⟩)))
      simp only [tpfPre]
      refine BI.wand_intro_left ?_
      refine BI.forall_intro fun σ => BI.forall_intro fun r => BI.forall_intro fun σ' =>
        BI.imp_intro ?_
      refine BI.pure_elim _ BI.and_elim_r fun hstep => BI.and_elim_l.trans ?_
      cases hstep
      case tick k hf =>
        have hf₂ : fragFocus L₂ j = some (Result.vis stepEv k) :=
          (fragFocus_append_add L₁ L₂ j) ▸ hf
        rw [set_append_add, curMask_some]
        iintro ⟨HA, HB⟩ Hheap
        ihave HB := BI.entails_wand (tpf_run_int
          (fun x => iprop(appMotive2 (GF := GF) L₁ none x ∧
            Iris.bi_least_fixpoint (tpfPre (GF := GF) (α := α)) x))
          (FragStep.tick (L := L₂) (i := j) (σ := σ) hf₂)) $$ HB
        imod HB $$ Hheap with ⟨Hh, HΨ⟩
        icases HΨ with ⟨HΨ, -⟩
        ihave HΨ := BI.entails_wand
          (appMotive2_elim_run L₁ (L₂.set j (some (k PUnit.unit))) j) $$ HΨ HA
        ihave HΨ := BI.entails_wand (TPf_unfold
          ((L₁ ++ L₂.set j (some (k PUnit.unit)), some (L₁.length + j)) : Frag α)) $$ HΨ
        imodintro
        iframe Hh
        iexact HΨ
      case heap f k hf hfσ =>
        have hf₂ : fragFocus L₂ j = some (Result.vis (modifyEv f) k) :=
          (fragFocus_append_add L₁ L₂ j) ▸ hf
        rw [set_append_add, curMask_some]
        iintro ⟨HA, HB⟩ Hheap
        ihave HB := BI.entails_wand (tpf_run_int
          (fun x => iprop(appMotive2 (GF := GF) L₁ none x ∧
            Iris.bi_least_fixpoint (tpfPre (GF := GF) (α := α)) x))
          (FragStep.heap (L := L₂) (i := j) (σ := σ) hf₂ hfσ)) $$ HB
        imod HB $$ Hheap with ⟨Hh, HΨ⟩
        icases HΨ with ⟨HΨ, -⟩
        ihave HΨ := BI.entails_wand
          (appMotive2_elim_run L₁ (L₂.set j (some (k σ))) j) $$ HΨ HA
        ihave HΨ := BI.entails_wand (TPf_unfold
          ((L₁ ++ L₂.set j (some (k σ)), some (L₁.length + j)) : Frag α)) $$ HΨ
        imodintro
        iframe Hh
        iexact HΨ
      case fork k hf =>
        have hf₂ : fragFocus L₂ j = some (Result.vis forkEv k) :=
          (fragFocus_append_add L₁ L₂ j) ▸ hf
        rw [set_append_add, List.append_assoc, curMask_some]
        iintro ⟨HA, HB⟩ Hheap
        ihave HB := BI.entails_wand (tpf_run_int
          (fun x => iprop(appMotive2 (GF := GF) L₁ none x ∧
            Iris.bi_least_fixpoint (tpfPre (GF := GF) (α := α)) x))
          (FragStep.fork (L := L₂) (i := j) (σ := σ) hf₂)) $$ HB
        imod HB $$ Hheap with ⟨Hh, HΨ⟩
        icases HΨ with ⟨HΨ, -⟩
        ihave HΨ := BI.entails_wand (appMotive2_elim_run L₁
          (L₂.set j (some (k Aeneas.Std.ConcE.Tags.cur))
            ++ [some (k Aeneas.Std.ConcE.Tags.new)]) j) $$ HΨ HA
        ihave HΨ := BI.entails_wand (TPf_unfold
          ((L₁ ++ (L₂.set j (some (k Aeneas.Std.ConcE.Tags.cur))
              ++ [some (k Aeneas.Std.ConcE.Tags.new)]),
            some (L₁.length + j)) : Frag α)) $$ HΨ
        imodintro
        iframe Hh
        iexact HΨ
      case releaseYield k hf =>
        have hf₂ : fragFocus L₂ j = some (Result.vis yieldEv k) :=
          (fragFocus_append_add L₁ L₂ j) ▸ hf
        rw [set_append_add, curMask_none]
        iintro ⟨HA, HB⟩ Hheap
        ihave HB := BI.entails_wand (tpf_run_rel
          (fun x => iprop(appMotive2 (GF := GF) L₁ none x ∧
            Iris.bi_least_fixpoint (tpfPre (GF := GF) (α := α)) x))
          (FragStep.releaseYield (L := L₂) (i := j) (σ := σ) hf₂)) $$ HB
        imod HB $$ Hheap with ⟨Hh, HΨ⟩
        icases HΨ with ⟨HΨ, -⟩
        ihave HΨ := BI.entails_wand
          (appMotive2_elim_rel L₁ (L₂.set j (some (k PUnit.unit)))) $$ HΨ HA
        ihave HΨ := BI.entails_wand (TPf_unfold
          ((L₁ ++ L₂.set j (some (k PUnit.unit)), none) : Frag α)) $$ HΨ
        imodintro
        iframe Hh
        iexact HΨ
      case releaseEnd k hf =>
        have hf₂ : fragFocus L₂ j = some (Result.vis endthreadEv k) :=
          (fragFocus_append_add L₁ L₂ j) ▸ hf
        rw [set_append_add, curMask_none]
        iintro ⟨HA, HB⟩ Hheap
        ihave HB := BI.entails_wand (tpf_run_rel
          (fun x => iprop(appMotive2 (GF := GF) L₁ none x ∧
            Iris.bi_least_fixpoint (tpfPre (GF := GF) (α := α)) x))
          (FragStep.releaseEnd (L := L₂) (i := j) (σ := σ) hf₂)) $$ HB
        imod HB $$ Hheap with ⟨Hh, HΨ⟩
        icases HΨ with ⟨HΨ, -⟩
        ihave HΨ := BI.entails_wand
          (appMotive2_elim_rel L₁ (L₂.set j none)) $$ HΨ HA
        ihave HΨ := BI.entails_wand (TPf_unfold
          ((L₁ ++ L₂.set j none, none) : Frag α)) $$ HΨ
        imodintro
        iframe Hh
        iexact HΨ
  · /- **Case A**: the left fragment holds the lock, at `i < |L₁|` — the side
       condition, without which `some i` would point into `L₂` after the merge.
       `fork` is the one case that rearranges: `FragStep.fork` puts the fresh
       slot last in `L₁`, the merge wants it last overall, and `TPf_rot` bridges
       the two. -/
    have hc2 : c₂ = none := by
      rcases hc with h | h
      · exact absurd h (by simp)
      · exact h
    subst hc2
    have hilt : i < L₁.length := hi i rfl
    refine .trans ?_ (BI.wand_mono_right (Iris.least_fixpoint_unfold_mpr
      (tpfPre (GF := GF) (α := α)) (x := ⟨((L₁ ++ L₂, some i) : Frag α)⟩)))
    simp only [tpfPre]
    refine BI.wand_intro_left ?_
    refine BI.forall_intro fun σ => BI.forall_intro fun r => BI.forall_intro fun σ' =>
      BI.imp_intro ?_
    refine BI.pure_elim _ BI.and_elim_r fun hstep => BI.and_elim_l.trans ?_
    cases hstep
    case tick k hf =>
      have hf₁ : fragFocus L₁ i = some (Result.vis stepEv k) :=
        (fragFocus_append_left hilt) ▸ hf
      rw [List.set_append_left i (some (k PUnit.unit)) hilt, curMask_some]
      iintro ⟨HA, HB⟩ Hheap
      ihave HB := BI.entails_wand (tpfPre_parked_TPf
        (fun x => iprop(appMotive2 (GF := GF) L₁ (some i) x ∧
          Iris.bi_least_fixpoint (tpfPre (GF := GF) (α := α)) x))
        (fun _ => BI.and_elim_r) L₂) $$ HB
      ihave HA := BI.entails_wand (tpf_run_int (appMotive (GF := GF))
        (FragStep.tick (L := L₁) (i := i) (σ := σ) hf₁)) $$ HA
      imod HA $$ Hheap with ⟨Hh, HΦ⟩
      ihave HΦ := BI.entails_wand (appMotive_elim_run
        (L₁.set i (some (k PUnit.unit))) L₂ i (by simpa using hilt)) $$ HΦ HB
      ihave HΦ := BI.entails_wand (TPf_unfold
        ((L₁.set i (some (k PUnit.unit)) ++ L₂, some i) : Frag α)) $$ HΦ
      imodintro
      iframe Hh
      iexact HΦ
    case heap f k hf hfσ =>
      have hf₁ : fragFocus L₁ i = some (Result.vis (modifyEv f) k) :=
        (fragFocus_append_left hilt) ▸ hf
      rw [List.set_append_left i (some (k σ)) hilt, curMask_some]
      iintro ⟨HA, HB⟩ Hheap
      ihave HB := BI.entails_wand (tpfPre_parked_TPf
        (fun x => iprop(appMotive2 (GF := GF) L₁ (some i) x ∧
          Iris.bi_least_fixpoint (tpfPre (GF := GF) (α := α)) x))
        (fun _ => BI.and_elim_r) L₂) $$ HB
      ihave HA := BI.entails_wand (tpf_run_int (appMotive (GF := GF))
        (FragStep.heap (L := L₁) (i := i) (σ := σ) hf₁ hfσ)) $$ HA
      imod HA $$ Hheap with ⟨Hh, HΦ⟩
      ihave HΦ := BI.entails_wand (appMotive_elim_run
        (L₁.set i (some (k σ))) L₂ i (by simpa using hilt)) $$ HΦ HB
      ihave HΦ := BI.entails_wand (TPf_unfold
        ((L₁.set i (some (k σ)) ++ L₂, some i) : Frag α)) $$ HΦ
      imodintro
      iframe Hh
      iexact HΦ
    case fork k hf =>
      have hf₁ : fragFocus L₁ i = some (Result.vis forkEv k) :=
        (fragFocus_append_left hilt) ▸ hf
      rw [List.set_append_left i (some (k Aeneas.Std.ConcE.Tags.cur)) hilt, curMask_some]
      iintro ⟨HA, HB⟩ Hheap
      ihave HB := BI.entails_wand (tpfPre_parked_TPf
        (fun x => iprop(appMotive2 (GF := GF) L₁ (some i) x ∧
          Iris.bi_least_fixpoint (tpfPre (GF := GF) (α := α)) x))
        (fun _ => BI.and_elim_r) L₂) $$ HB
      ihave HA := BI.entails_wand (tpf_run_int (appMotive (GF := GF))
        (FragStep.fork (L := L₁) (i := i) (σ := σ) hf₁)) $$ HA
      imod HA $$ Hheap with ⟨Hh, HΦ⟩
      ihave HΦ := BI.entails_wand (appMotive_elim_run
        (L₁.set i (some (k Aeneas.Std.ConcE.Tags.cur))
          ++ [some (k Aeneas.Std.ConcE.Tags.new)]) L₂ i
        (lock_lt_snoc L₁ i _ _ hilt i rfl)) $$ HΦ HB
      ihave HΦ := BI.entails_wand (TPf_rot_lt
        (L₁.set i (some (k Aeneas.Std.ConcE.Tags.cur))) L₂
        (some (k Aeneas.Std.ConcE.Tags.new)) i (by simpa using hilt)) $$ HΦ
      ihave HΦ := BI.entails_wand (TPf_unfold
        ((L₁.set i (some (k Aeneas.Std.ConcE.Tags.cur)) ++ L₂
          ++ [some (k Aeneas.Std.ConcE.Tags.new)], some i) : Frag α)) $$ HΦ
      imodintro
      iframe Hh
      iexact HΦ
    case releaseYield k hf =>
      have hf₁ : fragFocus L₁ i = some (Result.vis yieldEv k) :=
        (fragFocus_append_left hilt) ▸ hf
      rw [List.set_append_left i (some (k PUnit.unit)) hilt, curMask_none]
      iintro ⟨HA, HB⟩ Hheap
      ihave HB := BI.entails_wand (tpfPre_parked_TPf
        (fun x => iprop(appMotive2 (GF := GF) L₁ (some i) x ∧
          Iris.bi_least_fixpoint (tpfPre (GF := GF) (α := α)) x))
        (fun _ => BI.and_elim_r) L₂) $$ HB
      ihave HA := BI.entails_wand (tpf_run_rel (appMotive (GF := GF))
        (FragStep.releaseYield (L := L₁) (i := i) (σ := σ) hf₁)) $$ HA
      imod HA $$ Hheap with ⟨Hh, HΦ⟩
      ihave HΦ := BI.entails_wand
        (appMotive_elim_rel (L₁.set i (some (k PUnit.unit))) L₂) $$ HΦ HB
      ihave HΦ := BI.entails_wand (TPf_unfold
        ((L₁.set i (some (k PUnit.unit)) ++ L₂, none) : Frag α)) $$ HΦ
      imodintro
      iframe Hh
      iexact HΦ
    case releaseEnd k hf =>
      have hf₁ : fragFocus L₁ i = some (Result.vis endthreadEv k) :=
        (fragFocus_append_left hilt) ▸ hf
      rw [List.set_append_left i none hilt, curMask_none]
      iintro ⟨HA, HB⟩ Hheap
      ihave HB := BI.entails_wand (tpfPre_parked_TPf
        (fun x => iprop(appMotive2 (GF := GF) L₁ (some i) x ∧
          Iris.bi_least_fixpoint (tpfPre (GF := GF) (α := α)) x))
        (fun _ => BI.and_elim_r) L₂) $$ HB
      ihave HA := BI.entails_wand (tpf_run_rel (appMotive (GF := GF))
        (FragStep.releaseEnd (L := L₁) (i := i) (σ := σ) hf₁)) $$ HA
      imod HA $$ Hheap with ⟨Hh, HΦ⟩
      ihave HΦ := BI.entails_wand
        (appMotive_elim_rel (L₁.set i none) L₂) $$ HΦ HB
      ihave HΦ := BI.entails_wand (TPf_unfold
        ((L₁.set i none ++ L₂, none) : Frag α)) $$ HΦ
      imodintro
      iframe Hh
      iexact HΦ

private theorem appMotive2_of_TPf (L₁ : List (PThread α)) (c₁ : Option Nat)
    (L₂ : List (PThread α)) (c₂ : Option Nat) :
    TPf (GF := GF) (L₂, c₂) ⊢ appMotive2 L₁ c₁ ⟨((L₂, c₂) : Frag α)⟩ := by
  letI : OFE.NonExpansive (appMotive2 (GF := GF) (α := α) L₁ c₁) := leibnizO_ne (GF := GF)
  show Iris.bi_least_fixpoint (tpfPre (GF := GF) (α := α)) ⟨((L₂, c₂) : Frag α)⟩ ⊢ _
  iintro Hfix
  iapply (Iris.least_fixpoint_ind (F := tpfPre (GF := GF) (α := α))
      (Φ := appMotive2 L₁ c₁)) $$ [] %(⟨((L₂, c₂) : Frag α)⟩ : LeibnizO (Frag α)) Hfix
  iintro !> %y HF
  iapply (BI.entails_wand (tpfPre_appMotive2 L₁ c₁ y)) $$ HF

private theorem tpfPre_appMotive (p : LeibnizO (Frag α)) :
    tpfPre (appMotive (GF := GF)) p ⊢ appMotive (GF := GF) p := by
  obtain ⟨⟨L₁, c₁⟩⟩ := p
  simp only [appMotive]
  refine BI.forall_intro fun L₂ => BI.forall_intro fun c₂ => BI.imp_intro ?_
  refine BI.pure_elim _ BI.and_elim_r fun hcond => BI.and_elim_l.trans ?_
  iintro HA HB
  ihave HB := BI.entails_wand (appMotive2_of_TPf L₁ c₁ L₂ c₂) $$ HB
  iapply (BI.entails_wand (BI.imp_mp (P := appMotive2 (GF := GF) L₁ c₁
    ⟨((L₂, c₂) : Frag α)⟩) .rfl (BI.pure_intro hcond))) $$ HB HA

/-- **The merge, now symmetric.**

Nested induction, outer on the first fragment and inner on the second, exactly
as `twptp_app`. The cross terms — the ones the old `TP_app_l`/`TP_app_r` could
not express — are now steps of the fragment that owns the lock: `L₁` *releases*
(`some i → none`, covered by `L₁`'s own induction hypothesis) and `L₂` *acquires*
(`none → some j`, covered by `L₂`'s). `TPf_rot` handles `fork`'s rearrangement:
`FragStep.fork` appends the fresh slot at the end of the fragment, while the
merge wants it after the left half.

⚠️ `hi` is **not** bookkeeping: without it the statement is *false*, by the very
counterexample recorded above for `TP_app_l`. Take `L₁ = [some u]` with
`u = vis yield (fun _ => u)`, `L₂ = [some w]` with
`w = vis yield (fun _ => ret v)`, `c₁ = some 1`, `c₂ = none`. Then
`TPf (L₁, some 1)` holds by `tpf_stuck` (slot `1` is out of range) and
`TPf (L₂, none)` holds, but `joinCur 1 (some 1) none = some 1` now points at `w`
inside the *merged* pool, which releases to `[some u, some (ret v)]`, whose
parked branch must serve slot `0` — and `u` yields to itself forever. `TPf` is a
**least** fixpoint, so the merged claim fails. Every use of `TPf_app` supplies
`hi`, so nothing downstream is weakened. -/
private theorem TPf_app (L₁ L₂ : List (PThread α)) (c₁ c₂ : Option Nat)
    (hc : c₁ = none ∨ c₂ = none)
    (hi : ∀ i, c₁ = some i → i < L₁.length) :
    TPf (GF := GF) (L₁, c₁)
      ⊢ iprop(TPf (L₂, c₂) -∗ TPf (L₁ ++ L₂, joinCur L₁.length c₁ c₂)) := by
  letI : OFE.NonExpansive (appMotive (GF := GF) (α := α)) := leibnizO_ne (GF := GF)
  refine .trans ?_ (appMotive_elim L₁ L₂ c₁ c₂ ⟨hc, hi⟩)
  show Iris.bi_least_fixpoint (tpfPre (GF := GF) (α := α)) ⟨((L₁, c₁) : Frag α)⟩ ⊢ _
  iintro Hfix
  iapply (Iris.least_fixpoint_iter (F := tpfPre (GF := GF) (α := α)) (Φ := appMotive))
    $$ [] %(⟨((L₁, c₁) : Frag α)⟩ : LeibnizO (Frag α)) Hfix
  iintro !> %p HF
  iapply (BI.entails_wand (tpfPre_appMotive p)) $$ HF

/-! ### The glue, at the corrected index

Proved *from* `TPf_app` and `wpi_TPf`, so the decomposition is checked. -/

/-- The induction step of `wpi_TPf`, as a plain entailment so that the case
analysis can be done *outside* the proof mode.

The analysis is on the `FragStep`, not on the tree: `FragStep` has exactly five
rules and each of them pins the scheduled thread down to a `vis` node with a
known event. `ret`, `div` and `vis (fail e) k` therefore never appear as goals
at all — no `FragStep` fires on them, so the fixpoint's unfolding is vacuous.
(In particular `divOK .total = False` is *not* needed here: a diverging thread
takes no machine step, which is why silent divergence is excluded separately, by
`sysInv_not_diverging`.)

What is left is one goal per rule:

* `tick` / `heap` — `stepH`/`stateH` hand back the induction hypothesis at
  `k …`, and the fragment stays at `some 0`;
* `releaseYield` / `releaseEnd` — `ConcH` answers `🧱` / `🧾`, whose *first* half
  is the release. The fragment lands at `none`, and `TPf_park_singleton` (resp.
  `TPf_dead_singleton`) turns the remaining `|={⊤,∅}=>` back into the parked
  fixpoint;
* `fork` — `ConcH` answers `Ψ .cur ∗ B .new`, and `wpi_ind_emp` hands out an
  induction hypothesis for the `B` branch too, so the child arrives as
  `|={⊤,∅}=> TPf ([some (k .new)], some 0)`. `TPf_park_singleton` parks it and
  `TPf_app` merges, at `joinCur 1 (some 0) none = some 0`. -/
private theorem wpi_TPf_step (t : Result α) (Φ : Post GF α) :
    wpiAcc GF (Rust.rustH (GF := GF) .total) .total
        (fun p => iprop(TPf (GF := GF) ([some p.1.car], some 0) ∧
                        wpi GF (Rust.rustH (GF := GF) .total) .total p.1.car p.2))
        (⟨t⟩, Φ)
      ⊢ TPf (GF := GF) ([some t], some 0) := by
  refine .trans ?_ (Iris.least_fixpoint_unfold_mpr (tpfPre (GF := GF) (α := α))
    (x := ⟨(([some t], some 0) : Frag α)⟩))
  simp only [tpfPre]
  refine BI.forall_intro fun σ => BI.forall_intro fun q => BI.forall_intro fun σ' =>
    BI.imp_intro ?_
  refine BI.pure_elim _ BI.and_elim_r fun hstep => BI.and_elim_l.trans ?_
  cases hstep
  case tick k hf =>
    rw [fragFocus_singleton] at hf
    obtain rfl : t = Result.vis stepEv k := Option.some.inj hf
    rw [curMask_some]
    simp only [wpiAcc, Result.vis, unfold_vis, tRustH_step, List.set_cons_zero]
    refine .trans (BIFUpdate.mono BI.and_elim_l) ?_
    iintro HF Hheap
    imod HF with HF
    imodintro
    iframe Hheap
    ihave HF := BI.entails_wand
      (TPf_unfold (([some (k PUnit.unit)], some 0) : Frag α)) $$ HF
    iexact HF
  case heap f k hf hfσ =>
    rw [fragFocus_singleton] at hf
    obtain rfl : t = Result.vis (modifyEv f) k := Option.some.inj hf
    rw [curMask_some]
    simp only [wpiAcc, Result.vis, unfold_vis, tRustH_modify, List.set_cons_zero]
    refine .trans (BIFUpdate.mono (tRustH_modify_out hfσ
      (fun s => iprop(TPf (GF := GF) ([some (k s)], some 0) ∧
        wpi GF (Rust.rustH (GF := GF) .total) .total (k s) Φ)))) ?_
    iintro HF Hheap
    imod HF with HF
    imod HF $$ Hheap with ⟨Hh, HT⟩
    imodintro
    iframe Hh
    ihave HT := BI.entails_wand (BI.and_elim_l
      (P := TPf (GF := GF) ([some (k σ)], some 0))
      (Q := wpi GF (Rust.rustH (GF := GF) .total) .total (k σ) Φ)) $$ HT
    ihave HT := BI.entails_wand
      (TPf_unfold (([some (k σ)], some 0) : Frag α)) $$ HT
    iexact HT
  case fork k hf =>
    rw [fragFocus_singleton] at hf
    obtain rfl : t = Result.vis forkEv k := Option.some.inj hf
    rw [curMask_some]
    simp only [wpiAcc, Result.vis, unfold_vis, tRustH_fork, List.set_cons_zero]
    refine .trans (BIFUpdate.mono (BI.sep_mono BI.and_elim_l
      (BIFUpdate.mono BI.and_elim_l))) ?_
    refine .trans (BIFUpdate.mono (BI.sep_mono_right (TPf_park_singleton _))) ?_
    iintro HF Hheap
    imod HF with ⟨Hcur, Hnew⟩
    imodintro
    iframe Hheap
    ihave Hcur := BI.entails_wand
      (show TPf (GF := GF) ([some (k Aeneas.Std.ConcE.Tags.cur)], some 0)
          ⊢ iprop(TPf (GF := GF) ([some (k Aeneas.Std.ConcE.Tags.new)], none) -∗
                  TPf (GF := GF) ([some (k Aeneas.Std.ConcE.Tags.cur)]
                                    ++ [some (k Aeneas.Std.ConcE.Tags.new)], some 0))
          from TPf_app [some (k Aeneas.Std.ConcE.Tags.cur)]
            [some (k Aeneas.Std.ConcE.Tags.new)] (some 0) none (Or.inr rfl)
            (by intro i h; simp only [Option.some.injEq] at h; subst h; simp))
      $$ Hcur Hnew
    ihave Hcur := BI.entails_wand (TPf_unfold
      (([some (k Aeneas.Std.ConcE.Tags.cur)] ++ [some (k Aeneas.Std.ConcE.Tags.new)],
        some 0) : Frag α)) $$ Hcur
    iexact Hcur
  case releaseYield k hf =>
    rw [fragFocus_singleton] at hf
    obtain rfl : t = Result.vis yieldEv k := Option.some.inj hf
    rw [curMask_none]
    simp only [wpiAcc, Result.vis, unfold_vis, tRustH_yield, List.set_cons_zero]
    refine .trans (BIFUpdate.mono (BIFUpdate.mono (BIFUpdate.mono BI.and_elim_l))) ?_
    refine .trans (BIFUpdate.mono (BIFUpdate.mono (TPf_park_singleton _))) ?_
    iintro HF Hheap
    imod HF with HF
    imod HF with HF
    imodintro
    iframe Hheap
    ihave HF := BI.entails_wand
      (TPf_unfold (([some (k PUnit.unit)], none) : Frag α)) $$ HF
    iexact HF
  case releaseEnd k hf =>
    rw [fragFocus_singleton] at hf
    obtain rfl : t = Result.vis endthreadEv k := Option.some.inj hf
    rw [curMask_none]
    simp only [wpiAcc, Result.vis, unfold_vis, tRustH_endthread, List.set_cons_zero]
    iintro HF Hheap
    imod HF with HF
    imod HF with HT
    iclear HT
    imodintro
    iframe Hheap
    iapply (BI.entails_wand ((TPf_dead_singleton (GF := GF) (α := α)).trans
      (TPf_unfold ((([none] : List (PThread α)), none) : Frag α))))
    iempintro

/-- The motive is constant in the postcondition, so non-expansiveness is trivial.
This is the whole reason the postconditions were kept out of `Frag`. -/
private theorem tpfG_ne (t : Result α) :
    OFE.NonExpansive (fun _ : Post GF α => TPf (GF := GF) ([some t], some 0)) := by
  constructor
  intro _ _ _ _
  exact .rfl

/-- **A single thread, holding the big lock, cannot run forever.**

`wpi_ind_emp` at the motive `G t Ψ := TPf ([some t], some 0)` — constant in `Ψ`,
which is why the postconditions had to be kept out of the fixpoint's index: the
non-expansiveness obligation is then trivial. The step is `wpi_TPf_step`.

Stated first in the `∀`-form `wpi_ind_emp` produces, because the induction has
to be run *before* the tree and the postcondition are fixed. -/
private theorem wpi_TPf_all :
    iprop(emp) ⊢ iprop(∀ (t : Result α) (Ψ : Post GF α),
      wpi GF (Rust.rustH (GF := GF) .total) .total t Ψ -∗
      TPf (GF := GF) ([some t], some 0)) := by
  refine .trans ?_ (wpi_ind_emp (GF := GF) (H := Rust.rustH (GF := GF) .total)
    (m := .total) (fun t _ => TPf (GF := GF) ([some t], some 0)) tpfG_ne)
  refine .trans BI.intuitionistically_emp.mpr (BI.intuitionistically_mono ?_)
  refine BI.forall_intro fun t => BI.forall_intro fun Ψ => ?_
  iintro _Hemp HF
  iapply (BI.entails_wand (wpi_TPf_step t Ψ)) $$ HF

private theorem wpi_TPf (x : Result α × Post GF α) :
    runOb x ⊢ TPf (GF := GF) ([some x.1], some 0) :=
  BI.wand_entails (wpi_TPf_all.trans ((BI.forall_elim x.1).trans (BI.forall_elim x.2)))

private theorem TPf_singleton (x : OThread GF α) :
    parkOb x ⊢ TPf (GF := GF) ([x.tree], none) := by
  refine .trans ?_ (Iris.least_fixpoint_unfold_mpr (tpfPre (GF := GF) (α := α))
    (x := ⟨(([x.tree], none) : Frag α)⟩))
  simp only [tpfPre]
  refine BI.forall_intro fun j => BI.imp_intro ?_
  refine BI.pure_elim _ BI.and_elim_r fun hal => BI.and_elim_l.trans ?_
  obtain ⟨t, ht⟩ := hal
  rcases j with _ | j
  · cases x with
    | none => exact absurd ht (by simp [OThread.tree])
    | some y =>
      have hxt : ([OThread.tree (some y)] : List (PThread α)) = [some y.1] := rfl
      rw [hxt]
      simp only [parkOb]
      exact BIFUpdate.mono (wpi_TPf y)
  · exact absurd ht (by simp)

private theorem TPf_parked (M : List (OThread GF α)) :
    iprop([∗list] x ∈ M, parkOb x) ⊢ TPf (GF := GF) (M.map OThread.tree, none) := by
  induction M with
  | nil =>
    simp only [List.map_nil]
    refine .trans ?_ (Iris.least_fixpoint_unfold_mpr (tpfPre (GF := GF) (α := α))
      (x := ⟨(([], none) : Frag α)⟩))
    simp only [tpfPre]
    refine BI.forall_intro fun j => BI.imp_intro ?_
    exact BI.pure_elim _ BI.and_elim_r fun hal => absurd hal (by simp [fragAlive])
  | cons x xs ih =>
    simp only [List.map_cons]
    rw [show x.tree :: xs.map OThread.tree = [x.tree] ++ xs.map OThread.tree from rfl]
    refine .trans (BI.BigSepL.bigSepL_cons (Φ := fun _ (y : OThread GF α) => parkOb y)).mp ?_
    iintro ⟨Hx, Hxs⟩
    ihave Hx := BI.entails_wand (TPf_singleton x) $$ Hx
    ihave Hxs := BI.entails_wand ih $$ Hxs
    iapply (BI.entails_wand (show TPf (GF := GF) ([x.tree], none)
        ⊢ iprop(TPf (xs.map OThread.tree, none)
                -∗ TPf ([x.tree] ++ xs.map OThread.tree, none))
        from TPf_app [x.tree] (xs.map OThread.tree) none none (Or.inl rfl)
          (lock_lt_none _))) $$ Hx Hxs

/-- **The pool obligations give the fragment fixpoint.** The same split as
before — prefix, scheduled thread, suffix — but the two merges are now both
instances of the one symmetric `TPf_app`. -/
private theorem pool_TPf (L : List (OThread GF α)) (i : Nat) :
    iprop(oFocusObl L i ∗ [∗list] x ∈ L.set i none, parkOb x)
      ⊢ TPf (GF := GF) (L.map OThread.tree, some i) := by
  rcases hL : L[i]? with _ | y
  · have hst : fragFocus (L.map OThread.tree) i = none := by
      simp [fragFocus, List.getElem?_map, hL]
    exact BI.affine.trans (tpf_stuck hst)
  · cases y with
    | none =>
      have hst : fragFocus (L.map OThread.tree) i = none := by
        simp [fragFocus, List.getElem?_map, hL, OThread.tree]
      exact BI.affine.trans (tpf_stuck hst)
    | some x =>
      have hlt : i < L.length := (List.getElem?_eq_some_iff.mp hL).1
      have hget : L[i] = some x := (List.getElem?_eq_some_iff.mp hL).2
      have hsplit : L = L.take i ++ (some x :: L.drop (i + 1)) := by
        conv_lhs => rw [← List.take_append_drop i L]
        rw [List.drop_eq_getElem_cons hlt, hget]
      have hlen : (L.take i).length = i := by
        rw [List.length_take]; exact Nat.min_eq_left (Nat.le_of_lt hlt)
      have hset : L.set i none = L.take i ++ ((none : OThread GF α) :: L.drop (i + 1)) := by
        conv_lhs => rw [hsplit]
        rw [List.set_append_right i none (by rw [hlen]), hlen, Nat.sub_self,
          List.set_cons_zero]
      have hmap : L.map OThread.tree
          = (L.take i).map OThread.tree
              ++ ([some x.1] ++ (L.drop (i + 1)).map OThread.tree) := by
        conv_lhs => rw [hsplit]
        simp [OThread.tree]
      have hmaplen : ((L.take i).map OThread.tree).length = i := by
        rw [List.length_map, hlen]
      have hfoc : oFocusObl L i = runOb x := by simp only [oFocusObl, hL]
      rw [hmap, hset, hfoc]
      refine .trans ?_ (show TPf (GF := GF)
          ((L.take i).map OThread.tree ++ ([some x.1] ++ (L.drop (i + 1)).map OThread.tree),
            joinCur ((L.take i).map OThread.tree).length none (some 0))
          ⊢ TPf ((L.take i).map OThread.tree
                  ++ ([some x.1] ++ (L.drop (i + 1)).map OThread.tree), some i)
          from by simp only [joinCur, Nat.add_zero, hmaplen]; exact .rfl)
      refine .trans (BI.sep_mono_right
        (BI.BigSepL.bigSepL_append (Φ := fun _ (y : OThread GF α) => parkOb y)).mp) ?_
      refine .trans (BI.sep_mono_right (BI.sep_mono_right
        (BI.BigSepL.bigSepL_cons (Φ := fun _ (y : OThread GF α) => parkOb y)).mp)) ?_
      iintro ⟨Hrun, Hpre, Hnone, Hrest⟩
      iclear Hnone
      ihave Hrun := BI.entails_wand (wpi_TPf x) $$ Hrun
      ihave Hpre := BI.entails_wand (TPf_parked (L.take i)) $$ Hpre
      ihave Hrest := BI.entails_wand (TPf_parked (L.drop (i + 1))) $$ Hrest
      ihave Hrun := BI.entails_wand (show TPf (GF := GF) ([some x.1], some 0)
          ⊢ iprop(TPf ((L.drop (i + 1)).map OThread.tree, none)
                  -∗ TPf ([some x.1] ++ (L.drop (i + 1)).map OThread.tree, some 0))
          from TPf_app [some x.1] ((L.drop (i + 1)).map OThread.tree) (some 0) none
            (Or.inr rfl) (by intro i' h'; simp only [Option.some.injEq] at h'; subst h'; simp))
        $$ Hrun Hrest
      iapply (BI.entails_wand (TPf_app ((L.take i).map OThread.tree)
        ([some x.1] ++ (L.drop (i + 1)).map OThread.tree) none (some 0)
        (Or.inl rfl) (lock_lt_none _))) $$ Hpre Hrun

/-! #### ⚠️ Why the index has `Option Nat` in it

The merge was first attempted as

    TP_app_l : TP (L₁, i) ⊢ TPall L₂ -∗ TP (L₁ ++ L₂, i)    (i < |L₁|)
    TP_app_r : TPall L₁ ⊢ TP (L₂, j) -∗ TP (L₁ ++ L₂, |L₁| + j)

over the index `(threads, current)`. Both are *true* and neither is provable
there. That is what forced `Frag`; the argument is recorded here because it is
the justification for the whole fragment construction.

Two things went wrong. First, `TP_app_l` without `i < |L₁|` is outright
**false**: for `i ≥ |L₁|` the left half is stuck, so `TP (L₁, i)` holds from
`emp` by `tp_stuck`, while `TP (L₁ ++ L₂, i)` need not hold. Take

  `L₁ = [some u]` with `u = vis yield (fun _ => u)`,
  `L₂ = [some w]` with `w = vis yield (fun _ => ret v)`, and `i = 1`.

`TP (L₁, 1)` holds (index out of range) and `TPall L₂` holds (`w` yields once to
its only live slot and then returns), but in `L₁ ++ L₂` the thread `w` may yield
to slot `0`, and `u` then loops forever.

Second, and fatally:

proving `TP (L₁ ++ L₂, i)` by induction on `TP (L₁, i)`, the
combined pool may `yield` (or `endthread`) at `i ∈ L₁` to a slot `j ≥ |L₁|`,
moving the big lock into `L₂`. That transition is **not** a `PoolStep` of
`⟨L₁, i, σ⟩`: `PoolStep.yield` demands `Alive j` in the left half alone. So the
outer induction hypothesis cannot be invoked on it. This is the case Iris does
not have, because Iris's machine has no lock — a step of `t₁ ++ t₂` is always a
step of `t₁` or of `t₂`.

**Why it cannot be patched.** One *can* still invoke the hypothesis on the
L₁-step "yield to self" (`j := i`, which is alive after `setFocus`), getting the
induction hypothesis at `⟨(L₁'', i)⟩`. But when the lock later comes back from
`L₂` it may land on any slot `j₁` of `L₁''`, and what is needed then is the
hypothesis at `⟨(L₁'', j₁)⟩`. Extracting it for every `j₁` at once is impossible:
`tpPre`'s successor quantifier is guarded by `heapInterp σ -∗ …`, and
`heapInterp` is linear — one use yields exactly one successor and hands the heap
straight back, so `∀ j₁, Ψ ⟨(L₁'', j₁)⟩` cannot be produced *alongside* the
`heapInterp` the goal must return. Fundamentally, `TP (L₁, i)` is a statement
about executions that **start** with the lock at `i`; it says nothing about "the
lock left and came back elsewhere".

**The fix, carried out above:** put the lock's location in the index —
`Frag α := List (PThread α) × Option Nat`, with `none` meaning the lock is
outside the fragment, and `FragStep` splitting `yield`/`endthread` into a
*release* (`some i → none`) matched by the *acquire* (`none → some j`) built
into `tpfPre`'s parked branch. `TPall L` then **is** `TPf (L, none)` rather than
a derived `∀`, and the merge becomes the symmetric `TPf_app`, whose cross terms
are "`L₁` releases while `L₂` acquires" — each a step of the fragment that owns
it, so the matching induction hypothesis applies. *Acquire* is not a decrease,
but it need not be: it is a sub-derivation of the fixpoint at `(L, none)`, and
the release paired with it consumes one `wpi` layer of the releasing thread —
which is precisely why the induction must be nested.

Nothing in `Machine.lean` or `PoolStep` changed: `FragStep` is a derived relation
on the same `PThread` lists, and `TPf_TP` puts the two `FragStep`s of a `yield`
back together into the one `PoolStep` that `SNInv` counts. `Relabel` never
mentions the lock, so it transported to `TPf` unchanged — see `fragStep_relabel`
and `TPf_perm`, with the lock's location carried by `Option.map R.fwd`. -/


/-- **The pool obligations give the pool fixpoint**, and hence `TP`. Proved from
`TPf_app` and `wpi_TPf` above, via `pool_TPf` and `TPf_TP`. -/
private theorem pool_TP (L : List (OThread GF α)) (i : Nat) :
    iprop(oFocusObl L i ∗ [∗list] x ∈ L.set i none, parkOb x)
      ⊢ TP (GF := GF) (L.map OThread.tree, i) :=
  (pool_TPf L i).trans (TPf_TP _ _)


private theorem sysInv_TP (Φ : α → IProp GF) (c : Config α) :
    SysInv .total Φ c ⊢ iprop(heapInterp c.heap ∗ TP (GF := GF) (treeView c).pool) := by
  refine (sysInv_pool Φ c).trans (BI.sep_mono_right ?_)
  refine .trans (pool_TP (oblView Φ c) c.current) ?_
  rw [oblView_tree]
  exact .rfl

private theorem sysInv_snInv (Φ : α → IProp GF) (c : Config α) :
    SysInv .total Φ c ⊢ SNInv (GF := GF) c :=
  (sysInv_TP Φ c).trans ((BI.sep_mono_right (tp_snInv c)).trans BI.wand_elim_right)

theorem sysInv_sn (Φ : α → IProp GF) (c : Config α) :
    SysInv .total Φ c ⊢ iprop(|={∅}=> ⌜SN c⌝) :=
  (sysInv_snInv Φ c).trans (snInv_sn c)

end

end AeneasIris.Semantics
