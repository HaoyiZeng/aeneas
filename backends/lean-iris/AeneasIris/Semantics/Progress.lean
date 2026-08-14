import AeneasIris.Semantics.Machine

/-!
# Progress: the machine never wedges

`Semantics/Machine.lean` fixes what may go wrong (`Config.Faulty`) and
`Semantics/Preservation.lean` shows the Iris invariant rules that out. Neither
says anything about a *fourth* possibility, which is invisible to both:

> the scheduled slot is out of range, or holds a tombstone.

No `Step` rule fires in that situation, and `Config.Faulty` does not mention it.
So a configuration in that state is a **silent dead end** — and `Safe t`, being
a statement about *all reachable* configurations, gets *weaker* as the reachable
set shrinks. `Safe` would therefore be satisfied by a machine that mysteriously
wedges on step three, and nothing in the development, up to and including
adequacy, would notice.

This file closes that hole, entirely in plain Lean — no Iris, and no dependency
on `Invariant.lean` or `Preservation.lean`.

* `Config.WF` is the missing invariant: the scheduled slot exists and is alive.
* `init_wf` / `Step.wf` / `Reaches.wf` establish it along every execution, so
  every reachable configuration has `c.focus = some t` for some `t`.
* `progress` then says a well-formed, non-faulty configuration either has
  **legitimately** stopped or **can take a step**. There is no fourth case.

Together with `Safe`, this upgrades "no reachable configuration faults" to the
statement one actually wants: *every* reachable configuration either halts for
one of three explicitly enumerated reasons, or steps.

## Note on `Step.wf`

`Step.wf` needs no well-formedness hypothesis on its *source*: every rule of
`Step` has `c.focus = some …` as a premise, which already implies `c.WF`. That
is recorded as `Step.wf_src`, and it means the step relation can neither start
from nor lead to an ill-formed configuration. `Config.WF` is consequently not so
much an invariant that has to be maintained as one that cannot be escaped; the
reason to state it anyway is `init`, and the fact that `progress` needs it as a
hypothesis in order to get its hands on a focus at all.
-/

namespace AeneasIris.Semantics

open Aeneas.Data.Coinductive
open Aeneas.Std (Result RustEffect RustHeap Error FailE ConcE StepE StateE)

unseal Aeneas.Std.Result

section

variable {α : Type}

/-! ## Reading and writing the scheduled slot -/

/-- `Config.focus` says exactly that the scheduled slot holds a live thread. -/
theorem Config.focus_eq_some {c : Config α} {t : Result α} :
    c.focus = some t ↔ c.threads[c.current]? = some (Thread.alive t) := by
  unfold Config.focus
  constructor
  · intro h
    split at h
    · rename_i heq
      simp only [Option.some.injEq] at h
      subst h
      exact heq
    · exact absurd h (by simp)
  · intro h; rw [h]

theorem Config.focus_lt {c : Config α} {t : Result α} (h : c.focus = some t) :
    c.current < c.threads.length :=
  (List.getElem?_eq_some_iff.mp (Config.focus_eq_some.mp h)).1

/-- Indexing a slot that was just written. -/
private theorem getElem?_set_self {L : List (Thread α)} {i : Nat} (a : Thread α)
    (hi : i < L.length) : (L.set i a)[i]? = some a := by
  simp [hi]

/-- Indexing the parent slot of a forked pool: appending a child cannot disturb
a prefix index. Stated over abstract `L`, `M`, `a` on purpose — rewriting with
`List.getElem?_append_left` *in situ* is rejected as not type-correct, because
`RustEffect.O forkEv` is not reducibly `ConcE.Tags`. -/
private theorem getElem?_set_append {L M : List (Thread α)} {i : Nat} (a : Thread α)
    (hi : i < L.length) : ((L.set i a) ++ M)[i]? = some a := by
  rw [List.getElem?_append_left (by simpa using hi)]
  simp [hi]

/-! ## Well-formedness -/

/-- **The missing invariant: the scheduled slot exists and is alive.**

Just `c.Alive c.current`; no further conjunct is needed. In particular nothing
has to be said about the *other* slots: a tombstone is a legitimate state for
any thread that is not scheduled, and out-of-range indices can only ever be
observed through `c.current`, since `Step` reads no other slot. -/
def Config.WF (c : Config α) : Prop := c.Alive c.current

/-- Well-formedness is precisely "the focus is not `none`". -/
theorem Config.wf_iff_focus {c : Config α} : c.WF ↔ ∃ t, c.focus = some t := by
  unfold Config.WF Config.Alive
  exact ⟨fun ⟨t, ht⟩ => ⟨t, Config.focus_eq_some.mpr ht⟩,
         fun ⟨t, ht⟩ => ⟨t, Config.focus_eq_some.mp ht⟩⟩

theorem Config.WF.focus {c : Config α} (h : c.WF) : ∃ t, c.focus = some t :=
  Config.wf_iff_focus.mp h

theorem Config.wf_of_focus {c : Config α} {t : Result α} (h : c.focus = some t) : c.WF :=
  Config.wf_iff_focus.mpr ⟨t, h⟩

/-- The initial configuration is well formed: its single thread is scheduled. -/
theorem init_wf (t : Result α) : (init t).WF := ⟨t, rfl⟩

/-- **Every rule of `Step` already requires its source to be well formed.**
Each of the five has `c.focus = some …` as a premise. -/
theorem Step.wf_src {c c' : Config α} (h : Step c c') : c.WF := by
  cases h
  case tick hfoc => exact Config.wf_of_focus hfoc
  case heap hfoc _ => exact Config.wf_of_focus hfoc
  case yield hfoc _ => exact Config.wf_of_focus hfoc
  case fork hfoc => exact Config.wf_of_focus hfoc
  case endthread hfoc _ => exact Config.wf_of_focus hfoc

/-- **Well-formedness is preserved.** `tick`, `heap` and `fork` keep `current`
and write a live thread back into that slot; `yield` and `endthread` change
`current`, and their `Config.Alive` side condition *is* the conclusion. -/
theorem Step.wf {c c' : Config α} (h : Step c c') : c'.WF := by
  cases h
  case tick k hfoc =>
    refine ⟨k PUnit.unit, ?_⟩
    exact getElem?_set_self _ (Config.focus_lt hfoc)
  case heap f k σ' hfoc _ =>
    refine ⟨k c.heap, ?_⟩
    exact getElem?_set_self _ (Config.focus_lt hfoc)
  case yield k j hfoc halive => exact halive
  case fork k hfoc =>
    refine ⟨k ConcE.Tags.cur, ?_⟩
    exact getElem?_set_append _ (Config.focus_lt hfoc)
  case endthread k j hfoc halive => exact halive

/-- Well-formedness along a whole execution. -/
theorem Reaches.wf {c c' : Config α} (h : Reaches c c') (hwf : c.WF) : c'.WF := by
  induction h with
  | refl _ => exact hwf
  | tail hs _ ih => exact ih hs.wf

/-- Every configuration reachable from `init t` is well formed; in particular
its focus is always `some`. -/
theorem reaches_init_wf {t : Result α} {c : Config α} (h : Reaches (init t) c) : c.WF :=
  h.wf (init_wf t)

/-! ## Halting, legitimately -/

/-- **The three ways a configuration may legitimately have no successor.**

* the scheduled thread has **returned** — for thread `0` that is the program's
  result, which is what `MayReturn` observes;
* the scheduled thread has **silently diverged** — permitted at `.part`, ruled
  out at `.total` by `divOK .total = False`;
* the scheduled thread is ending and **there is no live thread to hand the lock
  to**. This is the paper's `KillLastThread` case (footnote 7): the whole
  program is over.

Note what is *not* here: "the scheduled slot is a tombstone or out of range".
That is the wedged state, and `progress` says it is unreachable from a
well-formed configuration. -/
def Config.Halted (c : Config α) : Prop :=
  (∃ v, c.focus = some (Result.ok v))
  ∨ c.focus = some Result.div
  ∨ (∃ k, c.focus = some (Result.vis endthreadEv k) ∧ ∀ j, ¬ c.kill.Alive j)

/-! ## Progress -/

/-- **Progress.** A well-formed configuration that is not about to fault has
either legitimately halted or can take a step. There is no fourth case, so a
non-faulty execution never wedges.

This is the statement that gives `Safe` its teeth. `Safe t` on its own only says
that no *reachable* configuration faults, and it becomes vacuously easier to
satisfy the fewer configurations are reachable; with `progress` (and
`reaches_init_wf`, which supplies the hypothesis) every reachable configuration
is accounted for: it halts for one of the three reasons enumerated in
`Config.Halted`, or it steps. -/
theorem progress (c : Config α) (hwf : c.WF) (hnf : ¬ c.Faulty) :
    c.Halted ∨ ∃ c', Step c c' := by
  obtain ⟨t, hfoc⟩ := hwf.focus
  cases t
  case ret v =>
    exact .inl (.inl ⟨v, hfoc⟩)
  case div =>
    exact .inl (.inr (.inl hfoc))
  case vis e k =>
    /- Split the four summands of `RustEffect = FailE ⊕ₑ ConcE ⊕ₑ StepE ⊕ₑ StateE`. -/
    rcases e with e | e | e | e
    · /- `fail`: excluded by `¬ Faulty` (it is `Panics`). -/
      cases e with
      | fail err => exact absurd ⟨_, hfoc, .inl ⟨err, k, rfl⟩⟩ hnf
    · cases e with
      | fork =>
        /- Always enabled: the child is appended, nothing is required of it. -/
        exact .inr ⟨_, .fork hfoc⟩
      | yield =>
        /- Always enabled: control may pass to the current thread itself, which
        `hwf` (through `hfoc`) says is live in the updated pool. -/
        refine .inr ⟨_, .yield (j := c.current) hfoc ⟨k PUnit.unit, ?_⟩⟩
        exact getElem?_set_self _ (Config.focus_lt hfoc)
      | endthread =>
        /- Enabled iff some thread survives to take the lock. Otherwise this is
        the legitimate `KillLastThread` halt. -/
        by_cases hj : ∃ j, c.kill.Alive j
        · obtain ⟨j, hj⟩ := hj
          exact .inr ⟨_, .endthread hfoc hj⟩
        · exact .inl (.inr (.inr ⟨k, hfoc, by grind⟩))
    · /- `step`: always enabled, pure bookkeeping. -/
      cases e with
      | step => exact .inr ⟨_, .tick hfoc⟩
    · /- `modify f`: enabled iff `f` is defined at the current heap; when it is
      not, that is exactly `StuckOn`, excluded by `¬ Faulty`. -/
      cases e with
      | modify f =>
        rcases hfσ : f c.heap with _ | σ'
        · exact absurd ⟨_, hfoc, .inr ⟨f, k, rfl, hfσ⟩⟩ hnf
        · exact .inr ⟨_, .heap hfoc hfσ⟩

/-- `progress`, with `Config.Halted` spelled out. -/
theorem progress_disj (c : Config α) (hwf : c.WF) (hnf : ¬ c.Faulty) :
    (∃ v, c.focus = some (Result.ok v))
    ∨ (c.focus = some Result.div)
    ∨ (∃ k, c.focus = some (Result.vis endthreadEv k) ∧ ∀ j, ¬ c.kill.Alive j)
    ∨ (∃ c', Step c c') := by
  rcases progress c hwf hnf with (h | h | h) | h
  · exact .inl h
  · exact .inr (.inl h)
  · exact .inr (.inr (.inl h))
  · exact .inr (.inr (.inr h))

/-! ## `Halted` is exactly "no successor"

`progress` would be weak if `Config.Halted` were too generous — a `Halted` that
also held of steppable configurations would make the disjunction easy and say
nothing. It is not: the three cases are precisely the configurations with no
successor, so `progress` is an exact characterisation. -/

/-- Every rule of `Step` fires at a `vis` node. -/
private theorem Step.focus_vis {c c' : Config α} (h : Step c c') :
    ∃ (e : RustEffect.I) (k : RustEffect.O e → Result α),
      c.focus = some (Result.vis e k) := by
  cases h
  case tick k hfoc => exact ⟨_, k, hfoc⟩
  case heap f k σ' hfoc _ => exact ⟨_, k, hfoc⟩
  case yield k j hfoc _ => exact ⟨_, k, hfoc⟩
  case fork k hfoc => exact ⟨_, k, hfoc⟩
  case endthread k j hfoc _ => exact ⟨_, k, hfoc⟩

/-- Two readings of the same focus agree on the event. -/
private theorem focus_event_eq {c : Config α} {e₁ e₂ : RustEffect.I}
    {k₁ : RustEffect.O e₁ → Result α} {k₂ : RustEffect.O e₂ → Result α}
    (h₁ : c.focus = some (Result.vis e₁ k₁))
    (h₂ : c.focus = some (Result.vis e₂ k₂)) : e₂ = e₁ :=
  (Aeneas.Std.Result.vis.injEq (Option.some.inj (h₁.symm.trans h₂))).symm

/-- **A halted configuration really has no successor.** -/
theorem Config.Halted.no_step {c : Config α} (h : c.Halted) {c' : Config α} :
    ¬ Step c c' := by
  intro hs
  obtain ⟨e, k, hv⟩ := hs.focus_vis
  rcases h with ⟨v, hh⟩ | hh | ⟨kk, hh, hno⟩
  · exact Aeneas.Std.ok_not_vis (Option.some.inj (hh.symm.trans hv))
  · exact Aeneas.Std.div_not_vis (Option.some.inj (hh.symm.trans hv))
  · /- The event is `endthread`, so only that rule could have fired — and its
    side condition contradicts "no live thread". -/
    cases hs
    case tick k' hfoc => cases focus_event_eq hh hfoc
    case heap f k' σ' hfoc _ => cases focus_event_eq hh hfoc
    case yield k' j hfoc _ => cases focus_event_eq hh hfoc
    case fork k' hfoc => cases focus_event_eq hh hfoc
    case endthread k' j hfoc halive => exact hno j halive

/-! ## What `Safe` really delivers -/

/-- **A safe program never wedges.** Every configuration reachable from `init t`
either has legitimately halted or can take another step. -/
theorem safe_progress {t : Result α} (hs : Safe t) {c : Config α}
    (hr : Reaches (init t) c) : c.Halted ∨ ∃ c', Step c c' :=
  progress c (reaches_init_wf hr) (hs c hr)

/-- **A safe program's stuck configurations are exactly its halted ones.** This
is the contrapositive reading of `safe_progress`, and it is the property the
prose "the machine does not get stuck" actually names. -/
theorem safe_halted_of_no_step {t : Result α} (hs : Safe t) {c : Config α}
    (hr : Reaches (init t) c) (hstuck : ∀ c', ¬ Step c c') : c.Halted :=
  (safe_progress hs hr).resolve_right (fun ⟨c', hc'⟩ => hstuck c' hc')

/-- The focus of a reachable configuration is never `none`: the scheduled slot
is always in range and alive. -/
theorem safe_focus_isSome {t : Result α} {c : Config α}
    (hr : Reaches (init t) c) : ∃ t', c.focus = some t' :=
  (reaches_init_wf hr).focus

/-- `Halted` and "stuck" coincide on a safe program's reachable
configurations. This is the exact form of "the machine does not get stuck". -/
theorem safe_stuck_iff_halted {t : Result α} (hs : Safe t) {c : Config α}
    (hr : Reaches (init t) c) : c.Halted ↔ ∀ c', ¬ Step c c' :=
  ⟨fun h _ => h.no_step, safe_halted_of_no_step hs hr⟩

end

end AeneasIris.Semantics
