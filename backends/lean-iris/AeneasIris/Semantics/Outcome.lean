import AeneasIris.Semantics.Progress

/-!
# Outcome: a safe, terminating program actually runs to a result

This file is the answer to review finding #3:

> `SN` holds trivially of a configuration that has already stopped, so
> `Terminates` does not rule out deadlock; and `adequacy_total` never claims the
> program *produces* anything — it has no `∃ v, MayReturn t v` conjunct. A
> reader takes "total correctness" to mean "runs to completion and yields a
> result", but the statement does not say that.

The two halves of the fix live in two places and **neither suffices alone**:

* `Semantics/Progress.lean` gives **non-wedging**: a safe configuration either
  has legitimately halted or can take a step (`progress`), and `Config.Halted`
  is *exactly* the successor-free set (`Config.Halted.no_step`). On its own this
  is satisfied by a machine that runs forever — it never has to halt.
* `Terminates` gives **finiteness**: `SN c`, no infinite `Step` chain. On its
  own this is satisfied by a machine that wedges immediately — `Acc` holds
  vacuously of a configuration with no successors, whether that configuration
  stopped for a good reason or a bad one.

Put together they give the statement one actually wants, and it is entirely
operational: **from every reachable configuration the machine can be driven, in
finitely many steps, to a configuration that has stopped for one of the reasons
`Config.Halted` enumerates** (`reaches_halted`). Since `Terminates` also
excludes `Config.Diverging`, the `div` branch of `Config.Halted` is ruled out
and only two possibilities remain — the scheduled thread returned a value, or
the last live thread ended. That is `Config.Produces`, and `produces_result`.

Note in particular what this excludes that `Terminates` alone does not: a
**deadlock**, i.e. a reachable configuration with no successor that is not a
legitimate halt. A set of threads all spinning on a lock would step forever and
is excluded by `SN`; a set of threads all blocked would be successor-free and is
excluded by `progress`, which forces any successor-free configuration to be
`Halted`.

## What is *not* claimed

Nothing here proves `Terminates`. That obligation lives on the Iris side, and at
the time of writing it still rests on `sysInv_snInv` in `Termination.lean`.
Every theorem below takes `Terminates t` as a **hypothesis**, so this file is
`sorry`-free and stays independent of the unfinished Iris argument — which is
the point: the operational reasoning is separable and can be checked now.

Nor is it claimed that the thread that halts is the *main* thread. `MayReturn`
observes thread `0` specifically, and which thread happens to hold the lock at
the halt is a scheduling matter; `mayReturn_of_produces` is the one-line bridge
for the case where it is thread `0`, and `exists_mayReturn` packages the side
condition a client would discharge.
-/

namespace AeneasIris.Semantics

open Aeneas.Data.Coinductive
open Aeneas.Std (Result RustEffect RustHeap)

unseal Aeneas.Std.Result

section

variable {α : Type}

/-! ## `Reaches` is a preorder

`Machine.lean` defines `Reaches` by consing a step at the *head*, which is the
convenient form for `Safe`, but the induction below extends an execution at the
*tail*. These three are the missing glue. -/

theorem Reaches.single {c₁ c₂ : Config α} (h : Step c₁ c₂) : Reaches c₁ c₂ :=
  .tail h (.refl c₂)

theorem Reaches.trans {c₁ c₂ c₃ : Config α} (h₁ : Reaches c₁ c₂) (h₂ : Reaches c₂ c₃) :
    Reaches c₁ c₃ := by
  induction h₁ with
  | refl _ => exact h₂
  | tail hs _ ih => exact .tail hs (ih h₂)

theorem Reaches.snoc {c₁ c₂ c₃ : Config α} (h : Reaches c₁ c₂) (s : Step c₂ c₃) :
    Reaches c₁ c₃ :=
  h.trans (.single s)

/-- Nothing is reachable from a configuration with no successor except itself. -/
theorem Reaches.eq_of_no_step {c c' : Config α} (h : Reaches c c')
    (hstuck : ∀ c₂, ¬ Step c c₂) : c' = c := by
  cases h with
  | refl _ => rfl
  | tail hs _ => exact absurd hs (hstuck _)

/-! ## Producing a result

`Config.Halted` has three branches; `¬ Config.Diverging` kills the middle one.
What is left is the honest notion of "the program is over". -/

/-- **The two ways a run can end with something to show for it.**

* the scheduled thread **returned a value** — for thread `0` that value is the
  program's result, and `mayReturn_of_produces` turns this into `MayReturn`;
* the scheduled thread ran `endthread` and **no live thread remains**, so the
  whole program is over (the paper's `KillLastThread`).

Silent divergence is deliberately absent: it is a legitimate *halt* at `.part`
but it is not a *result*, and `Terminates` excludes it. A `Config.Produces`
disjunction that still admitted `Result.div` would say nothing. -/
def Config.Produces (c : Config α) : Prop :=
  (∃ v, c.focus = some (Result.ok v))
  ∨ (∃ k, c.focus = some (Result.vis endthreadEv k) ∧ ∀ j, ¬ c.kill.Alive j)

/-- A halt that is not a divergence is a result. This is the only place the
`div` branch of `Config.Halted` is discharged, and it is discharged by
`Terminates`, not by anything structural. -/
theorem Config.Halted.produces {c : Config α} (h : c.Halted) (hd : ¬ c.Diverging) :
    c.Produces := by
  rcases h with h | h | h
  · exact .inl h
  · exact absurd ⟨Result.div, h, rfl⟩ hd
  · exact .inr h

/-- A producing configuration has indeed stopped. -/
theorem Config.Produces.halted {c : Config α} (h : c.Produces) : c.Halted := by
  rcases h with h | h
  · exact .inl h
  · exact .inr (.inr h)

theorem Config.Produces.no_step {c : Config α} (h : c.Produces) {c' : Config α} :
    ¬ Step c c' :=
  h.halted.no_step

/-! ## The main theorem -/

/-- The well-founded recursion behind `reaches_halted`, with the reachability
hypothesis in the motive so that `Acc`'s induction hypothesis can be used. -/
private theorem reaches_halted_aux {t : Result α} (hS : Safe t) (hT : Terminates t)
    (c : Config α) (hsn : SN c) :
    Reaches (init t) c → ∃ c', Reaches c c' ∧ c'.Halted ∧ ¬ c'.Diverging := by
  unfold SN at hsn
  induction hsn with
  | intro c _hacc ih =>
    intro hr
    by_cases hstep : ∃ c₂, Step c c₂
    · /- Not stopped yet: take any successor and recurse. `Acc` supplies the
      induction hypothesis; `Reaches.snoc` keeps the successor reachable from
      `init t`, and `Reaches.tail` glues the answer back on. -/
      obtain ⟨c₂, hs⟩ := hstep
      obtain ⟨c', hrc', hh, hd⟩ := ih c₂ hs (hr.snoc hs)
      exact ⟨c', .tail hs hrc', hh, hd⟩
    · /- No successor. By `progress` (through `safe_halted_of_no_step`) that can
      only be a legitimate halt, and `Terminates` says it is not a divergence. -/
      have hh : c.Halted :=
        safe_halted_of_no_step hS hr (fun c₂ hc₂ => hstep ⟨c₂, hc₂⟩)
      exact ⟨c, .refl c, hh, (hT c hr).2⟩

/-- **A safe, terminating program can always be driven to a legitimate halt.**

From *any* reachable configuration, finitely many steps lead to a configuration
that has stopped for one of the reasons `Config.Halted` enumerates, and that is
not silently diverging.

Both hypotheses are needed. Without `Safe`, `progress` does not apply and the
run could stop at a fault. Without `Terminates`, the recursion has nothing to
descend on and the machine may step forever. Conversely neither hypothesis alone
is enough — see the module docstring. -/
theorem reaches_halted {t : Result α} (hS : Safe t) (hT : Terminates t) :
    ∀ c, Reaches (init t) c → ∃ c', Reaches c c' ∧ c'.Halted ∧ ¬ c'.Diverging :=
  fun c hr => reaches_halted_aux hS hT c (hT c hr).1 hr

/-- **`reaches_halted`, with the `div` branch actually eliminated.**

This is the shape the review asked for: from every reachable configuration the
machine reaches one in which either the scheduled thread has returned a value,
or the last live thread has ended. Divergence is gone — that is what `Terminates`
buys, and a version of this statement that still admitted `Result.div` would be
empty. -/
theorem produces_result {t : Result α} (hS : Safe t) (hT : Terminates t) :
    ∀ c, Reaches (init t) c → ∃ c', Reaches c c' ∧ c'.Produces := by
  intro c hr
  obtain ⟨c', hrc', hh, hd⟩ := reaches_halted hS hT c hr
  exact ⟨c', hrc', hh.produces hd⟩

/-- `produces_result`, fully unfolded. -/
theorem produces_result_disj {t : Result α} (hS : Safe t) (hT : Terminates t) :
    ∀ c, Reaches (init t) c → ∃ c', Reaches c c' ∧
      ((∃ v, c'.focus = some (Result.ok v))
        ∨ (∃ k, c'.focus = some (Result.vis endthreadEv k) ∧ ∀ j, ¬ c'.kill.Alive j)) :=
  produces_result hS hT

/-- Specialised to the start: the program as a whole runs to a result. -/
theorem exists_produces {t : Result α} (hS : Safe t) (hT : Terminates t) :
    ∃ c, Reaches (init t) c ∧ c.Produces := by
  obtain ⟨c, hrc, hp⟩ := produces_result hS hT (init t) (.refl _)
  exact ⟨c, hrc, hp⟩

/-! ## Back to the main thread

`MayReturn` observes thread `0` while it holds the big lock. `Config.Produces`
does not say *which* thread halted, so the last step is a side condition the
client supplies — but once supplied, the bridge is definitional. -/

/-- **The bridge.** A reachable configuration in which the main thread is
scheduled and has returned `v` *is* a witness for `MayReturn t v`. -/
theorem mayReturn_of_produces {t : Result α} {c : Config α} {v : α}
    (hr : Reaches (init t) c) (hcur : c.current = 0)
    (hok : c.focus = some (Result.ok v)) : MayReturn t v :=
  ⟨c, hr, hcur, hok⟩

/-- **Safe + terminating + "the run ends with the main thread returning"
⟹ the program returns a value.**

⚠️ **This is bookkeeping, not a result.** Read the third hypothesis: it already
asserts `c.current = 0 ∧ ∃ v, c.focus = some (Result.ok v)` at the producing
configuration, which is exactly what `MayReturn` needs. So the theorem adds
essentially nothing to `exists_produces` — it repackages it. The real content is
in `exists_produces` (safety plus termination reach a halted configuration) and
in `mayReturn_of_produces` (that such a configuration is a `MayReturn` witness);
this just chains them.

The hypothesis is not discharged anywhere in general, and it cannot be: the
machine does not guarantee that the halting thread is the main one — see
`All.lean`'s note on a non-main thread freezing the machine at `ret`. A client
must either prove it for its own program or, better, write the trace directly
as `Example.prog_mayReturn` does.

Chain with `post_of_provable` (`Semantics/Soundness.lean`) to get "terminates
*and* the returned value satisfies `φ`". -/
theorem exists_mayReturn {t : Result α} (hS : Safe t) (hT : Terminates t)
    (hmain : ∀ c, Reaches (init t) c → c.Produces →
      c.current = 0 ∧ ∃ v, c.focus = some (Result.ok v)) :
    ∃ v, MayReturn t v := by
  obtain ⟨c, hr, hp⟩ := exists_produces hS hT
  obtain ⟨hcur, v, hok⟩ := hmain c hr hp
  exact ⟨v, mayReturn_of_produces hr hcur hok⟩

/-! ## Non-vacuity

`reaches_halted` and friends assume `Safe t ∧ Terminates t`. If those two were
jointly unsatisfiable everything above would be vacuously true, so here is a
witness — the simplest possible program, which returns immediately — carried all
the way to a `MayReturn`. This is the same discipline as `Config.Halted.no_step`
in `Progress.lean`: check that the theorem is not empty before believing it. -/

private theorem init_ok_no_step (v : α) (c : Config α) : ¬ Step (init (Result.ok v)) c :=
  Config.Halted.no_step (.inl ⟨v, rfl⟩)

theorem safe_ok (v : α) : Safe (Result.ok v) := by
  intro c hr
  obtain rfl := hr.eq_of_no_step (init_ok_no_step v)
  rintro ⟨t', hf, hbad⟩
  obtain rfl : t' = Result.ok v := (Option.some.inj hf).symm
  rcases hbad with ⟨e, k, he⟩ | ⟨f, k, he, _⟩
  · exact Aeneas.Std.ok_not_vis he
  · exact Aeneas.Std.ok_not_vis he

theorem terminates_ok (v : α) : Terminates (Result.ok v) := by
  intro c hr
  obtain rfl := hr.eq_of_no_step (init_ok_no_step v)
  refine ⟨.intro _ (fun y hy => absurd hy (init_ok_no_step v y)), ?_⟩
  rintro ⟨t', hf, hd⟩
  obtain rfl : t' = Result.ok v := (Option.some.inj hf).symm
  exact Aeneas.Std.ok_not_div hd

/-- End to end on the witness: the hypotheses hold, and the conclusion really
does yield a returned value. -/
example (v : α) : ∃ w, MayReturn (Result.ok v) w :=
  exists_mayReturn (safe_ok v) (terminates_ok v)
    (fun c hr _ => by
      obtain rfl := hr.eq_of_no_step (init_ok_no_step v)
      exact ⟨rfl, v, rfl⟩)

end

end AeneasIris.Semantics
