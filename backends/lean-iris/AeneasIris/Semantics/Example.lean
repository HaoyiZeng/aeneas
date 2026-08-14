import AeneasIris.Semantics.Races
import AeneasIris.Semantics.Outcome
import AeneasIris.Tactics.Core

/-!
# A worked example, end to end

Every link of the chain is now in place —

```
one `wpi` triple  ⟹  Safe  +  (MayReturn ⟹ φ)  +  DataRaceFree
```

— but until this file nobody had actually **walked** it. Here we take a concrete
program of exactly the shape Aeneas emits, prove one `wpi` triple about it, and
feed that triple to `safe_of_provable`, `dataRaceFree_of_provable` and
`post_of_provable`. What comes out the other end are three statements with **no
Iris in them at all**: pure `Prop`s about the machine of `Semantics/Machine.lean`.

## What the three conclusions say

For `prog = do let l ← alloc 0; store l 42; load l`:

* `prog_safe : Safe prog` — under **every schedule**, no reachable configuration
  is about to panic or to perform an undefined heap operation. Since
  `AccessState` is λRust's read/write state machine and `Val` pairs a type with
  an inhabitant, "undefined heap operation" covers out-of-bounds, use-after-free,
  type confusion *and* racing accesses.
* `prog_race_free : DataRaceFree prog` — the race strand of the above, stated
  with a definition of *race* (`RacesOn`) that does not mention "stuck".
* `prog_result : ∀ v, MayReturn prog v → v = 42` — if the main thread is
  scheduled and has returned, its value is `42`.

## Why this is also the strongest non-vacuity check available

`ProvableSpecOf` quantifies over **every** `BundledGFunctors` and **every**
`Iris.HasLC`, with the `InvGS_gen` and `HeapGS` instances bound in the telescope.
If that quantification were subtly wrong — if, say, the heap instance could not
actually be used under a universally quantified `GF` — then no real program
would satisfy it and the whole adequacy chain would be vacuously true. `prog_spec`
is a witness that it is not: the hypothesis of `safe_of_provable` is inhabited by
an honest program that touches the heap three times.

`prog_returns_42'` closes the loop: `∃ v, MayReturn prog v ∧ v = 42`,
unconditionally. The `MayReturn` half is `prog_mayReturn`, the six-step machine
execution written out explicitly; the `= 42` half is `prog_result`, i.e. the
`wpi` triple travelling through `post_of_provable`. It is deliberately *not*
closed by `rfl` — `42 = 42` holds by computation, so an `rfl` proof would
sidestep the logic entirely and witness nothing. No appeal to `Terminates` is
needed either, which matters because termination still rests on two open lemmas
in `Termination.lean`, and mixing a `sorry`-backed result in here would destroy
the point of the `#print axioms` check.

Writing that trace out required working around a real gap in the ITree
infrastructure; see "Peeling the ITree" below.

## What is trusted

Nothing about the semantics of Rust. The chain starts at the ITree — which *is*
the language, as `Machine.lean` explains — and ends at a `Prop` about that
machine. The single trust assumption is unchanged from today's Aeneas: that the
ITree it emits corresponds to the Rust source. No step of this file assumes
anything else.
-/

namespace AeneasIris.Semantics.Example

open Iris BI Aeneas.Data.Coinductive
open AeneasIris AeneasIris.HeapAPI AeneasIris.Heap
open scoped AeneasIris
open scoped Aeneas
open AeneasIris.Semantics
open Aeneas.Std (Result RustEffect Loc)

unseal Aeneas.Std.Result

/-! ## The program

Written exactly as a translated Rust function would be: in `Result`, with the
`HeapAPI` operations. Allocate a cell holding `0`, overwrite it with `42`, read
it back. -/

noncomputable def prog : Result Nat := do
  let l ← alloc (E := RustEffect) (0 : Nat)
  let _ ← store (E := RustEffect) l (42 : Nat)
  load (T := Nat) (E := RustEffect) l

/-! ## The triple

One proof, in an arbitrary Iris model. At `.part` every heap operation issues a
`▷`; `istep` spends it (`wpi_stepThen'`, then `ilat; inext`) and applies the
registered body rule, so one `istep` per operation is all that is needed. -/

theorem prog_spec : ProvableSpecOf .part prog (fun v => v = 42) := by
  intro GF hlc _ _
  unfold prog
  iintro _
  istep as ⟨l, Hl⟩
  istep
  istep
  itrivial

/-! ## Landing in plain Lean

Three applications, no Iris in any of the statements. -/

/-- **No panic, no undefined heap operation, under any schedule.** -/
theorem prog_safe : Safe prog := safe_of_provable prog_spec

/-- **No data races, under any schedule.** -/
theorem prog_race_free : DataRaceFree prog := dataRaceFree_of_provable prog_spec

/-- **If the main thread returns, it returns `42`.** -/
theorem prog_result : ∀ v, MayReturn prog v → v = 42 := post_of_provable prog_spec

/-! ## The conclusions really are Iris-free

Restated with everything unfolded, so that one can see there is no `IProp`,
no `BundledGFunctors` and no modality left — only `Config`, `Step` and
`Reaches`. -/

example : ∀ c, Reaches (init prog) c → ¬ c.Faulty := prog_safe

example : ∀ c, Reaches (init prog) c → ¬ c.Racing := prog_race_free

example : ∀ (v : Nat) (c : Config Nat),
    Reaches (init prog) c → c.current = 0 → c.focus = some (Result.ok v) → v = 42 :=
  fun v c hr hcur hfoc => prog_result v ⟨c, hr, hcur, hfoc⟩

/-- Combined with `Progress.lean`: a configuration reachable from `prog` that
cannot step has halted for one of the three enumerated reasons — it has not
wedged. -/
theorem prog_no_wedge : ∀ c, Reaches (init prog) c → (∀ c', ¬ Step c c') → c.Halted :=
  fun _ hr hstuck => safe_halted_of_no_step prog_safe hr hstuck

/-- Every configuration `prog` reaches is in a well-defined state: it has
halted, or it can step. -/
theorem prog_progress : ∀ c, Reaches (init prog) c → c.Halted ∨ ∃ c', Step c c' :=
  fun c hr => progress c (reaches_init_wf hr) (prog_safe c hr)

/-! ## `MayReturn` is inhabitable

`prog_result` is an implication, so it would say nothing if `MayReturn t v` held
for no `t`, `v` at all. It does not: the simplest program returns immediately,
and the witness is the initial configuration itself. -/

/-- **Non-vacuity of `MayReturn`.** `init (ok v)` already has the main thread
scheduled and returning, so no steps are needed. -/
theorem mayReturn_ok (v : Nat) : MayReturn (Result.ok v) v :=
  ⟨init (Result.ok v), .refl _, rfl, rfl⟩

/-! ## Peeling the ITree

To build a machine trace one needs `c.focus = some (Result.vis <ev> k)` with a
nameable `k`, i.e. the ITree has to be peeled to a `vis` node. That runs into a
real gap in the infrastructure, worth recording because the workaround is not
obvious and the proper fix is upstream.

**Symptom.** `Aeneas.Std.bind_vis` refuses to fire on a term that prints
*character-for-character identically to its own pattern*, even with
`pp.universes`. With `pp.explicit` the difference appears:

```
@Aeneas.Std.bind PUnit.{2} Nat (@Result.vis (RustEffect.O stepEv) stepEv ...)
```

`bind`'s value-type argument is `PUnit.{2}`; `Result.vis`'s is
`RustEffect.O stepEv`. `bind_vis` needs them to be the *same* argument.

**Root cause.** They are definitionally equal only through the `unif_hint`s in
`Aeneas/Data/Coinductive/Effect.lean`, which exist because `SumE` must **not**
be `@[reducible]` (it has to stay keyable for instance search). `isDefEq`
consults those hints; `simp`/`rw` keyed matching does not.

**Workaround used here**, all `rfl`, all local to this file:

* `sumE_O_inl`/`sumE_O_inr` and `rustEffect_O_stepEv`/`rustEffect_O_modifyEv`
  give the rewriter the reduction the hints were covering;
* `trigger_step_eq`/`trigger_act_eq` state the two primitive events directly in
  `Result.vis` form — note `trigger_step_eq` is phrased with
  `fun _ => Result.ok PUnit.unit` rather than `fun x => Result.ok x`, which is
  what forces the value-type argument to be `PUnit` and makes `bind_vis` match;
* `itree_bind_eq_std`/`itree_ret_eq_ok` reconcile the three `bind`s in play
  (`ITree.bind`, the ITree and `Result` `Monad` instances).

**Proper fix, upstream:** add `sumE_O_inl`/`sumE_O_inr` as `@[simp]` in
`Aeneas/Data/Coinductive/Effect.lean`, next to the `unif_hint`s. Two `rfl`
lines; they make the hints redundant *for the rewriter* without making `SumE`
reducible for instance search.

⚠️ Note `bind`-on-`vis` is **not** definitional — `ITree.bind` is a
`partial_fixpoint`, so `rfl` cannot do this and the rewrite is unavoidable.

The lemmas below are what came out of that.
 -/

section Peeling

open Aeneas.Std (Val StepE StateE RustHeap HMap Cell AccessState)
open Std.PartialMap
open scoped Aeneas.Std

/-- The answer type of a sum effect reduces. Both `rfl`, but the rewriter needs
them spelled out: `SumE` cannot be `@[reducible]` (it must stay keyable for
instance search), so `Aeneas/Data/Coinductive/Effect.lean` supplies `unif_hint`s
instead — and `unif_hint`s serve `isDefEq`, not `simp`/`rw` keyed matching. -/
@[simp] theorem sumE_O_inl {E₁ E₂ : Effect} (i : E₁.I) :
    (E₁ ⊕ₑ E₂).O (Sum.inl i) = E₁.O i := rfl

@[simp] theorem sumE_O_inr {E₁ E₂ : Effect} (i : E₂.I) :
    (E₁ ⊕ₑ E₂).O (Sum.inr i) = E₂.O i := rfl

/-- The answer types of the two events the example uses, reduced. -/
@[simp] theorem rustEffect_O_stepEv : RustEffect.O stepEv = PUnit.{2} := rfl

@[simp] theorem rustEffect_O_modifyEv (f : RustHeap.{0} → Option RustHeap.{0}) :
    RustEffect.O (modifyEv f) = RustHeap.{0} := rfl

/-- The two monads' `bind`s agree; `Aeneas.Std.bind` is the `Result`-level one. -/
theorem itree_bind_eq_std.{ua, ub} {α : Type ua} {β : Type ub}
    (t : Result α) (f : α → Result β) :
    ITree.bind t f = Aeneas.Std.bind t f := rfl

theorem itree_ret_eq_ok.{ua} {α : Type ua} (a : α) :
    (ITree.ret a : Result α) = Result.ok a := rfl

/-- The sub-effect injections compute: `Subeffect.map` at `StepE`/`StateE` really
is the `@[match_pattern]` abbreviation the machine's rules are stated with, with
the identity answer map. This is what lets `Effect.trigger`'s `let ⟨i₂,f⟩ := …`
iota-reduce. -/
theorem submap_step :
    (Subeffect.map (E₁ := StepE.{1}) (E₂ := RustEffect) StepE.I.step)
      = ⟨stepEv, fun x => x⟩ := rfl

theorem submap_modify (f : RustHeap.{0} → Option RustHeap.{0}) :
    (Subeffect.map (E₁ := StateE RustHeap.{0}) (E₂ := RustEffect) (StateE.I.modify f))
      = ⟨modifyEv f, fun x => x⟩ := rfl

/-- **The two events, in `Result` form.** These are the payoff of `submap_*`: the
primitive operations of the machine, with no `Effect.trigger` left. Both `rfl`. -/
theorem trigger_step_eq :
    (AeneasIris.Step.step (E := RustEffect))
      = Result.vis stepEv (fun _ => Result.ok PUnit.unit) := rfl

theorem trigger_act_eq (f : RustHeap.{0} → Option RustHeap.{0}) :
    (Heap.act (E := RustEffect) f) = Result.vis (modifyEv f) (fun s => Result.ok s) := rfl

/-! ### Peeling one operation

Each `HeapAPI` operation is `stepP` followed by an `act'`, so it contributes a
`tick` and then a `heap` step. These two lemmas turn the ITree into the `vis`
form the machine's rules are stated with. -/

/-- `act'` is a single `modify` event. -/
private theorem bind_act'_eq {R : Type} (f : RustHeap.{0} → Option RustHeap.{0})
    (k : RustHeap.{0} → R) (rest : R → Result Nat) :
    ITree.bind (Heap.act' (E := RustEffect) f k) rest
      = Result.vis (modifyEv f) (fun s => rest (k s)) := by
  unfold Heap.act'
  simp [trigger_act_eq, itree_bind_eq_std, itree_ret_eq_ok]

/-- `act'` at the end of a thread. -/
private theorem act'_eq {R : Type} (f : RustHeap.{0} → Option RustHeap.{0})
    (k : RustHeap.{0} → R) :
    (Heap.act' (E := RustEffect) f k : Result R)
      = Result.vis (modifyEv f) (fun s => Result.ok (k s)) := by
  unfold Heap.act'
  simp [trigger_act_eq, itree_bind_eq_std, itree_ret_eq_ok]

/-- A `stepP`-prefixed operation is a single `step` event followed by its body. -/
private theorem bind_stepThen_eq {R : Type} (body : Result R) (rest : R → Result Nat) :
    ITree.bind (ITree.bind (AeneasIris.Step.stepP (E := RustEffect)) (fun _ => body)) rest
      = Result.vis stepEv (fun _ => ITree.bind body rest) := by
  simp [AeneasIris.Step.stepP, trigger_step_eq, itree_bind_eq_std, itree_ret_eq_ok]

private theorem stepThen_eq {R : Type} (body : Result R) :
    (ITree.bind (AeneasIris.Step.stepP (E := RustEffect)) (fun _ => body) : Result R)
      = Result.vis stepEv (fun _ => body) := by
  simp [AeneasIris.Step.stepP, trigger_step_eq, itree_bind_eq_std, itree_ret_eq_ok]

/-! ### One machine step, in a single-threaded configuration -/

private theorem tick1 {tr : Result Nat} {k : RustEffect.O stepEv → Result Nat}
    {σ : RustHeap.{0}} (h : tr = Result.vis stepEv k) :
    Step (⟨[Thread.alive tr], 0, σ⟩ : Config Nat)
         ⟨[Thread.alive (k PUnit.unit)], 0, σ⟩ := by
  subst h; exact Step.tick rfl

private theorem heap1 {tr : Result Nat} {f : RustHeap.{0} → Option RustHeap.{0}}
    {k : RustEffect.O (modifyEv f) → Result Nat} {σ σ' : RustHeap.{0}}
    (h : tr = Result.vis (modifyEv f) k) (hf : f σ = some σ') :
    Step (⟨[Thread.alive tr], 0, σ⟩ : Config Nat) ⟨[Thread.alive (k σ)], 0, σ'⟩ := by
  subst h; exact Step.heap rfl hf

/-! ### The trace

Six machine steps: `tick`/`heap` for each of `alloc`, `store`, `load`. -/

private noncomputable def prog2 (l : Loc) : Result Nat :=
  ITree.bind (HeapAPI.store (E := RustEffect) l (42 : Nat))
    (fun _ => HeapAPI.load (T := Nat) (E := RustEffect) l)

private noncomputable def prog1 : Result Nat :=
  ITree.bind (Heap.alloc_body (E := RustEffect) (Val.pack (0 : Nat))) prog2

/-- The fresh-location function `alloc_body` uses. -/
private def freshOf (σ : RustHeap.{0}) : Loc :=
  Std.fresh (M := HMap.{1}) (K := Loc) (V := Cell.{1} Val.{0}) (m := σ) trivial

private def allocF (v : Val.{0}) : RustHeap.{0} → Option RustHeap.{0} :=
  fun σ => some (Std.insert σ (freshOf σ) (AccessState.reading 0, v))

private theorem alloc_body_eq (v : Val.{0}) :
    Heap.alloc_body (E := RustEffect) v = Heap.act' (allocF v) freshOf := rfl

private def storeF (l : Loc) (v : Val.{0}) : RustHeap.{0} → Option RustHeap.{0} :=
  fun σ => match Std.get? σ l with
    | some (AccessState.reading 0, _) => some (Std.insert σ l (AccessState.reading 0, v))
    | _ => none

private theorem store_body_eq (l : Loc) (v : Val.{0}) :
    Heap.store_body.{0,0} (E := RustEffect) l v
      = Heap.act' (storeF l v) (fun _ => PUnit.unit) := rfl

private noncomputable def loadF (T : Type) (l : Loc) : RustHeap.{0} → Option RustHeap.{0} :=
  fun σ => match Std.get? σ l with
    | some (AccessState.reading _, v) => if v.1 = T then some σ else none
    | _ => none

private theorem load_body_eq (T : Type) (l : Loc) :
    Heap.load_body (E := RustEffect) T l
      = ITree.bind (Heap.act' (loadF T l) (fun σ => (Heap.valAt l σ).bind (Val.unpackO T)))
          (fun o => match o with
                    | some x => ITree.ret x
                    | none => Heap.panic) := rfl

/-! ### The concrete heaps -/

private def loc0 : Loc := freshOf ∅

private def heapA : RustHeap.{0} :=
  Std.insert (∅ : RustHeap.{0}) loc0 (AccessState.reading 0, Val.pack (0 : Nat))

private def heapB : RustHeap.{0} :=
  Std.insert heapA loc0 (AccessState.reading 0, Val.pack (42 : Nat))

private theorem allocF_empty :
    allocF (Val.pack (0 : Nat)) (∅ : RustHeap.{0}) = some heapA := rfl

private theorem storeF_heapA :
    storeF loc0 (Val.pack (42 : Nat)) heapA = some heapB := by
  simp only [storeF, heapA, heapB, Std.get?_insert_eq rfl]

private theorem loadF_heapB : loadF Nat loc0 heapB = some heapB := by
  simp only [loadF, heapB, Std.get?_insert_eq rfl, if_true]

private theorem unpack_heapB : (Heap.valAt loc0 heapB).bind (Val.unpackO Nat) = some 42 := by
  simp only [Heap.valAt, heapB, Std.get?_insert_eq rfl, Option.bind_some, Val.unpackO_pack]

/-! ### `MayReturn prog 42`

The whole execution, six steps, with no `Terminates` and no `sorry`. -/

theorem prog_mayReturn : MayReturn prog 42 := by
  have e1 : prog = Result.vis stepEv (fun _ => prog1) :=
    bind_stepThen_eq (Heap.alloc_body (E := RustEffect) (Val.pack (0 : Nat))) prog2
  have e2 : prog1 = Result.vis (modifyEv (allocF (Val.pack (0 : Nat))))
      (fun s => prog2 (freshOf s)) :=
    bind_act'_eq (allocF (Val.pack (0 : Nat))) freshOf prog2
  have e3 : ∀ l : Loc, prog2 l = Result.vis stepEv
      (fun _ => ITree.bind (Heap.store_body.{0,0} (E := RustEffect) l (Val.pack (42 : Nat)))
        (fun _ => HeapAPI.load (T := Nat) (E := RustEffect) l)) :=
    fun _ => bind_stepThen_eq _ _
  have e4 : ∀ l : Loc,
      ITree.bind (Heap.store_body.{0,0} (E := RustEffect) l (Val.pack (42 : Nat)))
          (fun _ => HeapAPI.load (T := Nat) (E := RustEffect) l)
        = Result.vis (modifyEv (storeF l (Val.pack (42 : Nat))))
            (fun _ => HeapAPI.load (T := Nat) (E := RustEffect) l) :=
    fun _ => bind_act'_eq _ _ _
  have e5 : ∀ l : Loc, HeapAPI.load (T := Nat) (E := RustEffect) l
      = Result.vis stepEv (fun _ => Heap.load_body (E := RustEffect) Nat l) :=
    fun _ => stepThen_eq _
  have e6 : ∀ l : Loc, Heap.load_body (E := RustEffect) Nat l
      = Result.vis (modifyEv (loadF Nat l))
          (fun s => match (Heap.valAt l s).bind (Val.unpackO Nat) with
                    | some x => Result.ok x
                    | none => Heap.panic) :=
    fun _ => by
      rw [load_body_eq, act'_eq]
      simp only [Aeneas.Std.Result.vis, Aeneas.Std.Result.ok,
        Aeneas.Data.Coinductive.itree_vis_bind, Aeneas.Data.Coinductive.itree_ret_bind]
      apply congrArg
      funext s
      cases (Heap.valAt _ s).bind (Val.unpackO Nat) <;> rfl
  refine ⟨⟨[Thread.alive (match (Heap.valAt loc0 heapB).bind (Val.unpackO Nat) with
              | some x => Result.ok x
              | none => Heap.panic)], 0, heapB⟩,
    ?_, rfl, ?_⟩
  · exact .tail (tick1 e1)
      (.tail (heap1 e2 allocF_empty)
        (.tail (tick1 (e3 loc0))
          (.tail (heap1 (e4 loc0) storeF_heapA)
            (.tail (tick1 (e5 loc0))
              (.tail (heap1 (e6 loc0) loadF_heapB) (.refl _))))))
  · show some (match (Heap.valAt loc0 heapB).bind (Val.unpackO Nat) with
               | some x => Result.ok x
               | none => Heap.panic) = some (Result.ok 42)
    rw [unpack_heapB]

end Peeling



/-! ## The concurrent half: `fork`, `yield`, `endthread`

`prog` exercises only `Step.tick` and `Step.heap`. The other three rules — the
big-lock handoff — had no concrete witness at all, and they are the subtle part
of the design. `cprog` spawns a thread, yields to it, and lets it end, so the
trace below fires **all three**.

`Conc.spawn t` is `fork`, then `match tag with | .cur => ret () | .new => t;
endthread`. Note the Unix-style duplication the machine's `fork` rule encodes:
the *whole* continuation `k` is resumed twice, so the child's tree is
`k .new` — the spawn body followed by `endthread`, with the parent's remaining
work appended but unreachable past the `PEmpty` continuation. -/

section Conc

open Aeneas.Std (Val RustHeap ConcE)

noncomputable def cprog : Result Unit := do
  let _ ← Conc.spawn (E := RustEffect) (Result.ok ())
  let _ ← Conc.yieldU (E := RustEffect)
  Result.ok ()

/-! ### The three events, in `Result` form

Same trick as `trigger_step_eq`: the continuation is phrased so that
`Result.ok`'s implicit type argument elaborates to the *reduced* answer type, so
that `bind_vis` can match. -/

theorem trigger_fork_eq :
    (Effect.trigger ConcE.{1} ConcE.I.fork : Result (ConcE.O ConcE.I.fork))
      = Result.vis (α := ConcE.O ConcE.I.fork) forkEv (fun x => Result.ok x) := rfl

theorem trigger_yield_eq :
    (Effect.trigger ConcE.{1} ConcE.I.yield : Result PUnit.{2})
      = Result.vis yieldEv (fun _ => Result.ok PUnit.unit) := rfl

theorem trigger_endthread_eq :
    (Effect.trigger ConcE.{1} ConcE.I.endthread : Result (ConcE.O ConcE.I.endthread))
      = Result.vis (α := ConcE.O ConcE.I.endthread) endthreadEv (fun x => Result.ok x) := rfl

/-! ### One concurrent machine step -/

private theorem fork1 {tr : Result Unit} {k : RustEffect.O forkEv → Result Unit}
    {σ : RustHeap.{0}} (h : tr = Result.vis forkEv k) :
    Step (⟨[Thread.alive tr], 0, σ⟩ : Config Unit)
      ⟨[Thread.alive (k ConcE.Tags.cur), Thread.alive (k ConcE.Tags.new)], 0, σ⟩ := by
  subst h; exact Step.fork rfl

/-- Yield from thread `0` to thread `1`. -/
private theorem yield01 {t0 t1 : Result Unit} {k : RustEffect.O yieldEv → Result Unit}
    {σ : RustHeap.{0}} (h : t0 = Result.vis yieldEv k) :
    Step (⟨[Thread.alive t0, Thread.alive t1], 0, σ⟩ : Config Unit)
      ⟨[Thread.alive (k PUnit.unit), Thread.alive t1], 1, σ⟩ := by
  subst h; exact Step.yield (j := 1) rfl ⟨t1, rfl⟩

/-- Thread `1` ends; the lock goes back to thread `0`, which is still alive.
(Had thread `0` been dead too this would be `KillLastThread` and no rule would
fire — which is why the parent must not have finished yet.) -/
private theorem endthread10 {t0 t1 : Result Unit}
    {k : RustEffect.O endthreadEv → Result Unit} {σ : RustHeap.{0}}
    (h : t1 = Result.vis endthreadEv k) :
    Step (⟨[Thread.alive t0, Thread.alive t1], 1, σ⟩ : Config Unit)
      ⟨[Thread.alive t0, Thread.dead], 0, σ⟩ := by
  subst h; exact Step.endthread (j := 0) rfl ⟨t0, rfl⟩

/-! ### Peeling `spawn` -/

private noncomputable def spawnBody (t : Result Unit) (tag : ConcE.Tags.{1}) : Result Unit :=
  match tag with
  | .cur => Result.ok ()
  | .new => ITree.bind t (fun _ =>
      ITree.bind (Effect.trigger ConcE.{1} ConcE.I.endthread) (fun o => PEmpty.elim o))

private theorem spawn_eq (t : Result Unit) :
    Conc.spawn (E := RustEffect) t
      = ITree.bind (Effect.trigger ConcE.{1} ConcE.I.fork) (spawnBody t) := rfl

private noncomputable def crest : Unit → Result Unit :=
  fun _ => ITree.bind (Conc.yieldU (E := RustEffect)) (fun _ => Result.ok ())

private noncomputable def cforked (tag : ConcE.Tags.{1}) : Result Unit :=
  ITree.bind (spawnBody (Result.ok ()) tag) crest

private theorem e_fork : cprog = Result.vis forkEv cforked := by
  show Aeneas.Std.bind
      (Aeneas.Std.bind (α := RustEffect.O forkEv)
        (Result.vis (α := RustEffect.O forkEv) forkEv (fun x => Result.ok x))
        (spawnBody (Result.ok ()))) crest = _
  unfold cforked
  simp only [Aeneas.Std.bind_vis, Aeneas.Std.bind_ok]
  rfl

private theorem e_yield :
    cforked ConcE.Tags.cur = Result.vis yieldEv (fun _ => Result.ok ()) := by
  simp [cforked, spawnBody, crest, Conc.yieldU, Conc.yield, trigger_yield_eq,
    itree_bind_eq_std, itree_ret_eq_ok]

private theorem e_endthread :
    cforked ConcE.Tags.new
      = Result.vis endthreadEv (fun o => Aeneas.Std.bind (PEmpty.elim o : Result Unit) crest) := by
  show Aeneas.Std.bind
      (Aeneas.Std.bind (Result.ok () : Result Unit)
        (fun _ => Aeneas.Std.bind (α := RustEffect.O endthreadEv)
          (Result.vis (α := RustEffect.O endthreadEv) endthreadEv (fun x => Result.ok x))
          (fun o => (PEmpty.elim o : Result Unit)))) crest = _
  simp

/-! ### The trace: fork, yield, endthread -/

theorem cprog_mayReturn : MayReturn cprog () := by
  refine ⟨⟨[Thread.alive (Result.ok ()), Thread.dead], 0, (∅ : RustHeap.{0})⟩, ?_, rfl, rfl⟩
  exact .tail (fork1 e_fork)
    (.tail (yield01 e_yield)
      (.tail (endthread10 e_endthread) (.refl _)))

/-! ### What the trace witnesses

Three statements naming the three rules, so that "`Step.fork` fires on a real
program" is a theorem and not an inference from the trace above. -/

/-- **`Step.fork` fires**, and the pool really does grow to two threads. -/
theorem cprog_forks : ∃ c, Reaches (init cprog) c ∧ c.threads.length = 2 :=
  ⟨_, .tail (fork1 e_fork) (.refl _), rfl⟩

/-- **`Step.yield` fires**: the big lock moves from thread `0` to thread `1`. -/
theorem cprog_yields :
    ∃ c, Reaches (init cprog) c ∧ c.current = 1 ∧ c.Alive 1 :=
  ⟨_, .tail (fork1 e_fork) (.tail (yield01 e_yield) (.refl _)), rfl, _, rfl⟩

/-- **`Step.endthread` fires**: the child dies and the lock comes back to the
parent, which is still alive — so this is a handoff, not `KillLastThread`. -/
theorem cprog_endthread :
    ∃ c, Reaches (init cprog) c ∧ c.current = 0 ∧ c.threads[1]? = some Thread.dead :=
  ⟨_, .tail (fork1 e_fork) (.tail (yield01 e_yield)
      (.tail (endthread10 e_endthread) (.refl _))), rfl, rfl⟩

/-! ### Why there is no `wpi` triple for `cprog` here

`prog` gets one (`prog_spec`); `cprog` does not, and the reason is worth
recording rather than hiding.

1. `AeneasIris.Effects.ConcAPI` is **not** reachable from `AeneasIris.Tactics.Core`,
   so with this file's imports `irule` reports
   `no rule is registered for AeneasIris.Conc.spawn` even though `spawn_spec`
   carries `@[istep_rule]`. Adding the import fixes that much.
2. With the import, `irule` then fails at
   `ispecialize: itrivial could not solve … wpi_mask GF ?H ?m (Result.ok ()) (fun _ => True) ⊤`.

Point 2 is the interesting one, and it is the failure mode the tactics skill file
already documents for `stepP`: **`spawn_spec` is registered `.triple`, but its
precondition is not frame-directed.** A `.triple` rule's precondition is meant to
be a *resource* discharged by framing it out of the context; `spawn_spec`'s is
`wpi_mask … t (fun _ => True) ⊤`, i.e. the child's entire weakest precondition,
which no framing step can produce. That is precisely the argument that made
`stepP` a `cont` rule rather than a triple.

So `spawn_spec` looks like it wants `.cont` style too (or a companion rule
stated continuation-passing). Reporting rather than working around it, since the
fix belongs in `ConcAPI.lean`/`Tactics.lean`, which this file does not own. The
machine-side results below need no triple. -/

/-! ### The concurrent capstone -/

/-- **`cprog` returns**, and the schedule that makes it return exercises all
three concurrency rules. The concurrent analogue of `prog_returns_42'`:
no `Terminates`, no `sorry`, no Iris in the statement. -/
theorem cprog_returns : ∃ v, MayReturn cprog v := ⟨(), cprog_mayReturn⟩

end Conc





/-! ## The program really does return `42`

`prog_result` is an implication, so on its own it would say nothing if
`MayReturn prog v` held for no `v` — review finding #3 in miniature. It does
hold: `prog_mayReturn` below builds the six-step execution explicitly, so the
statement is not vacuous and the two hypotheses `prog_returns_42` needs are
discharged outright, with **no appeal to `Terminates`**. -/

/-- **The full statement.** `prog` returns, and what it returns is `42`.

Unconditional: no `Terminates`, no `sorry`, no Iris in the statement. The
`MayReturn` half is the explicit machine trace (`prog_mayReturn`); the `= 42`
half is `prog_result`, which is the `wpi` triple travelling through
`post_of_provable`.

Routing the second component through `prog_result` rather than closing it by
`rfl` is the whole point. `rfl` would prove the same statement — `42 = 42` is
true by computation — but it would prove it *without using the logic at all*,
and this theorem exists precisely to demonstrate that the logic reaches the
machine. A witness that can be discharged by `rfl` witnesses nothing. -/
theorem prog_returns_42' : ∃ v, MayReturn prog v ∧ v = 42 :=
  ⟨42, prog_mayReturn, prog_result 42 prog_mayReturn⟩

/-- Kept for reference: the same conclusion from `Semantics/Outcome.lean`, for a
program whose trace one does *not* want to write out by hand. `prog` no longer
needs it — see `prog_returns_42'`. -/
theorem prog_returns_42 (hT : Terminates prog)
    (hmain : ∀ c, Reaches (init prog) c → c.Produces →
      c.current = 0 ∧ ∃ v, c.focus = some (Result.ok v)) :
    ∃ v, MayReturn prog v ∧ v = 42 := by
  obtain ⟨v, hv⟩ := exists_mayReturn prog_safe hT hmain
  exact ⟨v, hv, prog_result v hv⟩

end AeneasIris.Semantics.Example
