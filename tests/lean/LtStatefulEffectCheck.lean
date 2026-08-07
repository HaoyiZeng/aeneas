/-!
# Why a stateful backward function must be `A → T B`, never `T (A → B)`

This file is the *semantic* justification for the shape of stateful backward
functions.  It is deliberately independent of any generated file: it states,
and machine-checks, what goes wrong if the backward value of a stateful
lifetime is emitted as

```
release : T (Guard → Unit)          -- WRONG: effect first, argument later
```

instead of

```
release : Guard → T Unit            -- RIGHT: argument first, effect at application
```

The theorems below are proved over an abstract event-emitting monad `Eff`,
so they apply to *any* effect interpretation, including:

* `Aeneas.Std.Result`, which is already an effect tree
  (`Result α := ITree RustEffect α`, `Primitives.lean`), and
* the ITree/`Comp` interpretation in which lock acquisition and release become
  observable events.

`old_shape_cannot_release` is the key result: it proves that the `T (A → B)`
encoding **cannot** implement a release that names the guard it releases.  Any
separation-logic interface whose release specification is stated about the
*application* `rel guard` — as `Rust.API.MultiShot.RwLockAPI.write_spec` and
`Rust.API.OneShot.RwLockAPI.write_spec` both are — is therefore not
instantiable by the old shape.
-/

namespace LtStatefulEffectCheck

/-! ## A minimal effect monad

`Eff Ev A` is a computation that emits a list of events of type `Ev` and
returns a value of type `A`.  This is the writer-monad shadow of an ITree: it
keeps exactly the structure the argument needs (which events are emitted, and
in which order) and discards everything else. -/

structure Eff (Ev : Type) (A : Type) where
  events : List Ev
  value : A

namespace Eff

instance {Ev : Type} : Monad (Eff Ev) where
  pure a := ⟨[], a⟩
  bind m f := ⟨m.events ++ (f m.value).events, (f m.value).value⟩

@[simp] theorem events_pure {Ev A : Type} (a : A) :
    (pure a : Eff Ev A).events = [] := rfl

@[simp] theorem value_pure {Ev A : Type} (a : A) :
    (pure a : Eff Ev A).value = a := rfl

@[simp] theorem events_bind {Ev A B : Type} (m : Eff Ev A) (f : A → Eff Ev B) :
    (m >>= f).events = m.events ++ (f m.value).events := rfl

@[simp] theorem value_bind {Ev A B : Type} (m : Eff Ev A) (f : A → Eff Ev B) :
    (m >>= f).value = (f m.value).value := rfl

/-- Emit one event. -/
def emit {Ev : Type} (e : Ev) : Eff Ev Unit := ⟨[e], ()⟩

@[simp] theorem events_emit {Ev : Type} (e : Ev) : (emit e).events = [e] := rfl

end Eff

/-- The event a lock release is supposed to emit.  It *names the guard being
released*; that is the whole point — a handler that cannot tell which guard was
released cannot release the corresponding lock. -/
inductive Event (G : Type) where
  | released : G → Event G
deriving DecidableEq

/-! ## The old shape `T (A → B)` -/

/-- **The old shape is blind.**

With `release : T (Guard → B)` the events are produced by `release` itself,
which is consumed by a bind *before* the guard is available.  Applying the
resulting function is a pure step and emits nothing.  Hence the emitted events
are literally the same no matter which guard is supplied.

This is exactly the code Aeneas currently generates:
```
let stateful_back1 ← stateful_back   -- events happen here, guard unknown
let () := stateful_back1 guard       -- guard supplied here, no events
```
-/
theorem old_shape_events_independent_of_guard
    {Ev G B : Type} (release : Eff Ev (G → B)) (g₁ g₂ : G) :
    (release >>= fun k => pure (k g₁)).events
      = (release >>= fun k => pure (k g₂)).events := by
  simp

/-- **The old shape cannot implement a lock release.**

There is no `T (Guard → B)` value whose events name the guard it is applied to,
as soon as two distinct guards exist.  Consequently the current Aeneas output
cannot be given the release specification of `MultiShot.RwLockAPI.write_spec`,
which requires the release of `g` to take the lock from `.write` to `.free`
*with `g`'s final value*. -/
theorem old_shape_cannot_release
    {G B : Type} (g₁ g₂ : G) (hne : g₁ ≠ g₂) :
    ¬ ∃ release : Eff (Event G) (G → B),
        ∀ g, (release >>= fun k => pure (k g)).events = [Event.released g] := by
  rintro ⟨release, h⟩
  have hsame : [Event.released g₁] = [Event.released g₂] := by
    rw [← h g₁, ← h g₂]
    exact old_shape_events_independent_of_guard release g₁ g₂
  simp only [List.cons.injEq, Event.released.injEq, and_true] at hsame
  exact hne hsame

/-- **The old shape does not enforce guard/lock pairing.**

Two releases and two guards: swapping which guard is handed to which release
changes nothing observable.  A model built on this encoding cannot distinguish
"release lock 1 with guard 1, lock 2 with guard 2" from the crossed pairing. -/
theorem old_shape_pairing_unenforced
    {Ev G B : Type} (r₁ r₂ : Eff Ev (G → B)) (g₁ g₂ : G) :
    (do let k₁ ← r₁; let k₂ ← r₂; pure (k₁ g₁, k₂ g₂)).events
      = (do let k₁ ← r₁; let k₂ ← r₂; pure (k₁ g₂, k₂ g₁)).events := by
  simp

/-! ## The new shape `A → T B` -/

/-- **The new shape can implement a lock release**, and does so exactly. -/
theorem new_shape_can_release {G : Type} :
    ∃ release : G → Eff (Event G) Unit,
      ∀ g, (release g).events = [Event.released g] :=
  ⟨fun g => Eff.emit (Event.released g), fun _ => rfl⟩

/-- **The new shape distinguishes guards**, which is precisely the property
`old_shape_events_independent_of_guard` shows the old shape lacks. -/
theorem new_shape_events_depend_on_guard
    {G : Type} (g₁ g₂ : G) (hne : g₁ ≠ g₂) :
    ∃ release : G → Eff (Event G) Unit,
      (release g₁).events ≠ (release g₂).events := by
  refine ⟨fun g => Eff.emit (Event.released g), ?_⟩
  simp only [Eff.events_emit, ne_eq, List.cons.injEq, Event.released.injEq,
    and_true]
  exact hne

/-- **The new shape enforces guard/lock pairing**: crossing the guards is
observable, so a proof obligation can rule it out. -/
theorem new_shape_pairing_enforced
    {G : Type} (g₁ g₂ : G) (hne : g₁ ≠ g₂) :
    ∃ release : G → Eff (Event G) Unit,
      (do let _ ← release g₁; release g₂).events
        ≠ (do let _ ← release g₂; release g₁).events := by
  refine ⟨fun g => Eff.emit (Event.released g), ?_⟩
  simp only [Eff.events_bind, Eff.events_emit, ne_eq,
    List.cons_append, List.nil_append, List.cons.injEq,
    Event.released.injEq, and_true]
  intro hcontra
  exact hne hcontra.1

/-! ## Corollary: the two shapes are not interchangeable

`T (A → B)` can always be *weakened* into `A → T B` (bind, then apply), which
is why the wrong shape still typechecks and why the mistake is easy to miss.
The converse fails, and the theorems above say why: the weakening direction
throws away the dependency of the effects on the argument. -/

/-- The old shape can be coerced into the new one — this is what makes the bug
silent — but by `old_shape_events_independent_of_guard` the result never uses
its argument to decide what to emit. -/
def weaken {Ev G B : Type} (release : Eff Ev (G → B)) : G → Eff Ev B :=
  fun g => release >>= fun k => pure (k g)

theorem weaken_events_constant
    {Ev G B : Type} (release : Eff Ev (G → B)) (g₁ g₂ : G) :
    (weaken release g₁).events = (weaken release g₂).events :=
  old_shape_events_independent_of_guard release g₁ g₂

/-- And so no coercion of an old-shape value can meet the release
specification: `weaken` can never produce `new_shape_can_release`'s witness. -/
theorem weaken_cannot_release
    {G B : Type} (g₁ g₂ : G) (hne : g₁ ≠ g₂) (release : Eff (Event G) (G → B)) :
    ¬ ∀ g, (weaken release g).events = [Event.released g] := by
  intro h
  exact old_shape_cannot_release g₁ g₂ hne ⟨release, h⟩

end LtStatefulEffectCheck
