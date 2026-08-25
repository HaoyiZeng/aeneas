/- Ordered maps -/
import Aeneas.Std.Scalar
import Aeneas.Std.Core.Cmp
import Aeneas.Tactic.Solver.ScalarTac
import Aeneas.Tactic.Step.Init
import Aeneas.Std.WP

namespace Aeneas

namespace Std

open Result Error WP

/-!
# `BTreeMap`

An ordered key/value map, modelling `std::collections::BTreeMap`.

Only the operations a client has needed so far are here: `new`, `get`,
`contains_key`, `insert`, `remove` and `pop_first`.  No iterators, no ranges, no
entry API.  Add them when something calls them.

## Shape

The carrier is an association list kept sorted by key with no duplicates.  That
is a model, not the B-tree: what a caller can observe of a `BTreeMap` is the
mapping and the order of iteration, and a sorted list has both.

## Comparison is monadic

Rust compares through `Ord::cmp`, which Aeneas gives as
`cmp : K → K → Result Ordering` -- it may fail.  Every lookup is therefore a
monadic recursion rather than a `List.find?`, and the specs below are stated
against a `cmp` that behaves (`LawfulCmp`).  For the scalar keys that occur in
practice the instance is `Aeneas.Std.UScalar`'s, which satisfies it.

## Not yet registered with `@[rust_fun]`

The name patterns depend on whether a client uses `std::collections::BTreeMap`
directly or a model of it, and the two spell the path differently.  Until that is
settled the definitions are reachable by hand, which is what a `FunsExternal`
forwarder does.
-/

namespace alloc.collections.btree.map

/-- An ordered key/value map: the pairs, sorted by key, without duplicates. -/
structure BTreeMap (K : Type) (V : Type) where
  val : List (K × V)

@[simp, scalar_tac_simps, simp_lists_safe, grind, agrind]
abbrev BTreeMap.length {K V} (m : BTreeMap K V) : Nat := m.val.length

@[simp, scalar_tac_simps, simp_lists_safe, grind, agrind]
abbrev BTreeMap.keys {K V} (m : BTreeMap K V) : List K := m.val.map Prod.fst

instance {K V} : Inhabited (BTreeMap K V) := ⟨⟨[]⟩⟩

theorem BTreeMap.eq_iff {K V} (m0 m1 : BTreeMap K V) : m0 = m1 ↔ m0.val = m1.val := by
  cases m0; cases m1; simp

/-! ## Construction -/

def BTreeMap.new (K : Type) (V : Type) : Result (BTreeMap K V) := ok ⟨[]⟩

@[step]
theorem BTreeMap.new_spec (K V : Type) :
  BTreeMap.new K V ⦃ (m : BTreeMap K V) => m.val = [] ⦄ := by
  simp [BTreeMap.new]

def BTreeMap.default (K : Type) (V : Type) : Result (BTreeMap K V) :=
  BTreeMap.new K V

@[step]
theorem BTreeMap.default_spec (K V : Type) :
  BTreeMap.default K V ⦃ (m : BTreeMap K V) => m.val = [] ⦄ := by
  simp [BTreeMap.default, BTreeMap.new]

/-! ## `pop_first`

The one operation that needs no comparison: the list is sorted, so the first
entry is the smallest. -/

def BTreeMap.pop_first {K V} (m : BTreeMap K V) :
    Result ((Option (K × V)) × (BTreeMap K V)) :=
  match m.val with
  | [] => ok (none, m)
  | e :: t => ok (some e, ⟨t⟩)

@[step]
theorem BTreeMap.pop_first_spec {K V} (m : BTreeMap K V) :
  BTreeMap.pop_first m ⦃ (o : Option (K × V)) (m1 : BTreeMap K V) =>
    o = m.val.head? ∧ m1.val = m.val.tail ⦄ := by
  unfold BTreeMap.pop_first
  cases h : m.val <;> simp [h]

/-! ## Lookup and update

Each walks the list once, comparing keys.  Sortedness means the walk may stop as
soon as it passes the key: `lt` at position `i` implies the key is absent. -/

def BTreeMap.getAux {K V} (cmp : K → K → Result Ordering)
    (l : List (K × V)) (k : K) : Result (Option V) :=
  match l with
  | [] => ok none
  | (k', v') :: t => do
    let o ← cmp k k'
    match o with
    | .eq => ok (some v')
    | .lt => ok none
    | .gt => BTreeMap.getAux cmp t k

def BTreeMap.get {K V} (inst : core.cmp.Ord K) (m : BTreeMap K V) (k : K) :
    Result (Option V) :=
  BTreeMap.getAux inst.cmp m.val k

def BTreeMap.contains_key {K V} (inst : core.cmp.Ord K) (m : BTreeMap K V)
    (k : K) : Result Bool := do
  let o ← BTreeMap.get inst m k
  ok o.isSome

/-- Insert, keeping the list sorted; returns the value that was displaced. -/
def BTreeMap.insertAux {K V} (cmp : K → K → Result Ordering)
    (l : List (K × V)) (k : K) (v : V) : Result ((Option V) × List (K × V)) :=
  match l with
  | [] => ok (none, [(k, v)])
  | (k', v') :: t => do
    let o ← cmp k k'
    match o with
    | .eq => ok (some v', (k, v) :: t)
    | .lt => ok (none, (k, v) :: (k', v') :: t)
    | .gt => do
      let (old, t') ← BTreeMap.insertAux cmp t k v
      ok (old, (k', v') :: t')

def BTreeMap.insert {K V} (inst : core.cmp.Ord K) (m : BTreeMap K V)
    (k : K) (v : V) : Result ((Option V) × (BTreeMap K V)) := do
  let (old, l) ← BTreeMap.insertAux inst.cmp m.val k v
  ok (old, ⟨l⟩)

/-- Remove, returning the value that was there. -/
def BTreeMap.removeAux {K V} (cmp : K → K → Result Ordering)
    (l : List (K × V)) (k : K) : Result ((Option V) × List (K × V)) :=
  match l with
  | [] => ok (none, [])
  | (k', v') :: t => do
    let o ← cmp k k'
    match o with
    | .eq => ok (some v', t)
    | .lt => ok (none, (k', v') :: t)
    | .gt => do
      let (old, t') ← BTreeMap.removeAux cmp t k
      ok (old, (k', v') :: t')

def BTreeMap.remove {K V} (inst : core.cmp.Ord K) (m : BTreeMap K V) (k : K) :
    Result ((Option V) × (BTreeMap K V)) := do
  let (old, l) ← BTreeMap.removeAux inst.cmp m.val k
  ok (old, ⟨l⟩)

/-! ## What the specs assume of `cmp`

`Ord::cmp` is a Rust method: it may fail, and nothing in its type says it
decides equality or is transitive.  The specs below take that as a hypothesis.
It is a property of the key type's instance, discharged once per key type, not
per call site. -/

/-- `cmp` succeeds everywhere and decides equality. -/
structure LawfulCmp {K : Type} (cmp : K → K → Result Ordering) : Prop where
  total : ∀ k k', ∃ o, cmp k k' = ok o
  eq_iff : ∀ k k', cmp k k' = ok .eq ↔ k = k'

/-! ### `get` -/

theorem BTreeMap.getAux_nil {K V} (cmp : K → K → Result Ordering) (k : K) :
  BTreeMap.getAux (V := V) cmp [] k = ok none := by simp [BTreeMap.getAux]

@[step]
theorem BTreeMap.getAux_cons_eq_spec {K V} (cmp : K → K → Result Ordering)
    (k k' : K) (v' : V) (t : List (K × V)) (h : cmp k k' = ok .eq) :
  BTreeMap.getAux cmp ((k', v') :: t) k ⦃ (o : Option V) => o = some v' ⦄ := by
  simp [BTreeMap.getAux, h]

@[step]
theorem BTreeMap.getAux_cons_lt_spec {K V} (cmp : K → K → Result Ordering)
    (k k' : K) (v' : V) (t : List (K × V)) (h : cmp k k' = ok .lt) :
  BTreeMap.getAux cmp ((k', v') :: t) k ⦃ (o : Option V) => o = none ⦄ := by
  simp [BTreeMap.getAux, h]

/-- Past the head, the walk is the walk on the tail. -/
theorem BTreeMap.getAux_cons_gt {K V} (cmp : K → K → Result Ordering)
    (k k' : K) (v' : V) (t : List (K × V)) (h : cmp k k' = ok .gt) :
  BTreeMap.getAux cmp ((k', v') :: t) k = BTreeMap.getAux cmp t k := by
  simp [BTreeMap.getAux, h]

/-- On an empty map the answer is `none`, whatever the comparison does. -/
@[step]
theorem BTreeMap.get_nil_spec {K V} (inst : core.cmp.Ord K) (m : BTreeMap K V)
    (k : K) (h : m.val = []) :
  BTreeMap.get inst m k ⦃ (o : Option V) => o = none ⦄ := by
  simp [BTreeMap.get, h, BTreeMap.getAux]

/-! ### `insert` and `remove`

TODO: the length bounds -- `insert` keeps the length or adds one, `remove` never
grows it.  Both are inductions over the list whose step has to case on the
recursive call's `Result`, which `split` will not do through the bind.  A caller
draining a map uses `pop_first`, whose spec is above and needs no comparison, so
nothing needs them yet. -/

end alloc.collections.btree.map

end Std

end Aeneas
