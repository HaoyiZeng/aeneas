import AeneasIris.RwLock
import AeneasIris.Tactics
import AeneasIris.AtomicWpi

/-!
# Logically atomic specs for `RwLock`, and what the yields cost

Now that every synchronisation operation begins with a `yield` (`ConcE.sync`),
can an invariant still be opened at a linearisation point — and can a client
still commit an atomic update there?

Yes, and the reason is that the mask discipline is *not* uniform:

| rule                                   | mask     |
|----------------------------------------|----------|
| `wpi_bind`                             | any `M`  |
| `wpi_load` / `wpi_store` / `wpi_cas_*` | any `M`  |
| `wpi_yieldU`                           | `⊤` only |

So "may I open an invariant here?" is exactly "is there a `yield` between here
and where I close it?". A linearisation point is a single event — the CAS
inside `try_write` — and no `yield` sits next to it, so the client's atomic
update can be committed there. `wpi_clear_mask` is a biconditional with **no**
`Atomic` side condition (`Rules.lean:642`) precisely because every event in an
ITree is one node, which is what makes this work.

What the yields *do* rule out is holding an invariant open **across** an
acquire. That is the deadlock-prone pattern — the thread that would restore the
invariant is itself waiting for the lock — so ruling it out is the point, not a
cost. The specs below say exactly this: `try_write` is stated at an arbitrary
mask, `write_acquire` at `⊤`.

The updates use `AeneasIris.AtomicP`, which admits any number of binders per
side. That is why these specs can say `isRwLock γ lk s v` -- with a single
binder per side the state and the value have to be packed by hand into one
variable, and every occurrence reads `sv.1` / `sv.2`. The same goes for `write`
and `read`, whose results are a guard *and* a release function.
-/

namespace AeneasIris.RwLockLAT

open Iris BI Aeneas.Data.Coinductive
open AeneasIris AeneasIris.Heap AeneasIris.HeapAPI
open Aeneas.Std (StateE StepE Loc RustHeap RustEffect Result)
open AeneasIris.RwLock
open AeneasIris.AtomicP AeneasIris.AtomicWpi


section

variable {GF : BundledGFunctors} [Iris.InvGS_gen hlc GF] [HeapGS.{0} GF] [RwSpinG GF]
variable {T : Type} [Nonempty T]

abbrev RH (GF : BundledGFunctors) [Iris.InvGS_gen hlc GF] [HeapGS.{0} GF] :
    Handler RustEffect GF := AeneasIris.RustHandler.rustH .later


/-! ## Allocation -/

/-- **`new`.** Mirrors `new_spec`: the lock starts free, holding `v`. -/
theorem new_spec (v : T) (Φ : Post GF (Handle T)) :
    iprop(∀ γ lk, isRwLock γ lk .free v -∗ Φ lk)
      ⊢ wpi_mask GF (RH GF) (new (E := RustEffect) v) (fun lk => Φ lk) ⊤ := by
  sorry

/-! ## Write -/

/-- **`try_write`.** Mirrors `try_write_spec`.

The postcondition is a function of the state the attempt *observed*: on `free`
the lock moves to `write` and the caller receives the guard; on any other state
nothing changes and the result is `none`. That the failing branch leaves
`isRwLock` untouched is what lets the enclosing loop abort and retry. -/
theorem try_write_spec (γ : GName) (lk : Handle T)
    (Φ : Post GF (Option (WriteGuard T))) :
    iprop(AU ⟪ ∃ s v, isRwLock γ lk s v ⟫ @ (⊤ : CoPset), (∅ : CoPset)
            ⟪ ∀ r,
                (isRwLock γ lk (if s = .free then .write else s) v ∗
                 (if s = .free then iprop(⌜r = some ⟨lk⟩⌝ ∗ writeGuard γ lk v)
                  else iprop(⌜r = none⌝))),
              COMM Φ r ⟫)
      ⊢ wpi_mask GF (RH GF) (try_write (E := RustEffect) lk) (fun r => Φ r) ⊤ := by
  sorry

/-- **`write`.** Mirrors `write_spec`.

`⌜s = .free⌝` sits in the *post*, not the pre: the operation may be called in
any state, and the update is committed at the instant the lock is free. That is
what "it blocked" means -- putting `.free` in the precondition would restrict the
spec to the uncontended case and make the retry loop pointless.

The release comes back under `□` as a nested atomic triple, mirroring the
reference's `□ (∀ v₁, writeGuard γ l v₁ -∗ ⟪…⟫ hl(&rel &l) @ ∅ ⟪…⟫)`. The `∀ v₁`
allows releasing a value different from the one acquired; the inner `∃ v₀`
absorbs whatever the lock held. -/
theorem write_spec (γ : GName) (lk : Handle T)
    (Φ : Post GF (WriteGuard T × (WriteGuard T → ITree RustEffect Unit))) :
    iprop(AU ⟪ ∃ s v, isRwLock γ lk s v ⟫ @ (⊤ : CoPset), (∅ : CoPset)
            ⟪ ∀ g rel,
                (isRwLock γ lk .write v ∗ ⌜s = .free⌝ ∗
                 ⌜g = ⟨lk⟩⌝ ∗ writeGuard γ lk v ∗
                 □ (∀ v₁ : T, writeGuard γ lk v₁ -∗
                      (AU ⟪ ∃ v₀, isRwLock γ lk .write v₀ ⟫
                             @ (⊤ : CoPset), (∅ : CoPset)
                           ⟪ isRwLock γ lk .free v₁, COMM True ⟫) -∗
                      wpi_mask GF (RH GF) (rel g) (fun _u => iprop(True)) ⊤)),
              COMM Φ (g, rel) ⟫)
      ⊢ wpi_mask GF (RH GF) (write (E := RustEffect) lk) (fun gr => Φ gr) ⊤ := by
  sorry

/-! ## Read

Same shape, with the reader count doing the work `free`/`write` does above:
`free` becomes `read 0` and `read n` becomes `read (n+1)`. -/

/-- **`try_read`.** Mirrors `try_read_spec`. -/
theorem try_read_spec (γ : GName) (lk : Handle T)
    (Φ : Post GF (Option (ReadGuard T))) :
    iprop(AU ⟪ ∃ s v, isRwLock γ lk s v ⟫ @ (⊤ : CoPset), (∅ : CoPset)
            ⟪ ∀ r,
                (isRwLock γ lk (match s with
                                | .free => .read 0
                                | .read n => .read (n + 1)
                                | .write => .write) v ∗
                 (if s = .write then iprop(⌜r = none⌝)
                  else iprop(⌜r = some ⟨lk⟩⌝ ∗ readGuardFrac γ lk 1 v))),
              COMM Φ r ⟫)
      ⊢ wpi_mask GF (RH GF) (try_read (E := RustEffect) lk) (fun r => Φ r) ⊤ := by
  sorry

/-- **`read`.** Mirrors `read_spec`.

The post is a disjunction because the reference's is. Unlike `write` there is no
`⌜s = .free⌝`: a reader waits only for the absence of a writer. -/
theorem read_spec (γ : GName) (lk : Handle T)
    (Φ : Post GF (ReadGuard T × (ReadGuard T → ITree RustEffect Unit))) :
    iprop(AU ⟪ ∃ s v, isRwLock γ lk s v ⟫ @ (⊤ : CoPset), (∅ : CoPset)
            ⟪ ∀ g rel,
                (((isRwLock γ lk (.read 0) v ∗ ⌜s = .free⌝) ∨
                  (∃ m : Nat, isRwLock γ lk (.read (m + 1)) v ∗ ⌜s = .read m⌝)) ∗
                 ⌜g = ⟨lk⟩⌝ ∗ readGuardFrac γ lk 1 v ∗
                 □ (readGuardFrac γ lk 1 v -∗
                      (AU ⟪ ∃ s', isRwLock γ lk s' v ⟫
                             @ (⊤ : CoPset), (∅ : CoPset)
                           ⟪ ((isRwLock γ lk .free v ∗ ⌜s' = .read 0⌝) ∨
                              (∃ n : Nat, isRwLock γ lk (.read n) v ∗
                                          ⌜s' = .read (n + 1)⌝)),
                             COMM True ⟫) -∗
                      wpi_mask GF (RH GF) (rel g) (fun _u => iprop(True)) ⊤)),
              COMM Φ (g, rel) ⟫)
      ⊢ wpi_mask GF (RH GF) (read (E := RustEffect) lk) (fun gr => Φ gr) ⊤ := by
  sorry

/-! ## Dereference

Plain Hoare triples: a guard is already exclusive (write) or fractional (read),
so no atomic update is involved. -/

/-- **`write_deref`.** -/
theorem write_deref_spec (γ : GName) (g : WriteGuard T) (v : T) (Φ : Post GF T) :
    iprop(writeGuard γ g.lock v ∗ (writeGuard γ g.lock v -∗ Φ v))
      ⊢ wpi_mask GF (RH GF) (write_deref (E := RustEffect) g) (fun r => Φ r) ⊤ := by
  sorry

/-- **`read_deref`.** -/
theorem read_deref_spec (γ : GName) (g : ReadGuard T) (q : Qp) (v : T)
    (Φ : Post GF T) :
    iprop(readGuardFrac γ g.lock q v ∗ (readGuardFrac γ g.lock q v -∗ Φ v))
      ⊢ wpi_mask GF (RH GF) (read_deref (E := RustEffect) g) (fun r => Φ r) ⊤ := by
  sorry

end

end AeneasIris.RwLockLAT
