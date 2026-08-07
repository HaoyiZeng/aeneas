import LtStatefulPurityOff
import LtStatefulPurityOn

/-!
# `-stateful-lifetimes` must be inert on code with no stateful lifetimes

`tests/src/lt-stateful-purity-off.rs` and `tests/src/lt-stateful-purity-on.rs`
are byte-identical Rust apart from their translation flags: the first is
translated with `-eval-drops`, the second with `-stateful-lifetimes
-eval-drops`.  Neither carries a single `#[verify::stateful_lifetimes]`
annotation.

A stateful lifetime is a property of an individual region, so turning the flag
on must change **nothing** here.  Each assertion below equates one function
across the two crates; any divergence is a build failure.

At the time these tests were written the flag was *not* inert.  It is a global
mode switch, because:

* `SymbolicToPureAbs.abs_to_ty` uses
  `!Config.stateful_lifetimes || abs_cont_is_monadic ctx abs`, making every loop
  and join continuation `Result`-valued;
* `abs_cont_to_texpr_aux` `ok`-wraps every continuation output for the same
  reason;
* `unit_vars_to_unit`, `simplify_duplicate_calls` and `filter_useless` (twice)
  are disabled wholesale in `PureMicroPasses.passes`.

The observable consequences on this very file were that `duplicate_calls`
translated to `let second ← x + 1; first + second` instead of `first + first`,
and that `merge_let_app_then_decompose_tuple` stopped firing in `use_choose` and
`bump_field`.  Those over-approximations exist only to protect a release that is
emitted as a *pure* application; once the release is monadic they are
unnecessary, and these assertions are what holds the line.
-/

open Aeneas Aeneas.Std Result

/- The generated definitions are noncomputable (they rest on axioms). -/
noncomputable section

namespace LtStatefulPurityCheck

/-! ## Plain mutable borrows -/

example : lt_stateful_purity_on.incr = lt_stateful_purity_off.incr := by rfl

example : lt_stateful_purity_on.unit_result = lt_stateful_purity_off.unit_result := by
  rfl

example : lt_stateful_purity_on.swap_pair = lt_stateful_purity_off.swap_pair := by
  rfl

/-! ## Joins over mutable borrows

`choose_mut` returns a `&mut` chosen by a branch, so its backward function is
built by `abs_to_ty` on a *join* continuation — the path the blanket makes
monadic. -/

example : lt_stateful_purity_on.choose_mut = lt_stateful_purity_off.choose_mut := by
  rfl

/-- The call site, where the continuation type becomes visible. This is one of
the two functions whose translation currently differs. -/
example : lt_stateful_purity_on.use_choose = lt_stateful_purity_off.use_choose := by
  rfl

/-! ## Loops carrying a mutable borrow

`abs_to_ty` is also what types the loop continuation. The body is asserted
separately from the wrapper because it is where the continuation appears. -/

example :
    lt_stateful_purity_on.loop_incr_loop.body
      = lt_stateful_purity_off.loop_incr_loop.body := by
  rfl

example :
    lt_stateful_purity_on.loop_incr_loop = lt_stateful_purity_off.loop_incr_loop := by
  rfl

example : lt_stateful_purity_on.loop_incr = lt_stateful_purity_off.loop_incr := by
  rfl

/-! ## Micro-passes that are currently disabled wholesale -/

/-- `simplify_duplicate_calls`. With the flag on, the two occurrences of `x + 1`
are no longer shared, so this currently translates to
`let second ← x + 1; first + second` rather than `first + first`. -/
example :
    lt_stateful_purity_on.duplicate_calls = lt_stateful_purity_off.duplicate_calls := by
  rfl

/-! ## Nested backward functions -/

example : lt_stateful_purity_on.field_mut = lt_stateful_purity_off.field_mut := by
  rfl

/-- The caller threads `field_mut`'s continuation; the second function whose
translation currently differs. -/
example : lt_stateful_purity_on.bump_field = lt_stateful_purity_off.bump_field := by
  rfl

end LtStatefulPurityCheck

end
