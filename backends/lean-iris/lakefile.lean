import Lake
open Lake DSL

/-!
The Iris-backed program logic for Aeneas ITrees.

This is a **separate package**, not a library inside `aeneas`, and that is
deliberate: Lake resolves dependencies per *package*, so a `require iris` in the
`aeneas` package would force every downstream user — including `tests/lean` — to
resolve iris-lean, whether or not they import a single Iris module. Keeping the
split at package granularity means `tests/lean` continues to depend on `aeneas`
alone.

Effect *signatures* (`FailE`, `StateE`, `ConcE`, `StepE`) are plain ITree
definitions and belong on the `aeneas` side; only their *handlers* and the
weakest precondition need Iris and live here.
-/

require aeneas from "../lean"
require iris from "../../../iris-lean/Iris"

package «aeneas-iris» where

@[default_target] lean_lib «AeneasIris» {}
