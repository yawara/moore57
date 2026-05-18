import Lean
import Moore57.Phases.FinalAssembly
import Moore57.Order22OnMoore57.NoGo
import Moore57.Order22OnMoore57.GroupAction

/-!
# Axioms check for the main theorem

This file asserts at elaboration time that the main theorem
`Moore57.no_D19_acts_on_Moore57_unconditional` depends only on axioms in a
fixed allowlist:

* Lean / Mathlib standard axioms: `propext`, `Classical.choice`, `Quot.sound`.
* Compiler-generated `native_decide` axioms (names containing
  `._native.native_decide.ax_`), used for ZMod-19 numeric decision procedures.

Any other axiom — including `sorryAx` (from `sorry`), user-defined `axiom`
declarations, or `Lean.ofReduceBool` outside the allowed pattern — causes
elaboration of this file to fail, which in turn fails `lake build`.

This is the CI guarantee that the proof is unconditional.
-/

open Lean Elab Command

namespace Moore57.AxiomsCheck

/-- Axioms that ship with Lean / Mathlib and are accepted by convention. -/
def allowedStandard : List Name := [``propext, ``Classical.choice, ``Quot.sound]

/-- A name is a `native_decide`-generated axiom iff its string representation
contains the marker `._native.native_decide.ax_`. -/
def isNativeDecideAxiom (n : Name) : Bool :=
  (n.toString.splitOn "._native.native_decide.ax_").length == 2

def isAllowed (n : Name) : Bool :=
  allowedStandard.contains n || isNativeDecideAxiom n

end Moore57.AxiomsCheck

/-- Assert that the given constant depends only on allowlisted axioms.
Fails elaboration (and therefore `lake build`) if any axiom outside the
allowlist appears in its dependency closure. -/
elab "#assert_only_allowed_axioms " name:ident : command => do
  let constName := name.getId
  let env ← getEnv
  unless env.contains constName do
    throwError m!"axioms check: constant `{constName}` not found"
  let axs ← liftCoreM <| Lean.collectAxioms constName
  let bad := axs.filter (fun a => !Moore57.AxiomsCheck.isAllowed a)
  if bad.isEmpty then
    logInfo m!"axioms check OK: `{constName}` depends on {axs.size} axiom(s), all in allowlist"
  else
    throwError m!"axioms check FAILED: `{constName}` depends on {bad.size} \
disallowed axiom(s):{indentD m!"{bad.toList}"}"

#assert_only_allowed_axioms Moore57.no_D19_acts_on_Moore57_unconditional
#assert_only_allowed_axioms Moore57.no_C38_acts_on_Moore57_unconditional
#assert_only_allowed_axioms Moore57.Moore57_no_order38_structure
#assert_only_allowed_axioms Moore57.no_Order22_acts_on_Moore57
#assert_only_allowed_axioms Moore57.no_Order22_group_acts_on_Moore57
#assert_only_allowed_axioms Moore57.no_Order110_group_acts_on_Moore57
