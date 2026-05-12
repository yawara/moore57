import Moore57.D19OnMoore57.Final.LinearFixedEnumerationReflectionBase
import Moore57.D19OnMoore57.AdjacentMoved.ReflectionConstantResidual

/-!
# Final D19 base-selection inputs from fixed enumeration and constant residual

This file combines the fixed-enumeration final input package with the
constant-residual reflection-copy adjacent-moved criterion at the downstream
`OrbitBaseSelectionInput` boundary.
-/

namespace Moore57

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- Final D19 input package using a full linear-character witness, an explicit
rotation-one fixed-point enumeration, a downstream base-selection input, and a
constant-residual reflection-copy adjacent-moved partition. -/
structure D19FinalLinearFixedEnumerationConstantResidualBaseInputs
    (h : D19ActsOnMoore57 V Γ) where
  /-- Full D19 linear-character witness for the trace representation. -/
  linearCharacter : D19ActsOnMoore57.D19LinearCharacterInput h
  /-- Explicit finite cover of the rotation-one fixed vertices. -/
  fixedEnumeration : D19ActsOnMoore57.RotationOneFixedEnumeration h
  /-- Pairwise-disjoint selected moved rotation orbits. -/
  orbitBase : OrbitBaseSelectionInput h
  /-- Constant-residual reflection-copy adjacent-moved partition over the
  selected bases. -/
  adjacentMoved :
    AdjacentMovedReflectionConstantResidual38Witness h orbitBase.base

namespace D19FinalLinearFixedEnumerationConstantResidualBaseInputs

variable {h : D19ActsOnMoore57 V Γ}

/-- Forget the constant-residual presentation to the existing fixed-enumeration,
reflection-copy base-input boundary. -/
noncomputable def toD19FinalLinearFixedEnumerationReflectionBaseInputs
    (data : D19FinalLinearFixedEnumerationConstantResidualBaseInputs h) :
    D19FinalLinearFixedEnumerationReflectionBaseInputs h where
  linearCharacter := data.linearCharacter
  fixedEnumeration := data.fixedEnumeration
  orbitBase := data.orbitBase
  adjacentMoved := data.adjacentMoved.toReflectionCopyPartition38Witness

/-- Forget the constant-residual presentation down to final inputs. -/
noncomputable def toD19FinalInputs
    (data : D19FinalLinearFixedEnumerationConstantResidualBaseInputs h) :
    D19FinalInputs h :=
  data.toD19FinalLinearFixedEnumerationReflectionBaseInputs.toD19FinalInputs

/-- Final linear-character, fixed-enumeration, constant-residual reflection-copy
base inputs cannot exist. -/
theorem not_nonempty (h : D19ActsOnMoore57 V Γ) :
    ¬ Nonempty (D19FinalLinearFixedEnumerationConstantResidualBaseInputs h) := by
  rintro ⟨data⟩
  exact D19FinalLinearFixedEnumerationReflectionBaseInputs.not_nonempty h
    ⟨data.toD19FinalLinearFixedEnumerationReflectionBaseInputs⟩

end D19FinalLinearFixedEnumerationConstantResidualBaseInputs

end Moore57
