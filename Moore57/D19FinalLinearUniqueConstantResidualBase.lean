import Moore57.D19FinalLinearUniqueReflectionBase
import Moore57.AdjacentMovedReflectionConstantResidual

/-!
# Final D19 base-selection inputs from unique fixed point and constant residual

This file combines the unique-fixed linear-character input package with the
constant-residual reflection-copy adjacent-moved criterion at the downstream
`OrbitBaseSelectionInput` boundary.
-/

namespace Moore57

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- Final D19 input package using a full linear-character witness, a unique
rotation-one fixed point, downstream base-selection input, and a
constant-residual reflection-copy adjacent-moved partition. -/
structure D19FinalLinearUniqueConstantResidualBaseInputs
    (h : D19ActsOnMoore57 V Γ) where
  /-- Full D19 linear-character witness for the trace representation. -/
  linearCharacter : D19ActsOnMoore57.D19LinearCharacterInput h
  /-- Rotation by `1` has a unique fixed vertex. -/
  rotationOne_unique_fixed : ∃! v : V, h.rotation 1 v = v
  /-- Pairwise-disjoint selected moved rotation orbits. -/
  orbitBase : OrbitBaseSelectionInput h
  /-- Constant-residual reflection-copy adjacent-moved partition over the
  selected bases. -/
  adjacentMoved :
    AdjacentMovedReflectionConstantResidual38Witness h orbitBase.base

namespace D19FinalLinearUniqueConstantResidualBaseInputs

variable {h : D19ActsOnMoore57 V Γ}

/-- Forget the constant-residual presentation to the existing unique-fixed,
reflection-copy base-input boundary. -/
noncomputable def toD19FinalLinearUniqueReflectionBaseInputs
    (data : D19FinalLinearUniqueConstantResidualBaseInputs h) :
    D19FinalLinearUniqueReflectionBaseInputs h where
  linearCharacter := data.linearCharacter
  rotationOne_unique_fixed := data.rotationOne_unique_fixed
  orbitBase := data.orbitBase
  adjacentMoved := data.adjacentMoved.toReflectionCopyPartition38Witness

/-- Forget the constant-residual presentation down to final inputs. -/
noncomputable def toD19FinalInputs
    (data : D19FinalLinearUniqueConstantResidualBaseInputs h) :
    D19FinalInputs h :=
  data.toD19FinalLinearUniqueReflectionBaseInputs.toD19FinalInputs

/-- Final linear-character, unique-fixed, constant-residual reflection-copy
base inputs cannot exist. -/
theorem not_nonempty (h : D19ActsOnMoore57 V Γ) :
    ¬ Nonempty (D19FinalLinearUniqueConstantResidualBaseInputs h) := by
  rintro ⟨data⟩
  exact D19FinalLinearUniqueReflectionBaseInputs.not_nonempty h
    ⟨data.toD19FinalLinearUniqueReflectionBaseInputs⟩

end D19FinalLinearUniqueConstantResidualBaseInputs

end Moore57
