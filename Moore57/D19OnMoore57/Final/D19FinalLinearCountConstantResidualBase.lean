import Moore57.D19OnMoore57.Final.D19FinalLinearCountReflectionBase
import Moore57.D19OnMoore57.AdjacentMoved.AdjacentMovedReflectionConstantResidual

/-!
# Final D19 base-selection inputs from exact fixed count and constant residual

This file combines the exact fixed count and constant-residual
reflection-copy package with the weaker downstream `OrbitBaseSelectionInput`
boundary.
-/

namespace Moore57

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- Final D19 input package using a full linear-character witness, exact
rotation-one fixed count, downstream base-selection input, and a
constant-residual reflection-copy adjacent-moved partition. -/
structure D19FinalLinearCountConstantResidualBaseInputs
    (h : D19ActsOnMoore57 V Γ) where
  /-- Full D19 linear-character witness for the trace representation. -/
  linearCharacter : D19ActsOnMoore57.D19LinearCharacterInput h
  /-- Rotation by `1` has exactly one fixed vertex. -/
  rotationOne_fixed_count : fixedVertexCount (h.rotation 1) = 1
  /-- Pairwise-disjoint selected moved rotation orbits. -/
  orbitBase : OrbitBaseSelectionInput h
  /-- Constant-residual reflection-copy adjacent-moved partition over the
  selected bases. -/
  adjacentMoved :
    AdjacentMovedReflectionConstantResidual38Witness h orbitBase.base

namespace D19FinalLinearCountConstantResidualBaseInputs

variable {h : D19ActsOnMoore57 V Γ}

/-- Forget the constant-residual presentation to the existing exact-count,
reflection-copy base-input boundary. -/
noncomputable def toD19FinalLinearCountReflectionBaseInputs
    (data : D19FinalLinearCountConstantResidualBaseInputs h) :
    D19FinalLinearCountReflectionBaseInputs h where
  linearCharacter := data.linearCharacter
  rotationOne_fixed_count := data.rotationOne_fixed_count
  orbitBase := data.orbitBase
  adjacentMoved := data.adjacentMoved.toReflectionCopyPartition38Witness

/-- Forget the constant-residual and exact-count presentations down to final
inputs. -/
noncomputable def toD19FinalInputs
    (data : D19FinalLinearCountConstantResidualBaseInputs h) :
    D19FinalInputs h :=
  data.toD19FinalLinearCountReflectionBaseInputs.toD19FinalInputs

/-- Cardinality-one fixed set variant of the exact-count input constructor. -/
noncomputable def of_fixedVertexSet_card_eq_one
    (linearCharacter : D19ActsOnMoore57.D19LinearCharacterInput h)
    (rotationOne_fixed_card :
      Fintype.card (fixedVertexSet (h.rotation 1)) = 1)
    (orbitBase : OrbitBaseSelectionInput h)
    (adjacentMoved :
      AdjacentMovedReflectionConstantResidual38Witness h orbitBase.base) :
    D19FinalLinearCountConstantResidualBaseInputs h where
  linearCharacter := linearCharacter
  rotationOne_fixed_count := by
    simpa [fixedVertexCount_eq_card_fixedVertexSet] using rotationOne_fixed_card
  orbitBase := orbitBase
  adjacentMoved := adjacentMoved

/-- Final linear-character, exact-count, constant-residual reflection-copy
base inputs cannot exist. -/
theorem not_nonempty (h : D19ActsOnMoore57 V Γ) :
    ¬ Nonempty (D19FinalLinearCountConstantResidualBaseInputs h) := by
  rintro ⟨data⟩
  exact D19FinalLinearCountReflectionBaseInputs.not_nonempty h
    ⟨data.toD19FinalLinearCountReflectionBaseInputs⟩

end D19FinalLinearCountConstantResidualBaseInputs

end Moore57
