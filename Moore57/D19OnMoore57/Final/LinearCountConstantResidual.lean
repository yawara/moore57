import Moore57.D19OnMoore57.Final.LinearUniqueReflection
import Moore57.D19OnMoore57.AdjacentMoved.ReflectionConstantResidual
import Moore57.D19OnMoore57.Rotation.FixedCountUnique

/-!
# Final D19 inputs from exact fixed count and constant residual

This file packages the final contradiction input where the linear-character
side is paired with the exact count `fixedVertexCount (h.rotation 1) = 1`,
and the adjacent-moved side is supplied by the constant-residual
reflection-copy criterion.
-/

namespace Moore57

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- Final D19 input package using the linear-character criterion, exact
rotation-one fixed count `1`, an orbit-base enumeration, and the
constant-residual reflection-copy adjacent-moved partition. -/
structure D19FinalLinearCountConstantResidualInputs
    (h : D19ActsOnMoore57 V Γ) where
  /-- Full D19 linear-character witness for the trace representation. -/
  linearCharacter : D19ActsOnMoore57.D19LinearCharacterInput h
  /-- Rotation by `1` fixes exactly one vertex. -/
  rotationOne_fixed_count : fixedVertexCount (h.rotation 1) = 1
  /-- Constructive enumeration of the selected 56 moved rotation orbits. -/
  orbitBase : OrbitBaseSelectionEnumeration h
  /-- Constant-residual reflection-copy adjacent-moved partition over the
  selected bases. -/
  adjacentMoved :
    AdjacentMovedReflectionConstantResidual38Witness h orbitBase.base

namespace D19FinalLinearCountConstantResidualInputs

variable {h : D19ActsOnMoore57 V Γ}

/-- Convert exact count and constant-residual data to the existing
linear-character, unique-fixed, reflection-copy final boundary. -/
noncomputable def toD19FinalLinearUniqueReflectionInputs
    (data : D19FinalLinearCountConstantResidualInputs h) :
    D19FinalLinearUniqueReflectionInputs h where
  linearCharacter := data.linearCharacter
  rotationOne_unique_fixed :=
    h.existsUnique_rotation_one_fixed_of_fixedVertexCount_eq_one
      data.rotationOne_fixed_count
  orbitBase := data.orbitBase
  adjacentMoved := data.adjacentMoved.toReflectionCopyPartition38Witness

/-- Forget the constant-residual and exact-count presentations to the existing
linear-character and unique-fixed constructive boundary. -/
noncomputable def toD19ConstructiveFinalLinearUniqueInputs
    (data : D19FinalLinearCountConstantResidualInputs h) :
    D19ConstructiveFinalLinearUniqueInputs h :=
  data.toD19FinalLinearUniqueReflectionInputs
    |>.toD19ConstructiveFinalLinearUniqueInputs

/-- Forget the specialized boundaries down to constructive final inputs. -/
noncomputable def toD19ConstructiveFinalInputs
    (data : D19FinalLinearCountConstantResidualInputs h) :
    D19ConstructiveFinalInputs h :=
  data.toD19FinalLinearUniqueReflectionInputs.toD19ConstructiveFinalInputs

/-- Forget all specialized boundaries down to final inputs. -/
noncomputable def toD19FinalInputs
    (data : D19FinalLinearCountConstantResidualInputs h) :
    D19FinalInputs h :=
  data.toD19FinalLinearUniqueReflectionInputs.toD19FinalInputs

/-- Cardinality-one fixed set variant of the exact-count input constructor. -/
noncomputable def of_fixedVertexSet_card_eq_one
    (linearCharacter : D19ActsOnMoore57.D19LinearCharacterInput h)
    (rotationOne_fixed_card :
      Fintype.card (fixedVertexSet (h.rotation 1)) = 1)
    (orbitBase : OrbitBaseSelectionEnumeration h)
    (adjacentMoved :
      AdjacentMovedReflectionConstantResidual38Witness h orbitBase.base) :
    D19FinalLinearCountConstantResidualInputs h where
  linearCharacter := linearCharacter
  rotationOne_fixed_count := by
    simpa [fixedVertexCount_eq_card_fixedVertexSet] using rotationOne_fixed_card
  orbitBase := orbitBase
  adjacentMoved := adjacentMoved

/-- Final inputs in the linear-character, exact-count, constant-residual
reflection-copy form cannot exist. -/
theorem not_nonempty (h : D19ActsOnMoore57 V Γ) :
    ¬ Nonempty (D19FinalLinearCountConstantResidualInputs h) := by
  rintro ⟨data⟩
  exact D19FinalLinearUniqueReflectionInputs.not_nonempty h
    ⟨data.toD19FinalLinearUniqueReflectionInputs⟩

end D19FinalLinearCountConstantResidualInputs

end Moore57
