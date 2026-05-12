import Moore57.D19OnMoore57.Final.Inputs
import Moore57.D19OnMoore57.LinearCharacter.Input
import Moore57.D19OnMoore57.Rotation.FixedUniqueCriteria
import Moore57.D19OnMoore57.Orbit.BaseSelectionInputBridge
import Moore57.D19OnMoore57.AdjacentMoved.ReflectionCopyCriteria

/-!
# Final D19 inputs from base-selection inputs and reflection copies

This file lowers the orbit-base boundary from an explicit coordinate
enumeration to the downstream base-selection input: moved bases with pairwise
disjoint rotation orbits.  The bridge to `OrbitBaseSelectionWitness` supplies
the global orbit-coordinate injectivity required by `D19FinalInputs`.
-/

namespace Moore57

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- Final D19 input package using a full linear-character witness, a unique
rotation-one fixed point, a downstream base-selection input, and a
reflection-copy adjacent-moved partition. -/
structure D19FinalLinearUniqueReflectionBaseInputs
    (h : D19ActsOnMoore57 V Γ) where
  /-- Full D19 linear-character witness for the trace representation. -/
  linearCharacter : D19ActsOnMoore57.D19LinearCharacterInput h
  /-- Rotation by `1` has a unique fixed vertex. -/
  rotationOne_unique_fixed : ∃! v : V, h.rotation 1 v = v
  /-- Pairwise-disjoint selected moved rotation orbits. -/
  orbitBase : OrbitBaseSelectionInput h
  /-- Reflection-copy adjacent-moved partition over the selected bases. -/
  adjacentMoved :
    AdjacentMovedReflectionCopyPartition38Witness h orbitBase.base

namespace D19FinalLinearUniqueReflectionBaseInputs

variable {h : D19ActsOnMoore57 V Γ}

/-- Convert the linear-character and unique-fixed inputs into the split final
character input. -/
def toD19FinalCharacterInputs
    (data : D19FinalLinearUniqueReflectionBaseInputs h) :
    D19FinalCharacterInputs h where
  representation := data.linearCharacter.toD19RepresentationCharacterInput
  fixedUpperBound :=
    D19ActsOnMoore57.RotationFixedUpperBoundInput.of_existsUnique_rotation_one_fixed
      h data.rotationOne_unique_fixed

/-- Forget the specialized base and reflection-copy presentation down to the
final input boundary. -/
noncomputable def toD19FinalInputs
    (data : D19FinalLinearUniqueReflectionBaseInputs h) :
    D19FinalInputs h where
  character := data.toD19FinalCharacterInputs
  orbitBase := data.orbitBase.toWitness
  fixedOrAContribution := fixedOrAContribution38
  fixed_or_A_contribution := by
    intro d hd
    rfl
  adjacentMovedDecomposition := by
    simpa [OrbitBaseSelectionInput.toWitness] using
      data.adjacentMoved.toDecomposition

/-- Final linear-character, unique-fixed, reflection-copy base inputs cannot
exist. -/
theorem not_nonempty (h : D19ActsOnMoore57 V Γ) :
    ¬ Nonempty (D19FinalLinearUniqueReflectionBaseInputs h) := by
  rintro ⟨data⟩
  exact D19FinalInputs.not_nonempty h ⟨data.toD19FinalInputs⟩

end D19FinalLinearUniqueReflectionBaseInputs

end Moore57
