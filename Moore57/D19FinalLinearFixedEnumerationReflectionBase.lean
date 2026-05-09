import Moore57.D19FinalInputs
import Moore57.D19LinearCharacterInput
import Moore57.FixedUpperBoundEnumeration
import Moore57.OrbitBaseSelectionInputBridge
import Moore57.AdjacentMovedReflectionCopyCriteria

/-!
# Final D19 base-selection inputs from fixed enumeration

This file lowers the orbit-base boundary in the fixed-enumeration,
reflection-copy final input package from an explicit orbit-base enumeration to
the downstream base-selection input: moved bases with pairwise disjoint
rotation orbits.
-/

namespace Moore57

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- Final D19 input package using a full linear-character witness, an explicit
rotation-one fixed-point enumeration, a downstream base-selection input, and a
reflection-copy adjacent-moved partition. -/
structure D19FinalLinearFixedEnumerationReflectionBaseInputs
    (h : D19ActsOnMoore57 V Γ) where
  /-- Full D19 linear-character witness for the trace representation. -/
  linearCharacter : D19ActsOnMoore57.D19LinearCharacterInput h
  /-- Explicit finite cover of the rotation-one fixed vertices. -/
  fixedEnumeration : D19ActsOnMoore57.RotationOneFixedEnumeration h
  /-- Pairwise-disjoint selected moved rotation orbits. -/
  orbitBase : OrbitBaseSelectionInput h
  /-- Reflection-copy adjacent-moved partition over the selected bases. -/
  adjacentMoved :
    AdjacentMovedReflectionCopyPartition38Witness h orbitBase.base

namespace D19FinalLinearFixedEnumerationReflectionBaseInputs

variable {h : D19ActsOnMoore57 V Γ}

/-- Convert the linear-character and fixed-enumeration inputs into the split
final character input. -/
def toD19FinalCharacterInputs
    (data : D19FinalLinearFixedEnumerationReflectionBaseInputs h) :
    D19FinalCharacterInputs h where
  representation := data.linearCharacter.toD19RepresentationCharacterInput
  fixedUpperBound := data.fixedEnumeration.toRotationFixedUpperBoundInput

/-- Forget the specialized base and reflection-copy presentation down to the
final input boundary. -/
noncomputable def toD19FinalInputs
    (data : D19FinalLinearFixedEnumerationReflectionBaseInputs h) :
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

/-- Final linear-character, fixed-enumeration, reflection-copy base inputs
cannot exist. -/
theorem not_nonempty (h : D19ActsOnMoore57 V Γ) :
    ¬ Nonempty (D19FinalLinearFixedEnumerationReflectionBaseInputs h) := by
  rintro ⟨data⟩
  exact D19FinalInputs.not_nonempty h ⟨data.toD19FinalInputs⟩

end D19FinalLinearFixedEnumerationReflectionBaseInputs

end Moore57
