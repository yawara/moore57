import Moore57.D19OnMoore57.E7Projection.E7Minus8D19CharacterInputComplementBoundary
import Moore57.D19OnMoore57.D19Core.D19GeometricInputs

/-!
# Complementary minus-8 boundary from reduced and geometric inputs

This file lifts the complementary `(-8)` character-input route to the reduced
and geometric D19 input packages.  All proofs are thin wrappers through the
`D19CharacterInput` complement boundary theorems.
-/

namespace Moore57

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

namespace D19ReducedHypotheses

variable {h : D19ActsOnMoore57 V Γ}

/-- Reduced hypotheses plus the standard reflection counts give a nonempty
linear-character input through the complementary minus-8 route. -/
theorem nonempty_d19LinearCharacterInput_of_complement
    (data : D19ReducedHypotheses h)
    (reflection_fixed_count :
      fixedVertexCount (h.smulEquiv (DihedralGroup.sr 0)) = 56)
    (reflection_adjacent_moved :
      adjacentMovedCount Γ (h.smulEquiv (DihedralGroup.sr 0)) = 112) :
    Nonempty (D19ActsOnMoore57.D19LinearCharacterInput h) :=
  D19ActsOnMoore57.nonempty_d19LinearCharacterInput_of_d19CharacterInputComplement
    h data.characterInput reflection_fixed_count reflection_adjacent_moved

/-- Reduced hypotheses plus the standard reflection counts give fixed-star
boundaries for all reflections through the complementary minus-8 route. -/
theorem involutionFixedSetStar56_of_complement_raw_reflection
    (data : D19ReducedHypotheses h)
    (reflection_fixed_count :
      fixedVertexCount (h.smulEquiv (DihedralGroup.sr 0)) = 56)
    (reflection_adjacent_moved :
      adjacentMovedCount Γ (h.smulEquiv (DihedralGroup.sr 0)) = 112)
    (k : ZMod 19) :
    InvolutionFixedSetStar56 Γ (h.smulEquiv (DihedralGroup.sr k)) :=
  D19ActsOnMoore57.involutionFixedSetStar56_of_d19CharacterInputComplement_raw_reflection
    h data.characterInput reflection_fixed_count reflection_adjacent_moved k

/-- Reduced hypotheses plus the standard reflection counts give `K_{1,55}`
witnesses for all reflections through the complementary minus-8 route. -/
theorem nonempty_involutionK155_of_complement_raw_reflection
    (data : D19ReducedHypotheses h)
    (reflection_fixed_count :
      fixedVertexCount (h.smulEquiv (DihedralGroup.sr 0)) = 56)
    (reflection_adjacent_moved :
      adjacentMovedCount Γ (h.smulEquiv (DihedralGroup.sr 0)) = 112)
    (k : ZMod 19) :
    Nonempty (InvolutionK155 Γ (h.smulEquiv (DihedralGroup.sr k))) :=
  D19ActsOnMoore57.nonempty_involutionK155_of_d19CharacterInputComplement_raw_reflection
    h data.characterInput reflection_fixed_count reflection_adjacent_moved k

/-- Reduced hypotheses plus the standard reflection counts give the
fixed-center leaf boundary through the complementary minus-8 route. -/
theorem reflectionFixedCenterLeafBoundary_of_complement
    (data : D19ReducedHypotheses h)
    (reflection_fixed_count :
      fixedVertexCount (h.smulEquiv (DihedralGroup.sr 0)) = 56)
    (reflection_adjacent_moved :
      adjacentMovedCount Γ (h.smulEquiv (DihedralGroup.sr 0)) = 112) :
    ReflectionFixedCenterLeafBoundary h :=
  D19ActsOnMoore57.reflectionFixedCenterLeafBoundary_of_d19CharacterInputComplement
    h data.characterInput reflection_fixed_count reflection_adjacent_moved

/-- Reduced hypotheses plus the standard reflection counts give the
representation character component boundary through the complementary minus-8
route. -/
theorem representationCharacterComponentsBoundary_of_complement
    (data : D19ReducedHypotheses h)
    (reflection_fixed_count :
      fixedVertexCount (h.smulEquiv (DihedralGroup.sr 0)) = 56)
    (reflection_adjacent_moved :
      adjacentMovedCount Γ (h.smulEquiv (DihedralGroup.sr 0)) = 112) :
    D19ActsOnMoore57.RepresentationCharacterComponentsBoundary h :=
  D19ActsOnMoore57.representationCharacterComponentsBoundary_of_d19CharacterInputComplement
    h data.characterInput reflection_fixed_count reflection_adjacent_moved

/-- Reduced hypotheses plus the standard reflection counts rule out the
current final-gap boundary through the complementary minus-8 route. -/
theorem no_currentFinalGapBoundary_of_complement
    (data : D19ReducedHypotheses h)
    (reflection_fixed_count :
      fixedVertexCount (h.smulEquiv (DihedralGroup.sr 0)) = 56)
    (reflection_adjacent_moved :
      adjacentMovedCount Γ (h.smulEquiv (DihedralGroup.sr 0)) = 112) :
    ¬ Nonempty (BranchOrbitABCCurrentFinalGapBoundary h) :=
  D19ActsOnMoore57.no_currentFinalGapBoundary_of_d19CharacterInputComplement
    h data.characterInput reflection_fixed_count reflection_adjacent_moved

/-- Reduced hypotheses plus a fixed-star reflection input give a nonempty
linear-character input through the complementary minus-8 route. -/
theorem nonempty_d19LinearCharacterInput_of_complementAndReflectionStar
    (data : D19ReducedHypotheses h)
    (hStar :
      InvolutionFixedSetStar56 Γ (h.smulEquiv (DihedralGroup.sr 0))) :
    Nonempty (D19ActsOnMoore57.D19LinearCharacterInput h) :=
  D19ActsOnMoore57.nonempty_d19LinearCharacterInput_of_d19CharacterInputComplementAndReflectionStar
    h data.characterInput hStar

/-- Reduced hypotheses plus a fixed-star reflection input give fixed-star
boundaries for all reflections through the complementary minus-8 route. -/
theorem involutionFixedSetStar56_of_complementAndReflectionStar_raw_reflection
    (data : D19ReducedHypotheses h)
    (hStar :
      InvolutionFixedSetStar56 Γ (h.smulEquiv (DihedralGroup.sr 0)))
    (k : ZMod 19) :
    InvolutionFixedSetStar56 Γ (h.smulEquiv (DihedralGroup.sr k)) :=
  D19ActsOnMoore57.involutionFixedSetStar56_of_d19CharacterInputComplementAndReflectionStar_raw_reflection
    h data.characterInput hStar k

/-- Reduced hypotheses plus a fixed-star reflection input give `K_{1,55}`
witnesses for all reflections through the complementary minus-8 route. -/
theorem nonempty_involutionK155_of_complementAndReflectionStar_raw_reflection
    (data : D19ReducedHypotheses h)
    (hStar :
      InvolutionFixedSetStar56 Γ (h.smulEquiv (DihedralGroup.sr 0)))
    (k : ZMod 19) :
    Nonempty (InvolutionK155 Γ (h.smulEquiv (DihedralGroup.sr k))) :=
  D19ActsOnMoore57.nonempty_involutionK155_of_d19CharacterInputComplementAndReflectionStar_raw_reflection
    h data.characterInput hStar k

/-- Reduced hypotheses plus a fixed-star reflection input give the
fixed-center leaf boundary through the complementary minus-8 route. -/
theorem reflectionFixedCenterLeafBoundary_of_complementAndReflectionStar
    (data : D19ReducedHypotheses h)
    (hStar :
      InvolutionFixedSetStar56 Γ (h.smulEquiv (DihedralGroup.sr 0))) :
    ReflectionFixedCenterLeafBoundary h :=
  D19ActsOnMoore57.reflectionFixedCenterLeafBoundary_of_d19CharacterInputComplementAndReflectionStar
    h data.characterInput hStar

/-- Reduced hypotheses plus a fixed-star reflection input give the
representation character component boundary through the complementary minus-8
route. -/
theorem representationCharacterComponentsBoundary_of_complementAndReflectionStar
    (data : D19ReducedHypotheses h)
    (hStar :
      InvolutionFixedSetStar56 Γ (h.smulEquiv (DihedralGroup.sr 0))) :
    D19ActsOnMoore57.RepresentationCharacterComponentsBoundary h :=
  D19ActsOnMoore57.representationCharacterComponentsBoundary_of_d19CharacterInputComplementAndReflectionStar
    h data.characterInput hStar

/-- Reduced hypotheses plus a fixed-star reflection input rule out the current
final-gap boundary through the complementary minus-8 route. -/
theorem no_currentFinalGapBoundary_of_complementAndReflectionStar
    (data : D19ReducedHypotheses h)
    (hStar :
      InvolutionFixedSetStar56 Γ (h.smulEquiv (DihedralGroup.sr 0))) :
    ¬ Nonempty (BranchOrbitABCCurrentFinalGapBoundary h) :=
  D19ActsOnMoore57.no_currentFinalGapBoundary_of_d19CharacterInputComplementAndReflectionStar
    h data.characterInput hStar

end D19ReducedHypotheses

namespace D19GeometricInputs

variable {h : D19ActsOnMoore57 V Γ}

/-- Geometric inputs plus the standard reflection counts give a nonempty
linear-character input through the complementary minus-8 route. -/
theorem nonempty_d19LinearCharacterInput_of_complement
    (data : D19GeometricInputs h)
    (reflection_fixed_count :
      fixedVertexCount (h.smulEquiv (DihedralGroup.sr 0)) = 56)
    (reflection_adjacent_moved :
      adjacentMovedCount Γ (h.smulEquiv (DihedralGroup.sr 0)) = 112) :
    Nonempty (D19ActsOnMoore57.D19LinearCharacterInput h) :=
  D19ReducedHypotheses.nonempty_d19LinearCharacterInput_of_complement
    data.toD19ReducedHypotheses reflection_fixed_count reflection_adjacent_moved

/-- Geometric inputs plus the standard reflection counts give fixed-star
boundaries for all reflections through the complementary minus-8 route. -/
theorem involutionFixedSetStar56_of_complement_raw_reflection
    (data : D19GeometricInputs h)
    (reflection_fixed_count :
      fixedVertexCount (h.smulEquiv (DihedralGroup.sr 0)) = 56)
    (reflection_adjacent_moved :
      adjacentMovedCount Γ (h.smulEquiv (DihedralGroup.sr 0)) = 112)
    (k : ZMod 19) :
    InvolutionFixedSetStar56 Γ (h.smulEquiv (DihedralGroup.sr k)) :=
  D19ReducedHypotheses.involutionFixedSetStar56_of_complement_raw_reflection
    data.toD19ReducedHypotheses reflection_fixed_count reflection_adjacent_moved k

/-- Geometric inputs plus the standard reflection counts give `K_{1,55}`
witnesses for all reflections through the complementary minus-8 route. -/
theorem nonempty_involutionK155_of_complement_raw_reflection
    (data : D19GeometricInputs h)
    (reflection_fixed_count :
      fixedVertexCount (h.smulEquiv (DihedralGroup.sr 0)) = 56)
    (reflection_adjacent_moved :
      adjacentMovedCount Γ (h.smulEquiv (DihedralGroup.sr 0)) = 112)
    (k : ZMod 19) :
    Nonempty (InvolutionK155 Γ (h.smulEquiv (DihedralGroup.sr k))) :=
  D19ReducedHypotheses.nonempty_involutionK155_of_complement_raw_reflection
    data.toD19ReducedHypotheses reflection_fixed_count reflection_adjacent_moved k

/-- Geometric inputs plus the standard reflection counts give the fixed-center
leaf boundary through the complementary minus-8 route. -/
theorem reflectionFixedCenterLeafBoundary_of_complement
    (data : D19GeometricInputs h)
    (reflection_fixed_count :
      fixedVertexCount (h.smulEquiv (DihedralGroup.sr 0)) = 56)
    (reflection_adjacent_moved :
      adjacentMovedCount Γ (h.smulEquiv (DihedralGroup.sr 0)) = 112) :
    ReflectionFixedCenterLeafBoundary h :=
  D19ReducedHypotheses.reflectionFixedCenterLeafBoundary_of_complement
    data.toD19ReducedHypotheses reflection_fixed_count reflection_adjacent_moved

/-- Geometric inputs plus the standard reflection counts give the
representation character component boundary through the complementary minus-8
route. -/
theorem representationCharacterComponentsBoundary_of_complement
    (data : D19GeometricInputs h)
    (reflection_fixed_count :
      fixedVertexCount (h.smulEquiv (DihedralGroup.sr 0)) = 56)
    (reflection_adjacent_moved :
      adjacentMovedCount Γ (h.smulEquiv (DihedralGroup.sr 0)) = 112) :
    D19ActsOnMoore57.RepresentationCharacterComponentsBoundary h :=
  D19ReducedHypotheses.representationCharacterComponentsBoundary_of_complement
    data.toD19ReducedHypotheses reflection_fixed_count reflection_adjacent_moved

/-- Geometric inputs plus the standard reflection counts rule out the current
final-gap boundary through the complementary minus-8 route. -/
theorem no_currentFinalGapBoundary_of_complement
    (data : D19GeometricInputs h)
    (reflection_fixed_count :
      fixedVertexCount (h.smulEquiv (DihedralGroup.sr 0)) = 56)
    (reflection_adjacent_moved :
      adjacentMovedCount Γ (h.smulEquiv (DihedralGroup.sr 0)) = 112) :
    ¬ Nonempty (BranchOrbitABCCurrentFinalGapBoundary h) :=
  D19ReducedHypotheses.no_currentFinalGapBoundary_of_complement
    data.toD19ReducedHypotheses reflection_fixed_count reflection_adjacent_moved

/-- Geometric inputs plus a fixed-star reflection input give a nonempty
linear-character input through the complementary minus-8 route. -/
theorem nonempty_d19LinearCharacterInput_of_complementAndReflectionStar
    (data : D19GeometricInputs h)
    (hStar :
      InvolutionFixedSetStar56 Γ (h.smulEquiv (DihedralGroup.sr 0))) :
    Nonempty (D19ActsOnMoore57.D19LinearCharacterInput h) :=
  D19ReducedHypotheses.nonempty_d19LinearCharacterInput_of_complementAndReflectionStar
    data.toD19ReducedHypotheses hStar

/-- Geometric inputs plus a fixed-star reflection input give fixed-star
boundaries for all reflections through the complementary minus-8 route. -/
theorem involutionFixedSetStar56_of_complementAndReflectionStar_raw_reflection
    (data : D19GeometricInputs h)
    (hStar :
      InvolutionFixedSetStar56 Γ (h.smulEquiv (DihedralGroup.sr 0)))
    (k : ZMod 19) :
    InvolutionFixedSetStar56 Γ (h.smulEquiv (DihedralGroup.sr k)) :=
  D19ReducedHypotheses.involutionFixedSetStar56_of_complementAndReflectionStar_raw_reflection
    data.toD19ReducedHypotheses hStar k

/-- Geometric inputs plus a fixed-star reflection input give `K_{1,55}`
witnesses for all reflections through the complementary minus-8 route. -/
theorem nonempty_involutionK155_of_complementAndReflectionStar_raw_reflection
    (data : D19GeometricInputs h)
    (hStar :
      InvolutionFixedSetStar56 Γ (h.smulEquiv (DihedralGroup.sr 0)))
    (k : ZMod 19) :
    Nonempty (InvolutionK155 Γ (h.smulEquiv (DihedralGroup.sr k))) :=
  D19ReducedHypotheses.nonempty_involutionK155_of_complementAndReflectionStar_raw_reflection
    data.toD19ReducedHypotheses hStar k

/-- Geometric inputs plus a fixed-star reflection input give the fixed-center
leaf boundary through the complementary minus-8 route. -/
theorem reflectionFixedCenterLeafBoundary_of_complementAndReflectionStar
    (data : D19GeometricInputs h)
    (hStar :
      InvolutionFixedSetStar56 Γ (h.smulEquiv (DihedralGroup.sr 0))) :
    ReflectionFixedCenterLeafBoundary h :=
  D19ReducedHypotheses.reflectionFixedCenterLeafBoundary_of_complementAndReflectionStar
    data.toD19ReducedHypotheses hStar

/-- Geometric inputs plus a fixed-star reflection input give the representation
character component boundary through the complementary minus-8 route. -/
theorem representationCharacterComponentsBoundary_of_complementAndReflectionStar
    (data : D19GeometricInputs h)
    (hStar :
      InvolutionFixedSetStar56 Γ (h.smulEquiv (DihedralGroup.sr 0))) :
    D19ActsOnMoore57.RepresentationCharacterComponentsBoundary h :=
  D19ReducedHypotheses.representationCharacterComponentsBoundary_of_complementAndReflectionStar
    data.toD19ReducedHypotheses hStar

/-- Geometric inputs plus a fixed-star reflection input rule out the current
final-gap boundary through the complementary minus-8 route. -/
theorem no_currentFinalGapBoundary_of_complementAndReflectionStar
    (data : D19GeometricInputs h)
    (hStar :
      InvolutionFixedSetStar56 Γ (h.smulEquiv (DihedralGroup.sr 0))) :
    ¬ Nonempty (BranchOrbitABCCurrentFinalGapBoundary h) :=
  D19ReducedHypotheses.no_currentFinalGapBoundary_of_complementAndReflectionStar
    data.toD19ReducedHypotheses hStar

end D19GeometricInputs

end

end Moore57
