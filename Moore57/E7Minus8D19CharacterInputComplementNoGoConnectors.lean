import Moore57.E7Minus8D19FinalCharacterInputComplementBoundary
import Moore57.E7Minus8D19CharacterInputComplementBoundary
import Moore57.E7Minus8BoundaryPackageActionNoGoConnectors
import Moore57.E7Minus8BoundaryPackageCurrentGapNoGoConnectors

/-!
# Action-level no-go connectors from complementary character inputs

This file exposes action-level no-go frontiers directly from
`D19CharacterInput` and `D19FinalCharacterInputs` after the `(-8)` character
values have been supplied by the complementary projection formula.
-/

namespace Moore57

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

namespace D19ActsOnMoore57

namespace E7Minus8CharacterReflectionCountBoundary

variable (h : D19ActsOnMoore57 V Γ)

/-- Build the complementary package from a coarse character input and a
fixed-star input at the standard reflection representative. -/
def ofD19CharacterInputComplementAndReflectionStar'
    (characterInput : D19CharacterInput h)
    (hStar :
      InvolutionFixedSetStar56 Γ (h.smulEquiv (DihedralGroup.sr 0))) :
    E7Minus8CharacterReflectionCountBoundary h :=
  ofD19CharacterInputComplementAndReflectionStar h characterInput hStar

end E7Minus8CharacterReflectionCountBoundary

/-- Complementary `D19CharacterInput` route rules out the action-level final
boundary. -/
theorem no_actionLevelFinalBoundary_of_d19CharacterInputComplement
    (h : D19ActsOnMoore57 V Γ)
    (characterInput : D19CharacterInput h)
    (reflection_fixed_count :
      fixedVertexCount (h.smulEquiv (DihedralGroup.sr 0)) = 56)
    (reflection_adjacent_moved :
      adjacentMovedCount Γ (h.smulEquiv (DihedralGroup.sr 0)) = 112) :
    ¬ Nonempty (BranchOrbitABCActionLevelFinalBoundary h) :=
  (E7Minus8CharacterReflectionCountBoundary.ofD19CharacterInputComplement h
    characterInput reflection_fixed_count reflection_adjacent_moved)
      |>.no_actionLevelFinalBoundary

/-- Complementary `D19CharacterInput` route rules out the action-level local
obstruction boundary. -/
theorem no_actionLevelLocalObstructionBoundary_of_d19CharacterInputComplement
    (h : D19ActsOnMoore57 V Γ)
    (characterInput : D19CharacterInput h)
    (reflection_fixed_count :
      fixedVertexCount (h.smulEquiv (DihedralGroup.sr 0)) = 56)
    (reflection_adjacent_moved :
      adjacentMovedCount Γ (h.smulEquiv (DihedralGroup.sr 0)) = 112) :
    ¬ Nonempty (BranchOrbitABCActionLevelLocalObstructionBoundary h) :=
  (E7Minus8CharacterReflectionCountBoundary.ofD19CharacterInputComplement h
    characterInput reflection_fixed_count reflection_adjacent_moved)
      |>.no_actionLevelLocalObstructionBoundary

/-- Complementary `D19CharacterInput` route rules out the action-level
reduced-coordinate witness boundary. -/
theorem no_actionLevelReducedCoordinateWitnessBoundary_of_d19CharacterInputComplement
    (h : D19ActsOnMoore57 V Γ)
    (characterInput : D19CharacterInput h)
    (reflection_fixed_count :
      fixedVertexCount (h.smulEquiv (DihedralGroup.sr 0)) = 56)
    (reflection_adjacent_moved :
      adjacentMovedCount Γ (h.smulEquiv (DihedralGroup.sr 0)) = 112) :
    ¬ Nonempty (BranchOrbitABCActionLevelReducedCoordinateWitnessBoundary h) :=
  (E7Minus8CharacterReflectionCountBoundary.ofD19CharacterInputComplement h
    characterInput reflection_fixed_count reflection_adjacent_moved)
      |>.no_actionLevelReducedCoordinateWitnessBoundary

/-- Complementary `D19CharacterInput` route rules out the action-level
set-invariant witness boundary. -/
theorem no_actionLevelSetInvariantWitnessBoundary_of_d19CharacterInputComplement
    (h : D19ActsOnMoore57 V Γ)
    (characterInput : D19CharacterInput h)
    (reflection_fixed_count :
      fixedVertexCount (h.smulEquiv (DihedralGroup.sr 0)) = 56)
    (reflection_adjacent_moved :
      adjacentMovedCount Γ (h.smulEquiv (DihedralGroup.sr 0)) = 112) :
    ¬ Nonempty (BranchOrbitABCActionLevelSetInvariantWitnessBoundary h) :=
  (E7Minus8CharacterReflectionCountBoundary.ofD19CharacterInputComplement h
    characterInput reflection_fixed_count reflection_adjacent_moved)
      |>.no_actionLevelSetInvariantWitnessBoundary

/-- Complementary `D19CharacterInput` route rules out the common-neighbor
reduced current-gap boundary. -/
theorem no_actionLevelCommonNeighborReducedBoundary_of_d19CharacterInputComplement
    (h : D19ActsOnMoore57 V Γ)
    (characterInput : D19CharacterInput h)
    (reflection_fixed_count :
      fixedVertexCount (h.smulEquiv (DihedralGroup.sr 0)) = 56)
    (reflection_adjacent_moved :
      adjacentMovedCount Γ (h.smulEquiv (DihedralGroup.sr 0)) = 112) :
    ¬ Nonempty (BranchOrbitABCActionLevelCommonNeighborReducedBoundary h) :=
  (E7Minus8CharacterReflectionCountBoundary.ofD19CharacterInputComplement h
    characterInput reflection_fixed_count reflection_adjacent_moved)
      |>.no_actionLevelCommonNeighborReducedBoundary

/-- Complementary `D19CharacterInput` route rules out the minimal-remaining
current-gap boundary. -/
theorem no_actionLevelMinimalRemainingBoundary_of_d19CharacterInputComplement
    (h : D19ActsOnMoore57 V Γ)
    (characterInput : D19CharacterInput h)
    (reflection_fixed_count :
      fixedVertexCount (h.smulEquiv (DihedralGroup.sr 0)) = 56)
    (reflection_adjacent_moved :
      adjacentMovedCount Γ (h.smulEquiv (DihedralGroup.sr 0)) = 112) :
    ¬ Nonempty (BranchOrbitABCActionLevelMinimalRemainingBoundary h) :=
  (E7Minus8CharacterReflectionCountBoundary.ofD19CharacterInputComplement h
    characterInput reflection_fixed_count reflection_adjacent_moved)
      |>.no_actionLevelMinimalRemainingBoundary

/-- Complementary `D19CharacterInput` route rules out the refined
minimal-remaining current-gap boundary. -/
theorem no_actionLevelMinimalRemainingRefinedBoundary_of_d19CharacterInputComplement
    (h : D19ActsOnMoore57 V Γ)
    (characterInput : D19CharacterInput h)
    (reflection_fixed_count :
      fixedVertexCount (h.smulEquiv (DihedralGroup.sr 0)) = 56)
    (reflection_adjacent_moved :
      adjacentMovedCount Γ (h.smulEquiv (DihedralGroup.sr 0)) = 112) :
    ¬ Nonempty (BranchOrbitABCActionLevelMinimalRemainingRefinedBoundary h) :=
  (E7Minus8CharacterReflectionCountBoundary.ofD19CharacterInputComplement h
    characterInput reflection_fixed_count reflection_adjacent_moved)
      |>.no_actionLevelMinimalRemainingRefinedBoundary

/-- Complementary `D19CharacterInput` route rules out the matching-equation
refined minimal-remaining current-gap boundary. -/
theorem no_actionLevelMinimalRemainingRefinedMatchingBoundary_of_d19CharacterInputComplement
    (h : D19ActsOnMoore57 V Γ)
    (characterInput : D19CharacterInput h)
    (reflection_fixed_count :
      fixedVertexCount (h.smulEquiv (DihedralGroup.sr 0)) = 56)
    (reflection_adjacent_moved :
      adjacentMovedCount Γ (h.smulEquiv (DihedralGroup.sr 0)) = 112) :
    ¬ Nonempty (BranchOrbitABCActionLevelMinimalRemainingRefinedMatchingBoundary h) :=
  (E7Minus8CharacterReflectionCountBoundary.ofD19CharacterInputComplement h
    characterInput reflection_fixed_count reflection_adjacent_moved)
      |>.no_actionLevelMinimalRemainingRefinedMatchingBoundary

/-- Fixed-star variant of
`no_actionLevelFinalBoundary_of_d19CharacterInputComplement`. -/
theorem no_actionLevelFinalBoundary_of_d19CharacterInputComplementAndReflectionStar
    (h : D19ActsOnMoore57 V Γ)
    (characterInput : D19CharacterInput h)
    (hStar :
      InvolutionFixedSetStar56 Γ (h.smulEquiv (DihedralGroup.sr 0))) :
    ¬ Nonempty (BranchOrbitABCActionLevelFinalBoundary h) :=
  (E7Minus8CharacterReflectionCountBoundary.ofD19CharacterInputComplementAndReflectionStar
    h characterInput hStar)
      |>.no_actionLevelFinalBoundary

/-- Fixed-star variant of
`no_actionLevelMinimalRemainingRefinedMatchingBoundary_of_d19CharacterInputComplement`. -/
theorem no_actionLevelMinimalRemainingRefinedMatchingBoundary_of_d19CharacterInputComplementAndReflectionStar
    (h : D19ActsOnMoore57 V Γ)
    (characterInput : D19CharacterInput h)
    (hStar :
      InvolutionFixedSetStar56 Γ (h.smulEquiv (DihedralGroup.sr 0))) :
    ¬ Nonempty (BranchOrbitABCActionLevelMinimalRemainingRefinedMatchingBoundary h) :=
  (E7Minus8CharacterReflectionCountBoundary.ofD19CharacterInputComplementAndReflectionStar
    h characterInput hStar)
      |>.no_actionLevelMinimalRemainingRefinedMatchingBoundary

/-- Final character inputs route to the action-level final no-go through the
complementary minus-8 package. -/
theorem no_actionLevelFinalBoundary_of_d19FinalCharacterInputsComplement
    (h : D19ActsOnMoore57 V Γ)
    (character : D19FinalCharacterInputs h)
    (reflection_fixed_count :
      fixedVertexCount (h.smulEquiv (DihedralGroup.sr 0)) = 56)
    (reflection_adjacent_moved :
      adjacentMovedCount Γ (h.smulEquiv (DihedralGroup.sr 0)) = 112) :
    ¬ Nonempty (BranchOrbitABCActionLevelFinalBoundary h) :=
  (E7Minus8CharacterReflectionCountBoundary.ofD19FinalCharacterInputsComplement h
    character reflection_fixed_count reflection_adjacent_moved)
      |>.no_actionLevelFinalBoundary

/-- Final character inputs route to the matching-equation refined
minimal-remaining no-go through the complementary minus-8 package. -/
theorem no_actionLevelMinimalRemainingRefinedMatchingBoundary_of_d19FinalCharacterInputsComplement
    (h : D19ActsOnMoore57 V Γ)
    (character : D19FinalCharacterInputs h)
    (reflection_fixed_count :
      fixedVertexCount (h.smulEquiv (DihedralGroup.sr 0)) = 56)
    (reflection_adjacent_moved :
      adjacentMovedCount Γ (h.smulEquiv (DihedralGroup.sr 0)) = 112) :
    ¬ Nonempty (BranchOrbitABCActionLevelMinimalRemainingRefinedMatchingBoundary h) :=
  (E7Minus8CharacterReflectionCountBoundary.ofD19FinalCharacterInputsComplement h
    character reflection_fixed_count reflection_adjacent_moved)
      |>.no_actionLevelMinimalRemainingRefinedMatchingBoundary

/-- Fixed-star final-character route to the action-level final no-go. -/
theorem no_actionLevelFinalBoundary_of_d19FinalCharacterInputsComplementAndReflectionStar
    (h : D19ActsOnMoore57 V Γ)
    (character : D19FinalCharacterInputs h)
    (hStar :
      InvolutionFixedSetStar56 Γ (h.smulEquiv (DihedralGroup.sr 0))) :
    ¬ Nonempty (BranchOrbitABCActionLevelFinalBoundary h) :=
  (E7Minus8CharacterReflectionCountBoundary.ofD19FinalCharacterInputsComplementAndReflectionStar
    h character hStar)
      |>.no_actionLevelFinalBoundary

/-- Fixed-star final-character route to the matching-equation refined
minimal-remaining no-go. -/
theorem no_actionLevelMinimalRemainingRefinedMatchingBoundary_of_d19FinalCharacterInputsComplementAndReflectionStar
    (h : D19ActsOnMoore57 V Γ)
    (character : D19FinalCharacterInputs h)
    (hStar :
      InvolutionFixedSetStar56 Γ (h.smulEquiv (DihedralGroup.sr 0))) :
    ¬ Nonempty (BranchOrbitABCActionLevelMinimalRemainingRefinedMatchingBoundary h) :=
  (E7Minus8CharacterReflectionCountBoundary.ofD19FinalCharacterInputsComplementAndReflectionStar
    h character hStar)
      |>.no_actionLevelMinimalRemainingRefinedMatchingBoundary

end D19ActsOnMoore57

end

end Moore57
