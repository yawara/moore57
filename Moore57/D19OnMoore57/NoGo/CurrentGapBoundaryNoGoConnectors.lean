import Moore57.D19OnMoore57.BranchOrbit.ABCFinalGapReportBoundary
import Moore57.D19OnMoore57.Final.CharacterComponentConnectors
import Moore57.D19OnMoore57.LinearCharacter.Minus8Auto

/-!
# Current-gap no-go connectors

This file records direct aliases from the split final-character inputs, or
from the representation component boundary itself, to the current action-level
boundary no-go frontiers.
-/

namespace Moore57

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- Component-boundary form of the common-neighbor reduced no-go frontier. -/
theorem no_D19_actionLevelCommonNeighborReducedBoundary_of_components
    (h : D19ActsOnMoore57 V Γ)
    (components :
      D19ActsOnMoore57.RepresentationCharacterComponentsBoundary h) :
    ¬ Nonempty (BranchOrbitABCActionLevelCommonNeighborReducedBoundary h) := by
  intro boundary
  exact no_D19_actionLevelCommonNeighborReducedBoundary h
    ⟨components, boundary⟩

/-- Final-character-input form of the common-neighbor reduced no-go frontier. -/
theorem no_D19_actionLevelCommonNeighborReducedBoundary_of_finalCharacterInputs
    (h : D19ActsOnMoore57 V Γ)
    (character : D19FinalCharacterInputs h) :
    ¬ Nonempty (BranchOrbitABCActionLevelCommonNeighborReducedBoundary h) :=
  no_D19_actionLevelCommonNeighborReducedBoundary_of_components h
    character.representationCharacterComponentsBoundary

/-- K155/eigenspace-character form of the common-neighbor reduced no-go
frontier. -/
theorem no_D19_actionLevelCommonNeighborReducedBoundary_of_eigenspaceCharactersAndK155_autoRotation
    (h : D19ActsOnMoore57 V Γ)
    (alpha beta gamma A B C : ℕ)
    (h7 : ∀ g : DihedralGroup 19,
      Matrix.trace (E7Matrix Γ * permMatrix (h.smulEquiv g)) =
        (d19LinearCharacter alpha beta gamma g : ℚ))
    (hMinus8 : ∀ g : DihedralGroup 19,
      Matrix.trace (permMatrix (h.smulEquiv g)) - 1 -
          Matrix.trace (E7Matrix Γ * permMatrix (h.smulEquiv g)) =
        (d19LinearCharacter A B C g : ℚ))
    {dt : ZMod 19}
    (hK : InvolutionK155 Γ (h.smulEquiv (DihedralGroup.sr dt))) :
    ¬ Nonempty (BranchOrbitABCActionLevelCommonNeighborReducedBoundary h) :=
  no_D19_actionLevelCommonNeighborReducedBoundary_of_components h
    (D19ActsOnMoore57.representationCharacterComponentsBoundary_of_eigenspaceCharactersAndInvolutionK155
      h alpha beta gamma A B C h7 hMinus8 hK)

/-- Component-boundary form of the minimal remaining no-go frontier. -/
theorem no_D19_actionLevelMinimalRemainingBoundary_of_components
    (h : D19ActsOnMoore57 V Γ)
    (components :
      D19ActsOnMoore57.RepresentationCharacterComponentsBoundary h) :
    ¬ Nonempty (BranchOrbitABCActionLevelMinimalRemainingBoundary h) := by
  intro boundary
  exact no_D19_actionLevelMinimalRemainingBoundary h
    ⟨components, boundary⟩

/-- Final-character-input form of the minimal remaining no-go frontier. -/
theorem no_D19_actionLevelMinimalRemainingBoundary_of_finalCharacterInputs
    (h : D19ActsOnMoore57 V Γ)
    (character : D19FinalCharacterInputs h) :
    ¬ Nonempty (BranchOrbitABCActionLevelMinimalRemainingBoundary h) :=
  no_D19_actionLevelMinimalRemainingBoundary_of_components h
    character.representationCharacterComponentsBoundary

/-- K155/eigenspace-character form of the minimal remaining no-go frontier. -/
theorem no_D19_actionLevelMinimalRemainingBoundary_of_eigenspaceCharactersAndK155_autoRotation
    (h : D19ActsOnMoore57 V Γ)
    (alpha beta gamma A B C : ℕ)
    (h7 : ∀ g : DihedralGroup 19,
      Matrix.trace (E7Matrix Γ * permMatrix (h.smulEquiv g)) =
        (d19LinearCharacter alpha beta gamma g : ℚ))
    (hMinus8 : ∀ g : DihedralGroup 19,
      Matrix.trace (permMatrix (h.smulEquiv g)) - 1 -
          Matrix.trace (E7Matrix Γ * permMatrix (h.smulEquiv g)) =
        (d19LinearCharacter A B C g : ℚ))
    {dt : ZMod 19}
    (hK : InvolutionK155 Γ (h.smulEquiv (DihedralGroup.sr dt))) :
    ¬ Nonempty (BranchOrbitABCActionLevelMinimalRemainingBoundary h) :=
  no_D19_actionLevelMinimalRemainingBoundary_of_components h
    (D19ActsOnMoore57.representationCharacterComponentsBoundary_of_eigenspaceCharactersAndInvolutionK155
      h alpha beta gamma A B C h7 hMinus8 hK)

/-- Component-boundary form of the refined minimal remaining no-go frontier. -/
theorem no_D19_actionLevelMinimalRemainingRefinedBoundary_of_components
    (h : D19ActsOnMoore57 V Γ)
    (components :
      D19ActsOnMoore57.RepresentationCharacterComponentsBoundary h) :
    ¬ Nonempty
        (BranchOrbitABCActionLevelMinimalRemainingRefinedBoundary h) := by
  intro boundary
  exact no_D19_actionLevelMinimalRemainingRefinedBoundary h
    ⟨components, boundary⟩

/-- Final-character-input form of the refined minimal remaining no-go
frontier. -/
theorem no_D19_actionLevelMinimalRemainingRefinedBoundary_of_finalCharacterInputs
    (h : D19ActsOnMoore57 V Γ)
    (character : D19FinalCharacterInputs h) :
    ¬ Nonempty
        (BranchOrbitABCActionLevelMinimalRemainingRefinedBoundary h) :=
  no_D19_actionLevelMinimalRemainingRefinedBoundary_of_components h
    character.representationCharacterComponentsBoundary

/-- K155/eigenspace-character form of the refined minimal remaining no-go
frontier. -/
theorem no_D19_actionLevelMinimalRemainingRefinedBoundary_of_eigenspaceCharactersAndK155_autoRotation
    (h : D19ActsOnMoore57 V Γ)
    (alpha beta gamma A B C : ℕ)
    (h7 : ∀ g : DihedralGroup 19,
      Matrix.trace (E7Matrix Γ * permMatrix (h.smulEquiv g)) =
        (d19LinearCharacter alpha beta gamma g : ℚ))
    (hMinus8 : ∀ g : DihedralGroup 19,
      Matrix.trace (permMatrix (h.smulEquiv g)) - 1 -
          Matrix.trace (E7Matrix Γ * permMatrix (h.smulEquiv g)) =
        (d19LinearCharacter A B C g : ℚ))
    {dt : ZMod 19}
    (hK : InvolutionK155 Γ (h.smulEquiv (DihedralGroup.sr dt))) :
    ¬ Nonempty
        (BranchOrbitABCActionLevelMinimalRemainingRefinedBoundary h) :=
  no_D19_actionLevelMinimalRemainingRefinedBoundary_of_components h
    (D19ActsOnMoore57.representationCharacterComponentsBoundary_of_eigenspaceCharactersAndInvolutionK155
      h alpha beta gamma A B C h7 hMinus8 hK)

/-- Component-boundary form of the matching-equation refined minimal remaining
no-go frontier. -/
theorem no_D19_actionLevelMinimalRemainingRefinedMatchingBoundary_of_components
    (h : D19ActsOnMoore57 V Γ)
    (components :
      D19ActsOnMoore57.RepresentationCharacterComponentsBoundary h) :
    ¬ Nonempty
        (BranchOrbitABCActionLevelMinimalRemainingRefinedMatchingBoundary h) := by
  intro boundary
  exact no_D19_actionLevelMinimalRemainingRefinedMatchingBoundary h
    ⟨components, boundary⟩

/-- Final-character-input form of the matching-equation refined minimal
remaining no-go frontier. -/
theorem no_D19_actionLevelMinimalRemainingRefinedMatchingBoundary_of_finalCharacterInputs
    (h : D19ActsOnMoore57 V Γ)
    (character : D19FinalCharacterInputs h) :
    ¬ Nonempty
        (BranchOrbitABCActionLevelMinimalRemainingRefinedMatchingBoundary h) :=
  no_D19_actionLevelMinimalRemainingRefinedMatchingBoundary_of_components h
    character.representationCharacterComponentsBoundary

/-- K155/eigenspace-character form of the matching-equation refined minimal
remaining no-go frontier. -/
theorem no_D19_actionLevelMinimalRemainingRefinedMatchingBoundary_of_eigenspaceCharactersAndK155_autoRotation
    (h : D19ActsOnMoore57 V Γ)
    (alpha beta gamma A B C : ℕ)
    (h7 : ∀ g : DihedralGroup 19,
      Matrix.trace (E7Matrix Γ * permMatrix (h.smulEquiv g)) =
        (d19LinearCharacter alpha beta gamma g : ℚ))
    (hMinus8 : ∀ g : DihedralGroup 19,
      Matrix.trace (permMatrix (h.smulEquiv g)) - 1 -
          Matrix.trace (E7Matrix Γ * permMatrix (h.smulEquiv g)) =
        (d19LinearCharacter A B C g : ℚ))
    {dt : ZMod 19}
    (hK : InvolutionK155 Γ (h.smulEquiv (DihedralGroup.sr dt))) :
    ¬ Nonempty
        (BranchOrbitABCActionLevelMinimalRemainingRefinedMatchingBoundary h) :=
  no_D19_actionLevelMinimalRemainingRefinedMatchingBoundary_of_components h
    (D19ActsOnMoore57.representationCharacterComponentsBoundary_of_eigenspaceCharactersAndInvolutionK155
      h alpha beta gamma A B C h7 hMinus8 hK)

/-- Component-boundary form of the current final-gap no-go frontier. -/
theorem no_D19_currentFinalGapBoundary_of_components
    (h : D19ActsOnMoore57 V Γ)
    (components :
      D19ActsOnMoore57.RepresentationCharacterComponentsBoundary h) :
    ¬ Nonempty (BranchOrbitABCCurrentFinalGapBoundary h) := by
  intro boundary
  exact no_D19_currentFinalGapBoundary h
    ⟨components, boundary⟩

/-- Final-character-input form of the current final-gap no-go frontier. -/
theorem no_D19_currentFinalGapBoundary_of_finalCharacterInputs
    (h : D19ActsOnMoore57 V Γ)
    (character : D19FinalCharacterInputs h) :
    ¬ Nonempty (BranchOrbitABCCurrentFinalGapBoundary h) :=
  no_D19_currentFinalGapBoundary_of_components h
    character.representationCharacterComponentsBoundary

/-- K155/eigenspace-character form of the current final-gap no-go frontier. -/
theorem no_D19_currentFinalGapBoundary_of_eigenspaceCharactersAndK155_autoRotation
    (h : D19ActsOnMoore57 V Γ)
    (alpha beta gamma A B C : ℕ)
    (h7 : ∀ g : DihedralGroup 19,
      Matrix.trace (E7Matrix Γ * permMatrix (h.smulEquiv g)) =
        (d19LinearCharacter alpha beta gamma g : ℚ))
    (hMinus8 : ∀ g : DihedralGroup 19,
      Matrix.trace (permMatrix (h.smulEquiv g)) - 1 -
          Matrix.trace (E7Matrix Γ * permMatrix (h.smulEquiv g)) =
        (d19LinearCharacter A B C g : ℚ))
    {dt : ZMod 19}
    (hK : InvolutionK155 Γ (h.smulEquiv (DihedralGroup.sr dt))) :
    ¬ Nonempty (BranchOrbitABCCurrentFinalGapBoundary h) :=
  no_D19_currentFinalGapBoundary_of_components h
    (D19ActsOnMoore57.representationCharacterComponentsBoundary_of_eigenspaceCharactersAndInvolutionK155
      h alpha beta gamma A B C h7 hMinus8 hK)

end

end Moore57
