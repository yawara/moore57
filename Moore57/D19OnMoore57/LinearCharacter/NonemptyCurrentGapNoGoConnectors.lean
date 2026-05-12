import Moore57.D19OnMoore57.LinearCharacter.NonemptyNoGoConnectors
import Moore57.D19OnMoore57.NoGo.CurrentGapBoundaryNoGoConnectors

/-!
# Current-gap no-go connectors from nonempty linear-character input

This file routes `Nonempty (D19LinearCharacterInput h)` into the component
boundary consumed by the current branch-orbit no-go frontiers.
-/

namespace Moore57

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- Common-neighbor reduced no-go from a nonempty linear-character input. -/
theorem no_D19_actionLevelCommonNeighborReducedBoundary_of_nonempty_linearCharacterInput
    (h : D19ActsOnMoore57 V Γ)
    (hin : Nonempty (D19ActsOnMoore57.D19LinearCharacterInput h)) :
    ¬ Nonempty (BranchOrbitABCActionLevelCommonNeighborReducedBoundary h) :=
  no_D19_actionLevelCommonNeighborReducedBoundary_of_components h
    (D19ActsOnMoore57.representationCharacterComponentsBoundary_of_nonempty_linearCharacterInput
      hin)

/-- Minimal remaining no-go from a nonempty linear-character input. -/
theorem no_D19_actionLevelMinimalRemainingBoundary_of_nonempty_linearCharacterInput
    (h : D19ActsOnMoore57 V Γ)
    (hin : Nonempty (D19ActsOnMoore57.D19LinearCharacterInput h)) :
    ¬ Nonempty (BranchOrbitABCActionLevelMinimalRemainingBoundary h) :=
  no_D19_actionLevelMinimalRemainingBoundary_of_components h
    (D19ActsOnMoore57.representationCharacterComponentsBoundary_of_nonempty_linearCharacterInput
      hin)

/-- Refined minimal remaining no-go from a nonempty linear-character input. -/
theorem no_D19_actionLevelMinimalRemainingRefinedBoundary_of_nonempty_linearCharacterInput
    (h : D19ActsOnMoore57 V Γ)
    (hin : Nonempty (D19ActsOnMoore57.D19LinearCharacterInput h)) :
    ¬ Nonempty
        (BranchOrbitABCActionLevelMinimalRemainingRefinedBoundary h) :=
  no_D19_actionLevelMinimalRemainingRefinedBoundary_of_components h
    (D19ActsOnMoore57.representationCharacterComponentsBoundary_of_nonempty_linearCharacterInput
      hin)

/-- Matching-equation refined minimal remaining no-go from a nonempty
linear-character input. -/
theorem no_D19_actionLevelMinimalRemainingRefinedMatchingBoundary_of_nonempty_linearCharacterInput
    (h : D19ActsOnMoore57 V Γ)
    (hin : Nonempty (D19ActsOnMoore57.D19LinearCharacterInput h)) :
    ¬ Nonempty
        (BranchOrbitABCActionLevelMinimalRemainingRefinedMatchingBoundary h) :=
  no_D19_actionLevelMinimalRemainingRefinedMatchingBoundary_of_components h
    (D19ActsOnMoore57.representationCharacterComponentsBoundary_of_nonempty_linearCharacterInput
      hin)

end

end Moore57
