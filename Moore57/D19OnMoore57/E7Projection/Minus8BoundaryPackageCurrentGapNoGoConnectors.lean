import Moore57.D19OnMoore57.E7Projection.Minus8BoundaryPackageNoGoConnectors
import Moore57.D19OnMoore57.LinearCharacter.NonemptyCurrentGapNoGoConnectors

/-!
# Current-gap no-go connectors for packaged E7/minus-8 boundaries

This file exposes the current branch-orbit no-go frontiers directly from the
Type-valued projection-character boundary packages.
-/

namespace Moore57

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

namespace D19ActsOnMoore57

variable {h : D19ActsOnMoore57 V Γ}

namespace E7Minus8CharacterReflectionCountBoundary

/-- Common-neighbor reduced current-gap no-go from the packaged direct character boundary. -/
theorem no_actionLevelCommonNeighborReducedBoundary
    (boundary : E7Minus8CharacterReflectionCountBoundary h) :
    ¬ Nonempty (BranchOrbitABCActionLevelCommonNeighborReducedBoundary h) :=
  no_D19_actionLevelCommonNeighborReducedBoundary_of_nonempty_linearCharacterInput
    h boundary.nonempty_d19LinearCharacterInput

/-- Minimal-remaining current-gap no-go from the packaged direct character boundary. -/
theorem no_actionLevelMinimalRemainingBoundary
    (boundary : E7Minus8CharacterReflectionCountBoundary h) :
    ¬ Nonempty (BranchOrbitABCActionLevelMinimalRemainingBoundary h) :=
  no_D19_actionLevelMinimalRemainingBoundary_of_nonempty_linearCharacterInput
    h boundary.nonempty_d19LinearCharacterInput

/-- Refined minimal-remaining current-gap no-go from the packaged direct character boundary. -/
theorem no_actionLevelMinimalRemainingRefinedBoundary
    (boundary : E7Minus8CharacterReflectionCountBoundary h) :
    ¬ Nonempty (BranchOrbitABCActionLevelMinimalRemainingRefinedBoundary h) :=
  no_D19_actionLevelMinimalRemainingRefinedBoundary_of_nonempty_linearCharacterInput
    h boundary.nonempty_d19LinearCharacterInput

/-- Matching-equation refined minimal-remaining current-gap no-go from the packaged direct
character boundary. -/
theorem no_actionLevelMinimalRemainingRefinedMatchingBoundary
    (boundary : E7Minus8CharacterReflectionCountBoundary h) :
    ¬ Nonempty (BranchOrbitABCActionLevelMinimalRemainingRefinedMatchingBoundary h) :=
  no_D19_actionLevelMinimalRemainingRefinedMatchingBoundary_of_nonempty_linearCharacterInput
    h boundary.nonempty_d19LinearCharacterInput

end E7Minus8CharacterReflectionCountBoundary

namespace E7Minus8InversePairTraceReflectionCountBoundary

/-- Common-neighbor reduced current-gap no-go from the packaged inverse-pair trace boundary. -/
theorem no_actionLevelCommonNeighborReducedBoundary
    (boundary : E7Minus8InversePairTraceReflectionCountBoundary h) :
    ¬ Nonempty (BranchOrbitABCActionLevelCommonNeighborReducedBoundary h) :=
  no_D19_actionLevelCommonNeighborReducedBoundary_of_nonempty_linearCharacterInput
    h boundary.nonempty_d19LinearCharacterInput

/-- Minimal-remaining current-gap no-go from the packaged inverse-pair trace boundary. -/
theorem no_actionLevelMinimalRemainingBoundary
    (boundary : E7Minus8InversePairTraceReflectionCountBoundary h) :
    ¬ Nonempty (BranchOrbitABCActionLevelMinimalRemainingBoundary h) :=
  no_D19_actionLevelMinimalRemainingBoundary_of_nonempty_linearCharacterInput
    h boundary.nonempty_d19LinearCharacterInput

/-- Refined minimal-remaining current-gap no-go from the packaged inverse-pair trace boundary. -/
theorem no_actionLevelMinimalRemainingRefinedBoundary
    (boundary : E7Minus8InversePairTraceReflectionCountBoundary h) :
    ¬ Nonempty (BranchOrbitABCActionLevelMinimalRemainingRefinedBoundary h) :=
  no_D19_actionLevelMinimalRemainingRefinedBoundary_of_nonempty_linearCharacterInput
    h boundary.nonempty_d19LinearCharacterInput

/-- Matching-equation refined minimal-remaining current-gap no-go from the packaged inverse-pair
trace boundary. -/
theorem no_actionLevelMinimalRemainingRefinedMatchingBoundary
    (boundary : E7Minus8InversePairTraceReflectionCountBoundary h) :
    ¬ Nonempty (BranchOrbitABCActionLevelMinimalRemainingRefinedMatchingBoundary h) :=
  no_D19_actionLevelMinimalRemainingRefinedMatchingBoundary_of_nonempty_linearCharacterInput
    h boundary.nonempty_d19LinearCharacterInput

end E7Minus8InversePairTraceReflectionCountBoundary

end D19ActsOnMoore57

end

end Moore57
