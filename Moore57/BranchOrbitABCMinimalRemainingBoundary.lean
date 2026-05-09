import Moore57.BranchOrbitABCCommonNeighborReducedBoundary
import Moore57.BranchOrbitABCDoublingCommonNeighborBasic
import Moore57.BranchOrbitABCEndpointCommonNeighborBasic
import Moore57.BranchOrbitABCMatchingTargetReflectionReduced

/-!
# Minimal remaining action-level boundary

This file packages the current smallest remaining action-level inputs into one
final-boundary structure.  The three reduced inputs are converted through the
existing common-neighbor and target-sign connectors before reusing the
common-neighbor reduced no-go theorem.
-/

namespace Moore57

open Finset

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

local instance instMinimalRemainingBoundaryPFintype
    {h : D19ActsOnMoore57 V Γ}
    (labeling : BranchOrbitABCReflectionLabeling h) :
    Fintype labeling.data.toAFiberCoordinates.P :=
  labeling.data.toAFiberCoordinates.P_fintype

local instance instMinimalRemainingBoundaryDecidableEq
    (α : Type*) : DecidableEq α :=
  Classical.decEq α

/-- Final action-level package after reducing the endpoint and doubling inputs
to their currently minimal remaining boundary forms. -/
structure BranchOrbitABCActionLevelMinimalRemainingBoundary
    (h : D19ActsOnMoore57 V Γ) where
  starCounts : ReflectionFixedNeighborStarCounts h
  labeling : BranchOrbitABCReflectionLabeling h
  middle :
    BranchOrbitABCReflectionLabeling.ReflectionFixedStarMiddleBoundary
      starCounts.toReflectionFixedStarBoundary labeling
  aFixing :
    BranchOrbitABCReflectionLabeling.ReflectionFixedStarAFixingBoundary
      starCounts.toReflectionFixedStarBoundary labeling
  referenceMatching :
    BranchOrbitABCReflectionLabeling.ReferenceMatchingPipelineBoundary labeling
  doublingBasic :
    BranchOrbitABCReflectionLabeling.MidpointExceptionDoublingMiddleCommonNeighborBasicBoundary
      labeling
  endpointTargetSign :
    BranchOrbitABCReflectionLabeling.EndpointMatchingAFixingTargetSignBoundary
      labeling
  endpointBasic :
    BranchOrbitABCReflectionLabeling.MidpointExceptionEndpointAdjCommonNeighborBasicBoundary
      labeling

namespace BranchOrbitABCActionLevelMinimalRemainingBoundary

variable {h : D19ActsOnMoore57 V Γ}

/-- Convert the minimal remaining package to the common-neighbor reduced
package. -/
def toActionLevelCommonNeighborReducedBoundary
    (boundary :
      BranchOrbitABCActionLevelMinimalRemainingBoundary h) :
    BranchOrbitABCActionLevelCommonNeighborReducedBoundary h where
  starCounts := boundary.starCounts
  labeling := boundary.labeling
  middle := boundary.middle
  aFixing := boundary.aFixing
  referenceMatching := boundary.referenceMatching
  doublingVertexPullback :=
    boundary.doublingBasic
      |>.toMidpointExceptionDoublingMiddleCommonNeighborBoundary
      |>.toMidpointExceptionDoublingMiddleVertexFixedPullbackBoundary
  endpointMatchingAFixing :=
    boundary.endpointTargetSign
      |>.toEndpointMatchingAFixingCoordinateBoundary
  endpointCommonNeighbor :=
    boundary.endpointBasic
      |>.toMidpointExceptionEndpointAdjCommonNeighborFixedBoundary

/-- Convert the minimal remaining package to the reduced coordinate witness
package. -/
def toActionLevelReducedCoordinateWitnessBoundary
    (boundary :
      BranchOrbitABCActionLevelMinimalRemainingBoundary h) :
    BranchOrbitABCActionLevelReducedCoordinateWitnessBoundary h :=
  boundary.toActionLevelCommonNeighborReducedBoundary
    |>.toActionLevelReducedCoordinateWitnessBoundary

/-- Convert the minimal remaining package to the Lean-aware final boundary. -/
noncomputable def toLeanAwareFixedStarFinalBoundary
    (boundary :
      BranchOrbitABCActionLevelMinimalRemainingBoundary h) :
    BranchOrbitABCReflectionLabeling.LeanAwareFixedStarFinalBoundary
      boundary.starCounts.toReflectionFixedStarBoundary boundary.labeling :=
  boundary.toActionLevelCommonNeighborReducedBoundary
    |>.toLeanAwareFixedStarFinalBoundary

end BranchOrbitABCActionLevelMinimalRemainingBoundary

/-- No action-level minimal remaining package can coexist with the
representation component boundary. -/
theorem no_D19_actionLevelMinimalRemainingBoundary
    (h : D19ActsOnMoore57 V Γ) :
    ¬ ∃ _representationComponents :
          D19ActsOnMoore57.RepresentationCharacterComponentsBoundary h,
        Nonempty
          (BranchOrbitABCActionLevelMinimalRemainingBoundary h) := by
  rintro ⟨representationComponents, ⟨boundary⟩⟩
  exact no_D19_actionLevelCommonNeighborReducedBoundary h
    ⟨representationComponents,
      ⟨boundary.toActionLevelCommonNeighborReducedBoundary⟩⟩

end

end Moore57
