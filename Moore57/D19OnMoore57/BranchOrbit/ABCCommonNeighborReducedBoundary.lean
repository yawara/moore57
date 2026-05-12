import Moore57.D19OnMoore57.BranchOrbit.ABCReducedCoordinateWitnessBoundary
import Moore57.D19OnMoore57.BranchOrbit.ABCEndpointCommonNeighborConcreteBoundary

/-!
# Common-neighbor reduced boundary

This action-level package replaces the endpoint fixedness-forcing input by the
more concrete swapped-pair common-neighbor input.  The conversion then uses the
formal common-neighbor fixedness lemma already packaged downstream.
-/

namespace Moore57

open Finset

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

local instance instCommonNeighborReducedBoundaryPFintype
    {h : D19ActsOnMoore57 V Γ}
    (labeling : BranchOrbitABCReflectionLabeling h) :
    Fintype labeling.data.toAFiberCoordinates.P :=
  labeling.data.toAFiberCoordinates.P_fintype

local instance instCommonNeighborReducedBoundaryDecidableEq
    (α : Type*) : DecidableEq α :=
  Classical.decEq α

/-- Action-level reduced package using the concrete endpoint common-neighbor
input. -/
structure BranchOrbitABCActionLevelCommonNeighborReducedBoundary
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
  doublingVertexPullback :
    BranchOrbitABCReflectionLabeling.MidpointExceptionDoublingMiddleVertexFixedPullbackBoundary
      labeling
  endpointMatchingAFixing :
    BranchOrbitABCReflectionLabeling.EndpointMatchingAFixingCoordinateBoundary
      labeling
  endpointCommonNeighbor :
    BranchOrbitABCReflectionLabeling.MidpointExceptionEndpointAdjCommonNeighborFixedBoundary
      labeling

namespace BranchOrbitABCActionLevelCommonNeighborReducedBoundary

variable {h : D19ActsOnMoore57 V Γ}

/-- Convert the common-neighbor reduced package to the previous reduced
coordinate witness package. -/
def toActionLevelReducedCoordinateWitnessBoundary
    (boundary :
      BranchOrbitABCActionLevelCommonNeighborReducedBoundary h) :
    BranchOrbitABCActionLevelReducedCoordinateWitnessBoundary h where
  starCounts := boundary.starCounts
  labeling := boundary.labeling
  middle := boundary.middle
  aFixing := boundary.aFixing
  referenceMatching := boundary.referenceMatching
  doublingVertexPullback := boundary.doublingVertexPullback
  endpointMatchingAFixing := boundary.endpointMatchingAFixing
  endpointAdjForcesAFixingFixed :=
    boundary.endpointCommonNeighbor
      |>.toMidpointExceptionEndpointAdjForcesAFixingFixedBoundary

/-- Convert the common-neighbor reduced package to the Lean-aware final
boundary. -/
noncomputable def toLeanAwareFixedStarFinalBoundary
    (boundary :
      BranchOrbitABCActionLevelCommonNeighborReducedBoundary h) :
    BranchOrbitABCReflectionLabeling.LeanAwareFixedStarFinalBoundary
      boundary.starCounts.toReflectionFixedStarBoundary boundary.labeling :=
  boundary.toActionLevelReducedCoordinateWitnessBoundary
    |>.toLeanAwareFixedStarFinalBoundary

end BranchOrbitABCActionLevelCommonNeighborReducedBoundary

/-- No action-level common-neighbor reduced package can coexist with the
representation component boundary. -/
theorem no_D19_actionLevelCommonNeighborReducedBoundary
    (h : D19ActsOnMoore57 V Γ) :
    ¬ ∃ _representationComponents :
          D19ActsOnMoore57.RepresentationCharacterComponentsBoundary h,
        Nonempty
          (BranchOrbitABCActionLevelCommonNeighborReducedBoundary h) := by
  rintro ⟨representationComponents, ⟨boundary⟩⟩
  exact no_D19_leanAwareFixedStarFinalBoundary h
    ⟨representationComponents,
      boundary.starCounts.toReflectionFixedStarBoundary,
      boundary.labeling,
      boundary.toLeanAwareFixedStarFinalBoundary⟩

end

end Moore57
