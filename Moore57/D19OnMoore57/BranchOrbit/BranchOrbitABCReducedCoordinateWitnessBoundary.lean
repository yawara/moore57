import Moore57.D19OnMoore57.BranchOrbit.BranchOrbitABCCoordinateWitnessFinalBoundary
import Moore57.D19OnMoore57.BranchOrbit.BranchOrbitABCEquationInvariantCoordinateBoundary
import Moore57.D19OnMoore57.BranchOrbit.BranchOrbitABCEndpointCommonNeighborBoundary

/-!
# Reduced coordinate witness boundary

This file exposes the current smallest action-level package:

* endpoint matching compatibility under the A-fixing coordinate reflection;
* endpoint adjacency forcing A-fixing fixedness;
* doubling vertex fixedness pullback.

The first two feed the coordinate witness package through existing connectors.
-/

namespace Moore57

open Finset

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

local instance instReducedCoordinateWitnessBoundaryPFintype
    {h : D19ActsOnMoore57 V Γ}
    (labeling : BranchOrbitABCReflectionLabeling h) :
    Fintype labeling.data.toAFiberCoordinates.P :=
  labeling.data.toAFiberCoordinates.P_fintype

local instance instReducedCoordinateWitnessBoundaryDecidableEq
    (α : Type*) : DecidableEq α :=
  Classical.decEq α

/-- Action-level package after reducing equation invariance and endpoint
non-adjacency to their current smaller geometric forms. -/
structure BranchOrbitABCActionLevelReducedCoordinateWitnessBoundary
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
  endpointAdjForcesAFixingFixed :
    BranchOrbitABCReflectionLabeling.MidpointExceptionEndpointAdjForcesAFixingFixedBoundary
      labeling

namespace BranchOrbitABCActionLevelReducedCoordinateWitnessBoundary

variable {h : D19ActsOnMoore57 V Γ}

/-- Convert the reduced package to the coordinate witness package. -/
def toActionLevelCoordinateWitnessBoundary
    (boundary :
      BranchOrbitABCActionLevelReducedCoordinateWitnessBoundary h) :
    BranchOrbitABCActionLevelCoordinateWitnessBoundary h where
  starCounts := boundary.starCounts
  labeling := boundary.labeling
  middle := boundary.middle
  aFixing := boundary.aFixing
  referenceMatching := boundary.referenceMatching
  doublingVertexPullback := boundary.doublingVertexPullback
  equationInvariant :=
    boundary.endpointMatchingAFixing
      |>.toMidpointEquationSetAFixingInvariantBoundary
  endpointPointwiseNonadj :=
    boundary.endpointAdjForcesAFixingFixed
      |>.toMidpointExceptionAFixingSupportEndpointPointwiseNonadjBoundary

/-- Convert the reduced package to the Lean-aware final boundary. -/
noncomputable def toLeanAwareFixedStarFinalBoundary
    (boundary :
      BranchOrbitABCActionLevelReducedCoordinateWitnessBoundary h) :
    BranchOrbitABCReflectionLabeling.LeanAwareFixedStarFinalBoundary
      boundary.starCounts.toReflectionFixedStarBoundary boundary.labeling :=
  boundary.toActionLevelCoordinateWitnessBoundary
    |>.toLeanAwareFixedStarFinalBoundary

end BranchOrbitABCActionLevelReducedCoordinateWitnessBoundary

/-- No action-level reduced coordinate witness package can coexist with the
representation component boundary. -/
theorem no_D19_actionLevelReducedCoordinateWitnessBoundary
    (h : D19ActsOnMoore57 V Γ) :
    ¬ ∃ _representationComponents :
          D19ActsOnMoore57.RepresentationCharacterComponentsBoundary h,
        Nonempty
          (BranchOrbitABCActionLevelReducedCoordinateWitnessBoundary h) := by
  rintro ⟨representationComponents, ⟨boundary⟩⟩
  exact no_D19_leanAwareFixedStarFinalBoundary h
    ⟨representationComponents,
      boundary.starCounts.toReflectionFixedStarBoundary,
      boundary.labeling,
      boundary.toLeanAwareFixedStarFinalBoundary⟩

end

end Moore57
