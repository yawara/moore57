import Moore57.D19OnMoore57.BranchOrbit.BranchOrbitABCMinimalRemainingBoundary
import Moore57.D19OnMoore57.BranchOrbit.BranchOrbitABCDoublingRemainingBoundary
import Moore57.D19OnMoore57.BranchOrbit.BranchOrbitABCEndpointSignAdjacencyBoundary

/-!
# Refined minimal remaining action-level boundary

This file replaces the remaining basic endpoint and doubling inputs in
`BranchOrbitABCActionLevelMinimalRemainingBoundary` by the current refined
local boundaries.

The endpoint sign-adjacency boundary supplies the endpoint common-neighbor
input and, through the existing endpoint fixedness connector, the pointwise
endpoint non-adjacency needed by the refined doubling connector.
-/

namespace Moore57

open Finset

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

local instance instMinimalRemainingRefinedBoundaryPFintype
    {h : D19ActsOnMoore57 V Γ}
    (labeling : BranchOrbitABCReflectionLabeling h) :
    Fintype labeling.data.toAFiberCoordinates.P :=
  labeling.data.toAFiberCoordinates.P_fintype

local instance instMinimalRemainingRefinedBoundaryDecidableEq
    (α : Type*) : DecidableEq α :=
  Classical.decEq α

/-- Refined action-level package: the doubling input is reduced to reflected
adjacency plus endpoint pointwise non-adjacency derived from the endpoint
sign-adjacency package, and the endpoint basic input is replaced by the
endpoint sign-adjacency package. -/
structure BranchOrbitABCActionLevelMinimalRemainingRefinedBoundary
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
  doublingReflectedAdj :
    BranchOrbitABCReflectionLabeling.MidpointExceptionDoublingMiddleReflectedAdjBoundary
      labeling
  endpointTargetSign :
    BranchOrbitABCReflectionLabeling.EndpointMatchingAFixingTargetSignBoundary
      labeling
  endpointSignAdjacency :
    BranchOrbitABCReflectionLabeling.EndpointSignAdjacencyBoundary labeling

namespace BranchOrbitABCActionLevelMinimalRemainingRefinedBoundary

variable {h : D19ActsOnMoore57 V Γ}

/-- The endpoint sign-adjacency package gives the pointwise endpoint
non-adjacency used by the refined doubling connector. -/
def endpointPointwiseNonadj
    (boundary :
      BranchOrbitABCActionLevelMinimalRemainingRefinedBoundary h) :
    BranchOrbitABCReflectionLabeling.MidpointExceptionAFixingSupportEndpointPointwiseNonadjBoundary
      boundary.labeling :=
  boundary.endpointSignAdjacency
    |>.toMidpointExceptionEndpointAdjForcesAFixingFixedBoundary
    |>.toMidpointExceptionAFixingSupportEndpointPointwiseNonadjBoundary

/-- Recover the previous minimal remaining package from the refined fields. -/
def toActionLevelMinimalRemainingBoundary
    (boundary :
      BranchOrbitABCActionLevelMinimalRemainingRefinedBoundary h) :
    BranchOrbitABCActionLevelMinimalRemainingBoundary h where
  starCounts := boundary.starCounts
  labeling := boundary.labeling
  middle := boundary.middle
  aFixing := boundary.aFixing
  referenceMatching := boundary.referenceMatching
  doublingBasic :=
    boundary.doublingReflectedAdj
      |>.toMidpointExceptionDoublingMiddleCommonNeighborBasicBoundary
        boundary.endpointPointwiseNonadj
  endpointTargetSign := boundary.endpointTargetSign
  endpointBasic :=
    boundary.endpointSignAdjacency
      |>.toMidpointExceptionEndpointAdjCommonNeighborBasicBoundary

/-- Direct conversion to the common-neighbor reduced package. -/
def toActionLevelCommonNeighborReducedBoundary
    (boundary :
      BranchOrbitABCActionLevelMinimalRemainingRefinedBoundary h) :
    BranchOrbitABCActionLevelCommonNeighborReducedBoundary h where
  starCounts := boundary.starCounts
  labeling := boundary.labeling
  middle := boundary.middle
  aFixing := boundary.aFixing
  referenceMatching := boundary.referenceMatching
  doublingVertexPullback :=
    boundary.doublingReflectedAdj
      |>.toMidpointExceptionDoublingMiddleCommonNeighborBoundary
        boundary.endpointPointwiseNonadj
      |>.toMidpointExceptionDoublingMiddleVertexFixedPullbackBoundary
  endpointMatchingAFixing :=
    boundary.endpointTargetSign
      |>.toEndpointMatchingAFixingCoordinateBoundary
  endpointCommonNeighbor :=
    boundary.endpointSignAdjacency
      |>.toMidpointExceptionEndpointAdjCommonNeighborBasicBoundary
      |>.toMidpointExceptionEndpointAdjCommonNeighborFixedBoundary

/-- Convert the refined package to the reduced coordinate witness package. -/
def toActionLevelReducedCoordinateWitnessBoundary
    (boundary :
      BranchOrbitABCActionLevelMinimalRemainingRefinedBoundary h) :
    BranchOrbitABCActionLevelReducedCoordinateWitnessBoundary h :=
  boundary.toActionLevelCommonNeighborReducedBoundary
    |>.toActionLevelReducedCoordinateWitnessBoundary

/-- Convert the refined package to the Lean-aware final boundary. -/
noncomputable def toLeanAwareFixedStarFinalBoundary
    (boundary :
      BranchOrbitABCActionLevelMinimalRemainingRefinedBoundary h) :
    BranchOrbitABCReflectionLabeling.LeanAwareFixedStarFinalBoundary
      boundary.starCounts.toReflectionFixedStarBoundary boundary.labeling :=
  boundary.toActionLevelCommonNeighborReducedBoundary
    |>.toLeanAwareFixedStarFinalBoundary

end BranchOrbitABCActionLevelMinimalRemainingRefinedBoundary

/-- Matching-equation variant of the refined package. -/
structure BranchOrbitABCActionLevelMinimalRemainingRefinedMatchingBoundary
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
  doublingReflectedAdj :
    BranchOrbitABCReflectionLabeling.MidpointExceptionDoublingMiddleReflectedAdjBoundary
      labeling
  endpointTargetSign :
    BranchOrbitABCReflectionLabeling.EndpointMatchingAFixingTargetSignBoundary
      labeling
  endpointSignMatching :
    BranchOrbitABCReflectionLabeling.EndpointSignMatchingBoundary labeling

namespace BranchOrbitABCActionLevelMinimalRemainingRefinedMatchingBoundary

variable {h : D19ActsOnMoore57 V Γ}

/-- Convert the matching-equation package to the adjacency refined package. -/
def toActionLevelMinimalRemainingRefinedBoundary
    (boundary :
      BranchOrbitABCActionLevelMinimalRemainingRefinedMatchingBoundary h) :
    BranchOrbitABCActionLevelMinimalRemainingRefinedBoundary h where
  starCounts := boundary.starCounts
  labeling := boundary.labeling
  middle := boundary.middle
  aFixing := boundary.aFixing
  referenceMatching := boundary.referenceMatching
  doublingReflectedAdj := boundary.doublingReflectedAdj
  endpointTargetSign := boundary.endpointTargetSign
  endpointSignAdjacency :=
    boundary.endpointSignMatching
      |>.toEndpointSignAdjacencyBoundary

/-- Convert the matching-equation package to the previous minimal package. -/
def toActionLevelMinimalRemainingBoundary
    (boundary :
      BranchOrbitABCActionLevelMinimalRemainingRefinedMatchingBoundary h) :
    BranchOrbitABCActionLevelMinimalRemainingBoundary h :=
  boundary.toActionLevelMinimalRemainingRefinedBoundary
    |>.toActionLevelMinimalRemainingBoundary

/-- Direct conversion to the common-neighbor reduced package. -/
def toActionLevelCommonNeighborReducedBoundary
    (boundary :
      BranchOrbitABCActionLevelMinimalRemainingRefinedMatchingBoundary h) :
    BranchOrbitABCActionLevelCommonNeighborReducedBoundary h :=
  boundary.toActionLevelMinimalRemainingRefinedBoundary
    |>.toActionLevelCommonNeighborReducedBoundary

/-- Convert the matching-equation package to the Lean-aware final boundary. -/
noncomputable def toLeanAwareFixedStarFinalBoundary
    (boundary :
      BranchOrbitABCActionLevelMinimalRemainingRefinedMatchingBoundary h) :
    BranchOrbitABCReflectionLabeling.LeanAwareFixedStarFinalBoundary
      boundary.starCounts.toReflectionFixedStarBoundary boundary.labeling :=
  boundary.toActionLevelMinimalRemainingRefinedBoundary
    |>.toLeanAwareFixedStarFinalBoundary

end BranchOrbitABCActionLevelMinimalRemainingRefinedMatchingBoundary

/-- No refined minimal remaining package can coexist with the representation
component boundary. -/
theorem no_D19_actionLevelMinimalRemainingRefinedBoundary
    (h : D19ActsOnMoore57 V Γ) :
    ¬ ∃ _representationComponents :
          D19ActsOnMoore57.RepresentationCharacterComponentsBoundary h,
        Nonempty
          (BranchOrbitABCActionLevelMinimalRemainingRefinedBoundary h) := by
  rintro ⟨representationComponents, ⟨boundary⟩⟩
  exact no_D19_actionLevelCommonNeighborReducedBoundary h
    ⟨representationComponents,
      ⟨boundary.toActionLevelCommonNeighborReducedBoundary⟩⟩

/-- No matching-equation refined minimal remaining package can coexist with
the representation component boundary. -/
theorem no_D19_actionLevelMinimalRemainingRefinedMatchingBoundary
    (h : D19ActsOnMoore57 V Γ) :
    ¬ ∃ _representationComponents :
          D19ActsOnMoore57.RepresentationCharacterComponentsBoundary h,
        Nonempty
          (BranchOrbitABCActionLevelMinimalRemainingRefinedMatchingBoundary h) := by
  rintro ⟨representationComponents, ⟨boundary⟩⟩
  exact no_D19_actionLevelMinimalRemainingRefinedBoundary h
    ⟨representationComponents,
      ⟨boundary.toActionLevelMinimalRemainingRefinedBoundary⟩⟩

end

end Moore57
