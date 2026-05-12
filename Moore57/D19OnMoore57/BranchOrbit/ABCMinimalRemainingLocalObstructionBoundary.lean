import Moore57.D19OnMoore57.BranchOrbit.ABCMinimalRemainingRefinedBoundary
import Moore57.D19OnMoore57.BranchOrbit.ABCActionLevelLocalObstructionBoundary

/-!
# Refined minimal remaining boundary to local obstruction boundary

This file connects the refined minimal remaining action-level package to the
local obstruction package without restating either boundary.  The refined
endpoint sign-adjacency field already gives pointwise endpoint non-adjacency;
with the A-fixing support cardinality this gives the no-all-endpoint-adjacent
local obstruction field.  The reflected doubling adjacency field combines with
the same pointwise endpoint non-adjacency to give the existing doubling
geometry boundary.
-/

namespace Moore57

open Finset

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

local instance instMinimalRemainingLocalObstructionBoundaryPFintype
    {h : D19ActsOnMoore57 V Γ}
    (labeling : BranchOrbitABCReflectionLabeling h) :
    Fintype labeling.data.toAFiberCoordinates.P :=
  labeling.data.toAFiberCoordinates.P_fintype

local instance instMinimalRemainingLocalObstructionBoundaryDecidableEq
    (α : Type*) : DecidableEq α :=
  Classical.decEq α

namespace BranchOrbitABCActionLevelMinimalRemainingRefinedBoundary

variable {h : D19ActsOnMoore57 V Γ}

/-- The refined endpoint pointwise non-adjacency field gives the local
obstruction endpoint field once the A-fixing support-cardinality boundary is
read from `aFixing`. -/
def toMidpointExceptionAFixingSupportNoAllEndpointAdjBoundary
    (boundary :
      BranchOrbitABCActionLevelMinimalRemainingRefinedBoundary h) :
    BranchOrbitABCReflectionLabeling.MidpointExceptionAFixingSupportNoAllEndpointAdjBoundary
      boundary.labeling :=
  boundary.endpointPointwiseNonadj
    |>.toMidpointExceptionAFixingSupportNoAllEndpointAdjBoundary
      boundary.aFixing.toAFixingReflectionFixedNeighborCardBoundary

/-- The refined doubling reflected-adjacency field, together with endpoint
pointwise non-adjacency, supplies the existing doubling geometry boundary used
by the local obstruction package. -/
def toMidpointExceptionDoublingGeometryBoundary
    (boundary :
      BranchOrbitABCActionLevelMinimalRemainingRefinedBoundary h) :
    BranchOrbitABCReflectionLabeling.MidpointExceptionDoublingGeometryBoundary
      boundary.labeling :=
  boundary.doublingReflectedAdj
    |>.toMidpointExceptionDoublingMiddleCommonNeighborBoundary
      boundary.endpointPointwiseNonadj
    |>.toMidpointExceptionDoublingGeometryBoundary

/-- Convert a refined minimal remaining package to the local midpoint-exception
obstruction package, with singleton fixedness kept as the explicit remaining
local input. -/
def toMidpointExceptionAFixingSupportLocalObstructionBoundary
    (boundary :
      BranchOrbitABCActionLevelMinimalRemainingRefinedBoundary h)
    (singletonFixed :
      BranchOrbitABCReflectionLabeling.MidpointExceptionAFixingSupportSingletonFixedBoundary
        boundary.labeling) :
    MidpointExceptionAFixingSupportLocalObstructionBoundary
      boundary.starCounts.toReflectionFixedStarBoundary boundary.labeling where
  aFixing := boundary.aFixing
  singletonFixed := singletonFixed
  noAllEndpointAdj :=
    boundary.toMidpointExceptionAFixingSupportNoAllEndpointAdjBoundary

/-- Convert a refined minimal remaining package to the action-level local
obstruction package, with singleton fixedness kept as the explicit remaining
local input. -/
def toActionLevelLocalObstructionBoundary
    (boundary :
      BranchOrbitABCActionLevelMinimalRemainingRefinedBoundary h)
    (singletonFixed :
      BranchOrbitABCReflectionLabeling.MidpointExceptionAFixingSupportSingletonFixedBoundary
        boundary.labeling) :
    BranchOrbitABCActionLevelLocalObstructionBoundary h where
  starCounts := boundary.starCounts
  labeling := boundary.labeling
  middle := boundary.middle
  aFixing := boundary.aFixing
  referenceMatching := boundary.referenceMatching
  exceptionDoublingGeometry :=
    boundary.toMidpointExceptionDoublingGeometryBoundary
  singletonFixed := singletonFixed
  noAllEndpointAdj :=
    boundary.toMidpointExceptionAFixingSupportNoAllEndpointAdjBoundary

/-- Convert a refined minimal remaining package directly to the action-level
case boundary, again exposing singleton fixedness as the only extra local
input needed for the local obstruction route. -/
def toActionLevelCaseBoundary
    (boundary :
      BranchOrbitABCActionLevelMinimalRemainingRefinedBoundary h)
    (singletonFixed :
      BranchOrbitABCReflectionLabeling.MidpointExceptionAFixingSupportSingletonFixedBoundary
        boundary.labeling) :
    BranchOrbitABCActionLevelCaseBoundary h :=
  (boundary.toActionLevelLocalObstructionBoundary singletonFixed)
    |>.toActionLevelCaseBoundary

end BranchOrbitABCActionLevelMinimalRemainingRefinedBoundary

end

end Moore57
