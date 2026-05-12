import Moore57.D19OnMoore57.BranchOrbit.Action
import Moore57.D19OnMoore57.BranchOrbit.ABCFinalGapReportBoundary

/-!
# Endpoint-obstruction final boundary

This file gives the final-gap data a route to the local obstruction package
whose endpoint input is the actual endpoint obstruction on the A-fixing
support.  In particular, the action-level package below does not carry
`EndpointSignAdjacencyBoundary` or the stronger `EndpointSignMatchingBoundary`
as a primary field.
-/

namespace Moore57

open Finset

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

local instance instEndpointObstructionFinalBoundaryPFintype
    {h : D19ActsOnMoore57 V Γ}
    (labeling : BranchOrbitABCReflectionLabeling h) :
    Fintype labeling.data.toAFiberCoordinates.P :=
  labeling.data.toAFiberCoordinates.P_fintype

local instance instEndpointObstructionFinalBoundaryDecidableEq
    (α : Type*) : DecidableEq α :=
  Classical.decEq α

/-- Action-level endpoint-obstruction package.

The endpoint field is pointwise non-adjacency on the A-fixing moving support.
Singleton fixedness is kept as an explicit local input for the card-one branch,
and the pointwise endpoint obstruction supplies the no-all-endpoint-adjacent
field needed for the card-two branch. -/
structure BranchOrbitABCActionLevelEndpointObstructionBoundary
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
  endpointPointwiseNonadj :
    BranchOrbitABCReflectionLabeling.MidpointExceptionAFixingSupportEndpointPointwiseNonadjBoundary
      labeling
  singletonFixed :
    BranchOrbitABCReflectionLabeling.MidpointExceptionAFixingSupportSingletonFixedBoundary
      labeling

namespace BranchOrbitABCActionLevelEndpointObstructionBoundary

variable {h : D19ActsOnMoore57 V Γ}

/-- The pointwise endpoint obstruction gives the no-all-endpoint-adjacent
local obstruction field using the A-fixing support-cardinality boundary. -/
def toMidpointExceptionAFixingSupportNoAllEndpointAdjBoundary
    (boundary : BranchOrbitABCActionLevelEndpointObstructionBoundary h) :
    BranchOrbitABCReflectionLabeling.MidpointExceptionAFixingSupportNoAllEndpointAdjBoundary
      boundary.labeling :=
  boundary.endpointPointwiseNonadj
    |>.toMidpointExceptionAFixingSupportNoAllEndpointAdjBoundary
      boundary.aFixing.toAFixingReflectionFixedNeighborCardBoundary

/-- Reflected-middle adjacency plus endpoint pointwise non-adjacency supplies
the geometric doubling input used by the local obstruction package. -/
def toMidpointExceptionDoublingGeometryBoundary
    (boundary : BranchOrbitABCActionLevelEndpointObstructionBoundary h) :
    BranchOrbitABCReflectionLabeling.MidpointExceptionDoublingGeometryBoundary
      boundary.labeling :=
  boundary.doublingReflectedAdj
    |>.toMidpointExceptionDoublingMiddleCommonNeighborBoundary
      boundary.endpointPointwiseNonadj
    |>.toMidpointExceptionDoublingGeometryBoundary

/-- Convert the endpoint-obstruction package to the existing action-level
local obstruction package. -/
def toActionLevelLocalObstructionBoundary
    (boundary : BranchOrbitABCActionLevelEndpointObstructionBoundary h) :
    BranchOrbitABCActionLevelLocalObstructionBoundary h where
  starCounts := boundary.starCounts
  labeling := boundary.labeling
  middle := boundary.middle
  aFixing := boundary.aFixing
  referenceMatching := boundary.referenceMatching
  exceptionDoublingGeometry :=
    boundary.toMidpointExceptionDoublingGeometryBoundary
  singletonFixed := boundary.singletonFixed
  noAllEndpointAdj :=
    boundary.toMidpointExceptionAFixingSupportNoAllEndpointAdjBoundary

/-- Convert the endpoint-obstruction package directly to the action-level
case package. -/
def toActionLevelCaseBoundary
    (boundary : BranchOrbitABCActionLevelEndpointObstructionBoundary h) :
    BranchOrbitABCActionLevelCaseBoundary h :=
  boundary.toActionLevelLocalObstructionBoundary.toActionLevelCaseBoundary

/-- Convert the endpoint-obstruction package to the Lean-aware final package
consumed by the final contradiction. -/
noncomputable def toLeanAwareFixedStarFinalBoundary
    (boundary : BranchOrbitABCActionLevelEndpointObstructionBoundary h) :
    BranchOrbitABCReflectionLabeling.LeanAwareFixedStarFinalBoundary
      boundary.starCounts.toReflectionFixedStarBoundary boundary.labeling :=
  boundary.toActionLevelLocalObstructionBoundary
    |>.toLeanAwareFixedStarFinalBoundary

end BranchOrbitABCActionLevelEndpointObstructionBoundary

/-- No action-level endpoint-obstruction package can coexist with the
representation component boundary. -/
theorem no_D19_actionLevelEndpointObstructionBoundary
    (h : D19ActsOnMoore57 V Γ) :
    ¬ ∃ _representationComponents :
          D19ActsOnMoore57.RepresentationCharacterComponentsBoundary h,
        Nonempty (BranchOrbitABCActionLevelEndpointObstructionBoundary h) := by
  rintro ⟨representationComponents, ⟨boundary⟩⟩
  exact no_D19_actionLevelLocalObstructionBoundary h
    ⟨representationComponents,
      ⟨boundary.toActionLevelLocalObstructionBoundary⟩⟩

/-- Final-gap endpoint-obstruction package.

This reuses the final-gap report's doubling equation/support wrappers, but the
endpoint input is the pointwise endpoint obstruction plus singleton fixedness,
not endpoint sign adjacency or endpoint sign matching. -/
structure BranchOrbitABCEndpointObstructionFinalBoundary
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
  doublingReflectedEquation :
    BranchOrbitABCDoublingReflectedEquationIssueBoundary labeling
  supportSubsetException :
    BranchOrbitABCSupportSubsetExceptionIssueBoundary labeling
  endpointPointwiseNonadj :
    BranchOrbitABCReflectionLabeling.MidpointExceptionAFixingSupportEndpointPointwiseNonadjBoundary
      labeling
  singletonFixed :
    BranchOrbitABCReflectionLabeling.MidpointExceptionAFixingSupportSingletonFixedBoundary
      labeling

namespace BranchOrbitABCEndpointObstructionFinalBoundary

variable {h : D19ActsOnMoore57 V Γ}

/-- Convert the final-gap endpoint-obstruction package to the action-level
endpoint-obstruction package. -/
def toActionLevelEndpointObstructionBoundary
    (boundary : BranchOrbitABCEndpointObstructionFinalBoundary h) :
    BranchOrbitABCActionLevelEndpointObstructionBoundary h where
  starCounts := boundary.starCounts
  labeling := boundary.labeling
  middle := boundary.middle
  aFixing := boundary.aFixing
  referenceMatching := boundary.referenceMatching
  doublingReflectedAdj :=
    boundary.doublingReflectedEquation
      |>.toMidpointExceptionDoublingMiddleReflectedAdjBoundary
        boundary.supportSubsetException
  endpointPointwiseNonadj := boundary.endpointPointwiseNonadj
  singletonFixed := boundary.singletonFixed

/-- Convert the final-gap endpoint-obstruction package to the existing
action-level local obstruction package. -/
def toActionLevelLocalObstructionBoundary
    (boundary : BranchOrbitABCEndpointObstructionFinalBoundary h) :
    BranchOrbitABCActionLevelLocalObstructionBoundary h :=
  boundary.toActionLevelEndpointObstructionBoundary
    |>.toActionLevelLocalObstructionBoundary

/-- Convert the final-gap endpoint-obstruction package to the action-level
case package. -/
def toActionLevelCaseBoundary
    (boundary : BranchOrbitABCEndpointObstructionFinalBoundary h) :
    BranchOrbitABCActionLevelCaseBoundary h :=
  boundary.toActionLevelEndpointObstructionBoundary
    |>.toActionLevelCaseBoundary

/-- Convert the final-gap endpoint-obstruction package to the Lean-aware final
package consumed by the final contradiction. -/
noncomputable def toLeanAwareFixedStarFinalBoundary
    (boundary : BranchOrbitABCEndpointObstructionFinalBoundary h) :
    BranchOrbitABCReflectionLabeling.LeanAwareFixedStarFinalBoundary
      boundary.starCounts.toReflectionFixedStarBoundary boundary.labeling :=
  boundary.toActionLevelEndpointObstructionBoundary
    |>.toLeanAwareFixedStarFinalBoundary

end BranchOrbitABCEndpointObstructionFinalBoundary

/-- No final-gap endpoint-obstruction package can coexist with the
representation component boundary. -/
theorem no_D19_endpointObstructionFinalBoundary
    (h : D19ActsOnMoore57 V Γ) :
    ¬ ∃ _representationComponents :
          D19ActsOnMoore57.RepresentationCharacterComponentsBoundary h,
        Nonempty (BranchOrbitABCEndpointObstructionFinalBoundary h) := by
  rintro ⟨representationComponents, ⟨boundary⟩⟩
  exact no_D19_actionLevelEndpointObstructionBoundary h
    ⟨representationComponents,
      ⟨boundary.toActionLevelEndpointObstructionBoundary⟩⟩

end

end Moore57
