import Moore57.D19OnMoore57.BranchOrbit.ABCCommonNeighborReducedBoundary
import Moore57.D19OnMoore57.BranchOrbit.ABCDoublingCommonNeighborBasic
import Moore57.D19OnMoore57.BranchOrbit.ABCEndpointCommonNeighborBasic
import Moore57.D19OnMoore57.BranchOrbit.Matching
import Moore57.D19OnMoore57.BranchOrbit.ABCDoublingRemainingBoundary
import Moore57.D19OnMoore57.BranchOrbit.ABCEndpointSignAdjacencyBoundary
import Moore57.D19OnMoore57.BranchOrbit.Action

/-!
# Minimal remaining action-level boundary: refinement chain

This file unifies four thematic layers of the minimal remaining action-level
package:

* **Minimal package** (`BranchOrbitABCActionLevelMinimalRemainingBoundary`):
  the smallest action-level inputs, converted through existing common-neighbor
  and target-sign connectors before reusing the common-neighbor reduced
  no-go theorem.
* **Refined package**
  (`BranchOrbitABCActionLevelMinimalRemainingRefinedBoundary`,
  `…RefinedMatchingBoundary`): the doubling input is reduced to reflected
  adjacency plus endpoint pointwise non-adjacency derived from the endpoint
  sign-adjacency package; the endpoint basic input is replaced by the
  endpoint sign-adjacency (or matching-equation) package.
* **Local obstruction connectors**: the refined endpoint pointwise
  non-adjacency together with the A-fixing support cardinality supplies the
  no-all-endpoint-adjacent local obstruction field; the reflected doubling
  adjacency field combines with the same pointwise non-adjacency to give the
  existing doubling geometry boundary.
* **Complete local obstruction**: the endpoint target-sign field supplies
  singleton fixedness for the card-one midpoint-exception/support case via
  midpoint-equation invariance, giving a direct path from the refined
  package to the local obstruction package without an extra singleton input.
-/

namespace Moore57

open Finset

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

local instance instMinimalRemainingPFintype
    {h : D19ActsOnMoore57 V Γ}
    (labeling : BranchOrbitABCReflectionLabeling h) :
    Fintype labeling.data.toAFiberCoordinates.P :=
  labeling.data.toAFiberCoordinates.P_fintype

local instance instMinimalRemainingDecidableEq
    (α : Type*) : DecidableEq α :=
  Classical.decEq α

/-! ## Minimal action-level package -/

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

/-! ## Refined action-level package -/

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

/-! ## Local obstruction connectors -/

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

/-! ## Complete local obstruction (singleton fixedness from target sign) -/

/-- The endpoint target-sign field supplies singleton fixedness for the
card-one midpoint-exception/support case via midpoint-equation invariance. -/
def toMidpointExceptionAFixingSupportSingletonFixedBoundary
    (boundary :
      BranchOrbitABCActionLevelMinimalRemainingRefinedBoundary h) :
    BranchOrbitABCReflectionLabeling.MidpointExceptionAFixingSupportSingletonFixedBoundary
      boundary.labeling :=
  boundary.endpointTargetSign
    |>.toMidpointEquationSetAFixingInvariantBoundary
    |>.toMidpointExceptionAFixingSupportSingletonFixedBoundary
      boundary.referenceMatching.criterion

/-- Convert the refined minimal remaining package directly to the local
midpoint-exception obstruction package. -/
def toMidpointExceptionAFixingSupportLocalObstructionBoundary'
    (boundary :
      BranchOrbitABCActionLevelMinimalRemainingRefinedBoundary h) :
    MidpointExceptionAFixingSupportLocalObstructionBoundary
      boundary.starCounts.toReflectionFixedStarBoundary boundary.labeling :=
  boundary.toMidpointExceptionAFixingSupportLocalObstructionBoundary
    boundary.toMidpointExceptionAFixingSupportSingletonFixedBoundary

/-- Convert the refined minimal remaining package directly to the action-level
local obstruction boundary. -/
def toActionLevelLocalObstructionBoundary'
    (boundary :
      BranchOrbitABCActionLevelMinimalRemainingRefinedBoundary h) :
    BranchOrbitABCActionLevelLocalObstructionBoundary h :=
  boundary.toActionLevelLocalObstructionBoundary
    boundary.toMidpointExceptionAFixingSupportSingletonFixedBoundary

/-- Convert the refined minimal remaining package directly to the action-level
case boundary. -/
def toActionLevelCaseBoundary'
    (boundary :
      BranchOrbitABCActionLevelMinimalRemainingRefinedBoundary h) :
    BranchOrbitABCActionLevelCaseBoundary h :=
  boundary.toActionLevelLocalObstructionBoundary'
    |>.toActionLevelCaseBoundary

end BranchOrbitABCActionLevelMinimalRemainingRefinedBoundary

end

end Moore57
