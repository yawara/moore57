import Moore57.D19OnMoore57.BranchOrbit.ABCReferenceSolutionFromExceptions
import Moore57.D19OnMoore57.BranchOrbit.ABCReferenceSolutionGeometryBoundary
import Moore57.D19OnMoore57.BranchOrbit.ABCReferenceMatchingPipeline
import Moore57.D19OnMoore57.BranchOrbit.ABCExceptionCardOneBoundary
import Moore57.D19OnMoore57.BranchOrbit.ABCExceptionAllSupportBoundary

/-!
# Reference matching/local obstruction bridge

This file packages the local midpoint-exception obstruction inputs together
with the reference matching pipeline.  The local obstruction gives the finite
case boundary for `S_(d/2) ∩ E`; the reference matching pipeline then turns
that disjointness into reference-solution containment in `Eᶜ`, and finally into
vertex fixedness for the reference matching solutions.
-/

namespace Moore57

open Finset

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

local instance instReferenceMatchingLocalObstructionBridgePFintype
    {h : D19ActsOnMoore57 V Γ}
    (labeling : BranchOrbitABCReflectionLabeling h) :
    Fintype labeling.data.toAFiberCoordinates.P :=
  labeling.data.toAFiberCoordinates.P_fintype

local instance instReferenceMatchingLocalObstructionBridgeDecidableEq
    (α : Type*) : DecidableEq α :=
  Classical.decEq α

namespace BranchOrbitABCReflectionLabeling

variable {h : D19ActsOnMoore57 V Γ}

/-- Boundary package combining reference matching with the local obstruction
that rules out midpoint-exception intersections with the A-fixing reflection
support. -/
structure ReferenceMatchingLocalObstructionBoundary
    (star : ReflectionFixedStarBoundary h)
    (labeling : BranchOrbitABCReflectionLabeling h) : Prop where
  aFixing :
    BranchOrbitABCReflectionLabeling.ReflectionFixedStarAFixingBoundary
      star labeling
  referenceMatching :
    BranchOrbitABCReflectionLabeling.ReferenceMatchingPipelineBoundary
      labeling
  singletonFixed :
    BranchOrbitABCReflectionLabeling.MidpointExceptionAFixingSupportSingletonFixedBoundary
      labeling
  noAllEndpointAdj :
    BranchOrbitABCReflectionLabeling.MidpointExceptionAFixingSupportNoAllEndpointAdjBoundary
      labeling

namespace ReferenceMatchingLocalObstructionBoundary

variable {star : ReflectionFixedStarBoundary h}
variable {labeling : BranchOrbitABCReflectionLabeling h}

/-- The local obstruction fields supply the finite midpoint-exception case
boundary: A-fixing gives the two-point support size, singleton fixedness
excludes card one, and endpoint-adjacency obstruction excludes card two. -/
def toMidpointExceptionAFixingSupportCaseBoundary
    (boundary : ReferenceMatchingLocalObstructionBoundary star labeling) :
    MidpointExceptionAFixingSupportCaseBoundary labeling :=
  let supportCard :=
    boundary.aFixing.toAFixingReflectionFixedNeighborCardBoundary
  let noCardTwo :=
    boundary.noAllEndpointAdj.toMidpointExceptionAFixingSupportNoCardTwoBoundary
      boundary.referenceMatching.criterion
  boundary.singletonFixed.toMidpointExceptionAFixingSupportCaseBoundary
    supportCard
    (noCardTwo.no_card_two supportCard)

/-- Reference matching plus the local obstruction puts every reference
matching solution in the complement of the A-fixing reflection support. -/
noncomputable def toReferenceRotationMatchingSolutionAFixingSupportComplBoundary
    (boundary : ReferenceMatchingLocalObstructionBoundary star labeling) :
    ReferenceRotationMatchingSolutionAFixingSupportComplBoundary labeling :=
  boundary.toMidpointExceptionAFixingSupportCaseBoundary
    |>.toReferenceRotationMatchingSolutionAFixingSupportComplBoundary
      boundary.referenceMatching

/-- Reference matching plus the local obstruction fixes all reference
matching solution vertices under the A-fixing reflection. -/
noncomputable def toReferenceRotationMatchingSolutionVertexFixedBoundary
    (boundary : ReferenceMatchingLocalObstructionBoundary star labeling) :
    ReferenceRotationMatchingSolutionVertexFixedBoundary labeling :=
  boundary.toReferenceRotationMatchingSolutionAFixingSupportComplBoundary
    |>.toReferenceRotationMatchingSolutionVertexFixedBoundary

/-- Reference matching plus the local obstruction also gives the direct
reference-to-midpoint comparison boundary. -/
noncomputable def toReferenceRotationToMidpointReflectionBoundary
    (boundary : ReferenceMatchingLocalObstructionBoundary star labeling) :
    ReferenceRotationToMidpointReflectionBoundary labeling :=
  boundary.toReferenceRotationMatchingSolutionAFixingSupportComplBoundary
    |>.toReferenceRotationToMidpointReflectionBoundary

end ReferenceMatchingLocalObstructionBoundary

end BranchOrbitABCReflectionLabeling

end

end Moore57
