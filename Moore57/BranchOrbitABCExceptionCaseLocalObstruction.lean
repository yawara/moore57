import Moore57.BranchOrbitABCExceptionCardOneBoundary
import Moore57.BranchOrbitABCExceptionAllSupportBoundary

/-!
# Local obstruction package for the midpoint-exception support case

This file bundles the current geometric obstruction inputs for the
`S_(d/2) ∩ E` cardinality split into the existing
`MidpointExceptionAFixingSupportCaseBoundary`.
-/

namespace Moore57

open Finset

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

local instance instExceptionCaseLocalObstructionPFintype
    {h : D19ActsOnMoore57 V Γ}
    (labeling : BranchOrbitABCReflectionLabeling h) :
    Fintype labeling.data.toAFiberCoordinates.P :=
  labeling.data.toAFiberCoordinates.P_fintype

local instance instExceptionCaseLocalObstructionDecidableEq
    (α : Type*) : DecidableEq α :=
  Classical.decEq α

variable {h : D19ActsOnMoore57 V Γ}

/-- Local geometric obstruction package for the two positive cardinality
cases of `S_(d/2) ∩ E`: the A-fixing fixed-star input supplies the support
cardinality, singleton intersections are fixed by the A-fixing reflection,
and the endpoint-adjacency obstruction excludes the all-support/card-two
case. -/
structure MidpointExceptionAFixingSupportLocalObstructionBoundary
    (star : ReflectionFixedStarBoundary h)
    (labeling : BranchOrbitABCReflectionLabeling h) : Prop where
  aFixing :
    BranchOrbitABCReflectionLabeling.ReflectionFixedStarAFixingBoundary
      star labeling
  singletonFixed :
    BranchOrbitABCReflectionLabeling.MidpointExceptionAFixingSupportSingletonFixedBoundary
      labeling
  noAllEndpointAdj :
    BranchOrbitABCReflectionLabeling.MidpointExceptionAFixingSupportNoAllEndpointAdjBoundary
      labeling

namespace MidpointExceptionAFixingSupportLocalObstructionBoundary

variable {star : ReflectionFixedStarBoundary h}
variable {labeling : BranchOrbitABCReflectionLabeling h}

/-- Convert the local obstruction package into the existing finite
cardinality case boundary. -/
def toMidpointExceptionAFixingSupportCaseBoundary
    (boundary :
      MidpointExceptionAFixingSupportLocalObstructionBoundary star labeling) :
    BranchOrbitABCReflectionLabeling.MidpointExceptionAFixingSupportCaseBoundary
      labeling :=
  boundary.singletonFixed.toMidpointExceptionAFixingSupportCaseBoundary
    boundary.aFixing.toAFixingReflectionFixedNeighborCardBoundary
    ((boundary.noAllEndpointAdj.toMidpointExceptionAFixingSupportNoCardTwoBoundary
      (labeling.midpointReflectionCriterionBoundary_of_fixedCenterLeaf
        star.toReflectionFixedCenterLeafBoundary)).no_card_two
      boundary.aFixing.toAFixingReflectionFixedNeighborCardBoundary)

end MidpointExceptionAFixingSupportLocalObstructionBoundary

/-- Direct constructor for the existing case boundary from the local
obstruction inputs. -/
def midpointExceptionAFixingSupportCaseBoundary_of_localObstruction
    {star : ReflectionFixedStarBoundary h}
    {labeling : BranchOrbitABCReflectionLabeling h}
    (aFixing :
      BranchOrbitABCReflectionLabeling.ReflectionFixedStarAFixingBoundary
        star labeling)
    (singletonFixed :
      BranchOrbitABCReflectionLabeling.MidpointExceptionAFixingSupportSingletonFixedBoundary
        labeling)
    (noAllEndpointAdj :
      BranchOrbitABCReflectionLabeling.MidpointExceptionAFixingSupportNoAllEndpointAdjBoundary
        labeling) :
    BranchOrbitABCReflectionLabeling.MidpointExceptionAFixingSupportCaseBoundary
      labeling :=
  (MidpointExceptionAFixingSupportLocalObstructionBoundary.mk
      aFixing singletonFixed noAllEndpointAdj)
    |>.toMidpointExceptionAFixingSupportCaseBoundary

end

end Moore57
