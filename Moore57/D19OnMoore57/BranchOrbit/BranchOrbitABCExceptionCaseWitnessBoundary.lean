import Moore57.D19OnMoore57.BranchOrbit.BranchOrbitABCExceptionCaseLocalObstruction
import Moore57.D19OnMoore57.BranchOrbit.BranchOrbitABCExceptionSingletonInvariantBoundary
import Moore57.D19OnMoore57.BranchOrbit.BranchOrbitABCExceptionEndpointWitnessBoundary

/-!
# Witness-level midpoint exception case boundary

This file connects two more geometric witness forms to the existing finite
case package for `S_(d/2) ∩ E`:

* invariance of the intersection under the A-fixing reflection excludes the
  singleton case;
* a pointwise non-adjacency witness excludes the all-support/card-two case.
-/

namespace Moore57

open Finset

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

local instance instExceptionCaseWitnessBoundaryPFintype
    {h : D19ActsOnMoore57 V Γ}
    (labeling : BranchOrbitABCReflectionLabeling h) :
    Fintype labeling.data.toAFiberCoordinates.P :=
  labeling.data.toAFiberCoordinates.P_fintype

local instance instExceptionCaseWitnessBoundaryDecidableEq
    (α : Type*) : DecidableEq α :=
  Classical.decEq α

namespace BranchOrbitABCReflectionLabeling

variable {h : D19ActsOnMoore57 V Γ}

/-- Witness-level obstruction package for the positive cardinality cases of
`S_(d/2) ∩ E`. -/
structure MidpointExceptionAFixingSupportCaseWitnessBoundary
    (star : ReflectionFixedStarBoundary h)
    (labeling : BranchOrbitABCReflectionLabeling h) : Prop where
  aFixing : ReflectionFixedStarAFixingBoundary star labeling
  intersectionInvariant :
    MidpointExceptionAFixingSupportIntersectionInvariantBoundary labeling
  endpointNonadjWitness :
    MidpointExceptionAFixingSupportEndpointNonadjWitnessBoundary labeling

namespace MidpointExceptionAFixingSupportCaseWitnessBoundary

variable {star : ReflectionFixedStarBoundary h}
variable {labeling : BranchOrbitABCReflectionLabeling h}

/-- The witness-level fields imply the local obstruction package used by the
case-boundary connector. -/
def toMidpointExceptionAFixingSupportLocalObstructionBoundary
    (boundary :
      MidpointExceptionAFixingSupportCaseWitnessBoundary star labeling) :
    MidpointExceptionAFixingSupportLocalObstructionBoundary star labeling where
  aFixing := boundary.aFixing
  singletonFixed :=
    boundary.intersectionInvariant
      |>.toMidpointExceptionAFixingSupportSingletonFixedBoundary
  noAllEndpointAdj :=
    boundary.endpointNonadjWitness
      |>.toMidpointExceptionAFixingSupportNoAllEndpointAdjBoundary

/-- Convert the witness-level package into the finite midpoint-exception case
boundary. -/
def toMidpointExceptionAFixingSupportCaseBoundary
    (boundary :
      MidpointExceptionAFixingSupportCaseWitnessBoundary star labeling) :
    MidpointExceptionAFixingSupportCaseBoundary labeling :=
  boundary.toMidpointExceptionAFixingSupportLocalObstructionBoundary
    |>.toMidpointExceptionAFixingSupportCaseBoundary

end MidpointExceptionAFixingSupportCaseWitnessBoundary

end BranchOrbitABCReflectionLabeling

end

end Moore57
