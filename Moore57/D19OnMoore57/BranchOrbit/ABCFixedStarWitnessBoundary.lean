import Moore57.D19OnMoore57.BranchOrbit.ABCFixedStarLocalObstructionBoundary
import Moore57.D19OnMoore57.BranchOrbit.ABCExceptionCaseWitnessBoundary

/-!
# Fixed-star witness boundary

This file packages the newest witness-level midpoint-exception inputs at the
fixed-star level.  The witnesses first assemble the local obstruction package,
which then feeds the existing fixed-star local obstruction and lean-aware final
boundary.
-/

namespace Moore57

open Finset

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

local instance instFixedStarWitnessBoundaryPFintype
    {h : D19ActsOnMoore57 V Γ}
    (labeling : BranchOrbitABCReflectionLabeling h) :
    Fintype labeling.data.toAFiberCoordinates.P :=
  labeling.data.toAFiberCoordinates.P_fintype

local instance instFixedStarWitnessBoundaryDecidableEq
    (α : Type*) : DecidableEq α :=
  Classical.decEq α

namespace BranchOrbitABCReflectionLabeling

variable {h : D19ActsOnMoore57 V Γ}

/-- Fixed-star-level package using the witness inputs for the local midpoint
exception obstruction. -/
structure FixedStarWitnessBoundary
    (star : ReflectionFixedStarBoundary h)
    (labeling : BranchOrbitABCReflectionLabeling h) : Prop where
  middle : ReflectionFixedStarMiddleBoundary star labeling
  aFixing : ReflectionFixedStarAFixingBoundary star labeling
  referenceMatching : ReferenceMatchingPipelineBoundary labeling
  intersectionInvariant :
    MidpointExceptionAFixingSupportIntersectionInvariantBoundary labeling
  endpointNonadjWitness :
    MidpointExceptionAFixingSupportEndpointNonadjWitnessBoundary labeling

namespace FixedStarWitnessBoundary

variable {star : ReflectionFixedStarBoundary h}
variable {labeling : BranchOrbitABCReflectionLabeling h}

/-- Forget the fixed-star-level fields not needed for the witness-level
midpoint-exception case package. -/
def toMidpointExceptionAFixingSupportCaseWitnessBoundary
    (boundary : FixedStarWitnessBoundary star labeling) :
    MidpointExceptionAFixingSupportCaseWitnessBoundary star labeling where
  aFixing := boundary.aFixing
  intersectionInvariant := boundary.intersectionInvariant
  endpointNonadjWitness := boundary.endpointNonadjWitness

/-- Convert the witness package to the local midpoint-exception obstruction
package. -/
def toMidpointExceptionAFixingSupportLocalObstructionBoundary
    (boundary : FixedStarWitnessBoundary star labeling) :
    MidpointExceptionAFixingSupportLocalObstructionBoundary star labeling :=
  boundary.toMidpointExceptionAFixingSupportCaseWitnessBoundary
    |>.toMidpointExceptionAFixingSupportLocalObstructionBoundary

/-- Convert the witness package to the fixed-star local obstruction package. -/
def toFixedStarLocalObstructionBoundary
    (boundary : FixedStarWitnessBoundary star labeling) :
    FixedStarLocalObstructionBoundary star labeling where
  middle := boundary.middle
  referenceMatching := boundary.referenceMatching
  localObstruction :=
    boundary.toMidpointExceptionAFixingSupportLocalObstructionBoundary

/-- Convert the witness package to the lean-aware fixed-star final package. -/
noncomputable def toLeanAwareFixedStarFinalBoundary
    (boundary : FixedStarWitnessBoundary star labeling) :
    LeanAwareFixedStarFinalBoundary star labeling :=
  boundary.toFixedStarLocalObstructionBoundary
    |>.toLeanAwareFixedStarFinalBoundary

end FixedStarWitnessBoundary

end BranchOrbitABCReflectionLabeling

/-- No fixed-star witness package can coexist with the representation component
boundary. -/
theorem no_D19_fixedStarWitnessBoundary
    (h : D19ActsOnMoore57 V Γ) :
    ¬ ∃ _representationComponents :
          D19ActsOnMoore57.RepresentationCharacterComponentsBoundary h,
        ∃ star : ReflectionFixedStarBoundary h,
        ∃ labeling : BranchOrbitABCReflectionLabeling h,
          BranchOrbitABCReflectionLabeling.FixedStarWitnessBoundary
            star labeling := by
  rintro ⟨representationComponents, star, labeling, boundary⟩
  exact no_D19_leanAwareFixedStarFinalBoundary h
    ⟨representationComponents, star, labeling,
      boundary.toLeanAwareFixedStarFinalBoundary⟩

end

end Moore57
