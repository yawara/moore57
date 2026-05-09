import Moore57.BranchOrbitABCFixedStarWitnessBoundary
import Moore57.BranchOrbitABCExceptionEquationInvariantBoundary
import Moore57.BranchOrbitABCExceptionEndpointPointwiseBoundary

/-!
# Fixed-star coordinate witness boundary

This file lowers the fixed-star witness package to the current smaller
coordinate-level inputs:

* midpoint-equation-set invariance under the A-fixing coordinate reflection;
* pointwise endpoint non-adjacency on the A-fixing moving support.
-/

namespace Moore57

open Finset

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

local instance instFixedStarCoordinateWitnessBoundaryPFintype
    {h : D19ActsOnMoore57 V Γ}
    (labeling : BranchOrbitABCReflectionLabeling h) :
    Fintype labeling.data.toAFiberCoordinates.P :=
  labeling.data.toAFiberCoordinates.P_fintype

local instance instFixedStarCoordinateWitnessBoundaryDecidableEq
    (α : Type*) : DecidableEq α :=
  Classical.decEq α

namespace BranchOrbitABCReflectionLabeling

variable {h : D19ActsOnMoore57 V Γ}

/-- Fixed-star package using the current coordinate-level witness inputs. -/
structure FixedStarCoordinateWitnessBoundary
    (star : ReflectionFixedStarBoundary h)
    (labeling : BranchOrbitABCReflectionLabeling h) : Prop where
  middle : ReflectionFixedStarMiddleBoundary star labeling
  aFixing : ReflectionFixedStarAFixingBoundary star labeling
  referenceMatching : ReferenceMatchingPipelineBoundary labeling
  equationInvariant : MidpointEquationSetAFixingInvariantBoundary labeling
  endpointPointwiseNonadj :
    MidpointExceptionAFixingSupportEndpointPointwiseNonadjBoundary labeling

namespace FixedStarCoordinateWitnessBoundary

variable {star : ReflectionFixedStarBoundary h}
variable {labeling : BranchOrbitABCReflectionLabeling h}

/-- Convert coordinate-level inputs to the previous fixed-star witness package. -/
def toFixedStarWitnessBoundary
    (boundary : FixedStarCoordinateWitnessBoundary star labeling) :
    FixedStarWitnessBoundary star labeling where
  middle := boundary.middle
  aFixing := boundary.aFixing
  referenceMatching := boundary.referenceMatching
  intersectionInvariant :=
    boundary.equationInvariant
      |>.toMidpointExceptionAFixingSupportIntersectionInvariantBoundary
        boundary.referenceMatching.criterion
  endpointNonadjWitness :=
    boundary.endpointPointwiseNonadj
      |>.toMidpointExceptionAFixingSupportEndpointNonadjWitnessBoundary
        boundary.aFixing.toAFixingReflectionFixedNeighborCardBoundary

/-- Convert the fixed-star coordinate witness package to the lean-aware final
boundary. -/
noncomputable def toLeanAwareFixedStarFinalBoundary
    (boundary : FixedStarCoordinateWitnessBoundary star labeling) :
    LeanAwareFixedStarFinalBoundary star labeling :=
  boundary.toFixedStarWitnessBoundary.toLeanAwareFixedStarFinalBoundary

end FixedStarCoordinateWitnessBoundary

end BranchOrbitABCReflectionLabeling

/-- No fixed-star coordinate witness package can coexist with the
representation component boundary. -/
theorem no_D19_fixedStarCoordinateWitnessBoundary
    (h : D19ActsOnMoore57 V Γ) :
    ¬ ∃ _representationComponents :
          D19ActsOnMoore57.RepresentationCharacterComponentsBoundary h,
        ∃ star : ReflectionFixedStarBoundary h,
        ∃ labeling : BranchOrbitABCReflectionLabeling h,
          BranchOrbitABCReflectionLabeling.FixedStarCoordinateWitnessBoundary
            star labeling := by
  rintro ⟨representationComponents, star, labeling, boundary⟩
  exact no_D19_leanAwareFixedStarFinalBoundary h
    ⟨representationComponents, star, labeling,
      boundary.toLeanAwareFixedStarFinalBoundary⟩

end

end Moore57
