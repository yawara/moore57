import Moore57.D19OnMoore57.BranchOrbit.ABCLeanAwareFinalBoundary
import Moore57.D19OnMoore57.BranchOrbit.ABCExceptionCaseLocalObstruction
import Moore57.D19OnMoore57.BranchOrbit.ABCReferenceMatchingLocalObstructionBridge
import Moore57.D19OnMoore57.BranchOrbit.ABCExceptionCaseWitnessBoundary
import Moore57.D19OnMoore57.BranchOrbit.ABCExceptionEquationInvariantBoundary
import Moore57.D19OnMoore57.BranchOrbit.ABCExceptionEndpointPointwiseBoundary

/-!
# Fixed-star boundary refinement chain

This file unifies three thematic layers of the fixed-star midpoint-exception
obstruction:

* **Local obstruction** (`FixedStarLocalObstructionBoundary`): assemble the
  fixed-star middle field, reference matching, and the local one-point and
  two-point obstructions into the existing lean-aware final boundary.
* **Witness** (`FixedStarWitnessBoundary`): replace the local obstruction by
  intersection invariance and endpoint non-adjacency witnesses.  The
  witnesses first assemble the local obstruction package, which then feeds
  the existing fixed-star local obstruction boundary.
* **Coordinate witness** (`FixedStarCoordinateWitnessBoundary`): lower the
  fixed-star witness package to the current smaller coordinate-level inputs
  (midpoint-equation-set invariance under the A-fixing coordinate reflection
  and pointwise endpoint non-adjacency on the A-fixing moving support).
-/

namespace Moore57

open Finset

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

local instance instFixedStarPFintype
    {h : D19ActsOnMoore57 V Γ}
    (labeling : BranchOrbitABCReflectionLabeling h) :
    Fintype labeling.data.toAFiberCoordinates.P :=
  labeling.data.toAFiberCoordinates.P_fintype

local instance instFixedStarDecidableEq
    (α : Type*) : DecidableEq α :=
  Classical.decEq α

namespace BranchOrbitABCReflectionLabeling

variable {h : D19ActsOnMoore57 V Γ}

/-! ## Local obstruction package -/

/-- Fixed-star-level package of the current local obstruction inputs. -/
structure FixedStarLocalObstructionBoundary
    (star : ReflectionFixedStarBoundary h)
    (labeling : BranchOrbitABCReflectionLabeling h) : Prop where
  middle : ReflectionFixedStarMiddleBoundary star labeling
  referenceMatching : ReferenceMatchingPipelineBoundary labeling
  localObstruction :
    MidpointExceptionAFixingSupportLocalObstructionBoundary star labeling

namespace FixedStarLocalObstructionBoundary

variable {star : ReflectionFixedStarBoundary h}
variable {labeling : BranchOrbitABCReflectionLabeling h}

/-- The local obstruction fields assemble the finite midpoint-exception case
boundary. -/
def toMidpointExceptionAFixingSupportCaseBoundary
    (boundary : FixedStarLocalObstructionBoundary star labeling) :
    MidpointExceptionAFixingSupportCaseBoundary labeling :=
  boundary.localObstruction.toMidpointExceptionAFixingSupportCaseBoundary

/-- Forget the fixed-star middle field and expose the smaller
reference-matching/local-obstruction package. -/
def toReferenceMatchingLocalObstructionBoundary
    (boundary : FixedStarLocalObstructionBoundary star labeling) :
    ReferenceMatchingLocalObstructionBoundary star labeling where
  aFixing := boundary.localObstruction.aFixing
  referenceMatching := boundary.referenceMatching
  singletonFixed := boundary.localObstruction.singletonFixed
  noAllEndpointAdj := boundary.localObstruction.noAllEndpointAdj

/-- Reference matching plus the local obstruction fixes the reference
matching solutions under the A-fixing reflection. -/
noncomputable def toReferenceRotationMatchingSolutionVertexFixedBoundary
    (boundary : FixedStarLocalObstructionBoundary star labeling) :
    ReferenceRotationMatchingSolutionVertexFixedBoundary labeling :=
  boundary.toReferenceMatchingLocalObstructionBoundary
    |>.toReferenceRotationMatchingSolutionVertexFixedBoundary

/-- Reference matching plus the local obstruction puts reference matching
solutions in the complement of the A-fixing reflection support. -/
noncomputable def toReferenceRotationMatchingSolutionAFixingSupportComplBoundary
    (boundary : FixedStarLocalObstructionBoundary star labeling) :
    ReferenceRotationMatchingSolutionAFixingSupportComplBoundary labeling :=
  boundary.toReferenceMatchingLocalObstructionBoundary
    |>.toReferenceRotationMatchingSolutionAFixingSupportComplBoundary

/-- Reference matching plus the local obstruction gives the reference-to-
midpoint comparison boundary. -/
noncomputable def toReferenceRotationToMidpointReflectionBoundary
    (boundary : FixedStarLocalObstructionBoundary star labeling) :
    ReferenceRotationToMidpointReflectionBoundary labeling :=
  boundary.toReferenceRotationMatchingSolutionAFixingSupportComplBoundary
    |>.toReferenceRotationToMidpointReflectionBoundary

/-- Convert the fixed-star local obstruction package to the lean-aware final
package. -/
noncomputable def toLeanAwareFixedStarFinalBoundary
    (boundary : FixedStarLocalObstructionBoundary star labeling) :
    LeanAwareFixedStarFinalBoundary star labeling :=
  LeanAwareFixedStarFinalBoundary.of_referenceMatching_aFixingCenter_cases
    boundary.middle boundary.localObstruction.aFixing
    boundary.referenceMatching
    boundary.toMidpointExceptionAFixingSupportCaseBoundary

end FixedStarLocalObstructionBoundary

/-! ## Witness package -/

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

/-! ## Coordinate witness package -/

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

/-! ## No-go theorems -/

/-- No fixed-star local obstruction package can coexist with the representation
component boundary. -/
theorem no_D19_fixedStarLocalObstructionBoundary
    (h : D19ActsOnMoore57 V Γ) :
    ¬ ∃ _representationComponents :
          D19ActsOnMoore57.RepresentationCharacterComponentsBoundary h,
        ∃ star : ReflectionFixedStarBoundary h,
        ∃ labeling : BranchOrbitABCReflectionLabeling h,
          BranchOrbitABCReflectionLabeling.FixedStarLocalObstructionBoundary
            star labeling := by
  rintro ⟨representationComponents, star, labeling, boundary⟩
  exact no_D19_leanAwareFixedStarFinalBoundary h
    ⟨representationComponents, star, labeling,
      boundary.toLeanAwareFixedStarFinalBoundary⟩

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
