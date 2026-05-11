import Moore57.BranchOrbitABCLeanAwareFinalBoundary
import Moore57.BranchOrbitABCExceptionCaseLocalObstruction
import Moore57.BranchOrbitABCReferenceMatchingLocalObstructionBridge

/-!
# Fixed-star local obstruction boundary

This file packages the local midpoint-exception obstruction at the fixed-star
level, before adding the action-level fixed-star count data.  It is the
natural intermediate form of the branch argument: once a fixed-star labeling,
reference matching, and the local one-point/two-point obstructions are
available, the existing lean-aware final boundary follows.
-/

namespace Moore57

open Finset

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

local instance instFixedStarLocalObstructionBoundaryPFintype
    {h : D19ActsOnMoore57 V Γ}
    (labeling : BranchOrbitABCReflectionLabeling h) :
    Fintype labeling.data.toAFiberCoordinates.P :=
  labeling.data.toAFiberCoordinates.P_fintype

local instance instFixedStarLocalObstructionBoundaryDecidableEq
    (α : Type*) : DecidableEq α :=
  Classical.decEq α

namespace BranchOrbitABCReflectionLabeling

variable {h : D19ActsOnMoore57 V Γ}

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

end BranchOrbitABCReflectionLabeling

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

end

end Moore57
