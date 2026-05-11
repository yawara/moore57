import Moore57.D19OnMoore57.BranchOrbit.BranchOrbitABCFixedStarWitnessBoundary
import Moore57.D19OnMoore57.BranchOrbit.BranchOrbitABCActionLevelWitnessBoundary
import Moore57.D19OnMoore57.BranchOrbit.BranchOrbitABCExceptionIntersectionInvariantDecomp

/-!
# Set-invariant witness boundaries

The previous witness packages used invariance of
`S_(d/2) ∩ E` under the A-fixing reflection.  The A-fixing support part of
that invariance is now proved, so this file exposes smaller packages that only
ask for invariance of the midpoint-exception set `S_(d/2)`.
-/

namespace Moore57

open Finset

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

local instance instSetInvariantWitnessBoundaryPFintype
    {h : D19ActsOnMoore57 V Γ}
    (labeling : BranchOrbitABCReflectionLabeling h) :
    Fintype labeling.data.toAFiberCoordinates.P :=
  labeling.data.toAFiberCoordinates.P_fintype

local instance instSetInvariantWitnessBoundaryDecidableEq
    (α : Type*) : DecidableEq α :=
  Classical.decEq α

namespace BranchOrbitABCReflectionLabeling

variable {h : D19ActsOnMoore57 V Γ}

/-- Fixed-star witness package with midpoint-exception-set invariance instead
of intersection invariance. -/
structure FixedStarSetInvariantWitnessBoundary
    (star : ReflectionFixedStarBoundary h)
    (labeling : BranchOrbitABCReflectionLabeling h) : Prop where
  middle : ReflectionFixedStarMiddleBoundary star labeling
  aFixing : ReflectionFixedStarAFixingBoundary star labeling
  referenceMatching : ReferenceMatchingPipelineBoundary labeling
  exceptionSetInvariant : MidpointExceptionSetAFixingInvariantBoundary labeling
  endpointNonadjWitness :
    MidpointExceptionAFixingSupportEndpointNonadjWitnessBoundary labeling

namespace FixedStarSetInvariantWitnessBoundary

variable {star : ReflectionFixedStarBoundary h}
variable {labeling : BranchOrbitABCReflectionLabeling h}

/-- Promote set invariance to the previously used intersection-invariant
witness package. -/
def toFixedStarWitnessBoundary
    (boundary : FixedStarSetInvariantWitnessBoundary star labeling) :
    FixedStarWitnessBoundary star labeling where
  middle := boundary.middle
  aFixing := boundary.aFixing
  referenceMatching := boundary.referenceMatching
  intersectionInvariant :=
    boundary.exceptionSetInvariant
      |>.toMidpointExceptionAFixingSupportIntersectionInvariantBoundary
  endpointNonadjWitness := boundary.endpointNonadjWitness

/-- Convert the set-invariant package to the lean-aware fixed-star final
boundary. -/
noncomputable def toLeanAwareFixedStarFinalBoundary
    (boundary : FixedStarSetInvariantWitnessBoundary star labeling) :
    LeanAwareFixedStarFinalBoundary star labeling :=
  boundary.toFixedStarWitnessBoundary.toLeanAwareFixedStarFinalBoundary

end FixedStarSetInvariantWitnessBoundary

end BranchOrbitABCReflectionLabeling

/-- Action-level package with midpoint-exception-set invariance instead of
intersection invariance. -/
structure BranchOrbitABCActionLevelSetInvariantWitnessBoundary
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
  doublingFixedPullback :
    BranchOrbitABCReflectionLabeling.MidpointExceptionDoublingMiddleFixedPullbackBoundary
      labeling
  exceptionSetInvariant :
    BranchOrbitABCReflectionLabeling.MidpointExceptionSetAFixingInvariantBoundary
      labeling
  endpointNonadjWitness :
    BranchOrbitABCReflectionLabeling.MidpointExceptionAFixingSupportEndpointNonadjWitnessBoundary
      labeling

namespace BranchOrbitABCActionLevelSetInvariantWitnessBoundary

variable {h : D19ActsOnMoore57 V Γ}

/-- Promote set invariance to the existing action-level witness package. -/
def toActionLevelWitnessBoundary
    (boundary : BranchOrbitABCActionLevelSetInvariantWitnessBoundary h) :
    BranchOrbitABCActionLevelWitnessBoundary h where
  starCounts := boundary.starCounts
  labeling := boundary.labeling
  middle := boundary.middle
  aFixing := boundary.aFixing
  referenceMatching := boundary.referenceMatching
  doublingFixedPullback := boundary.doublingFixedPullback
  intersectionInvariant :=
    boundary.exceptionSetInvariant
      |>.toMidpointExceptionAFixingSupportIntersectionInvariantBoundary
  endpointNonadjWitness := boundary.endpointNonadjWitness

/-- Convert the set-invariant action-level package to the lean-aware final
boundary. -/
noncomputable def toLeanAwareFixedStarFinalBoundary
    (boundary : BranchOrbitABCActionLevelSetInvariantWitnessBoundary h) :
    BranchOrbitABCReflectionLabeling.LeanAwareFixedStarFinalBoundary
      boundary.starCounts.toReflectionFixedStarBoundary boundary.labeling :=
  boundary.toActionLevelWitnessBoundary.toLeanAwareFixedStarFinalBoundary

end BranchOrbitABCActionLevelSetInvariantWitnessBoundary

/-- No action-level set-invariant witness package can coexist with the
representation component boundary. -/
theorem no_D19_actionLevelSetInvariantWitnessBoundary
    (h : D19ActsOnMoore57 V Γ) :
    ¬ ∃ _representationComponents :
          D19ActsOnMoore57.RepresentationCharacterComponentsBoundary h,
        Nonempty (BranchOrbitABCActionLevelSetInvariantWitnessBoundary h) := by
  rintro ⟨representationComponents, ⟨boundary⟩⟩
  exact no_D19_leanAwareFixedStarFinalBoundary h
    ⟨representationComponents,
      boundary.starCounts.toReflectionFixedStarBoundary,
      boundary.labeling,
      boundary.toLeanAwareFixedStarFinalBoundary⟩

end

end Moore57
