import Moore57.BranchOrbitABCMinimalRemainingLocalObstructionBoundary
import Moore57.BranchOrbitABCEquationInvariantCoordinateBoundary

/-!
# Singleton fixedness from midpoint-equation invariance

This file keeps the midpoint-exception `card = 1` step on the invariance side
of the argument.  It does not introduce another singleton-fixedness boundary:
it reuses the existing midpoint-equation-set invariance boundary to produce the
existing singleton-fixedness/no-card-one fields.
-/

namespace Moore57

open Finset

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

local instance instSingletonFixedFromInvarianceBoundaryPFintype
    {h : D19ActsOnMoore57 V Γ}
    (labeling : BranchOrbitABCReflectionLabeling h) :
    Fintype labeling.data.toAFiberCoordinates.P :=
  labeling.data.toAFiberCoordinates.P_fintype

local instance instSingletonFixedFromInvarianceBoundaryDecidableEq
    (α : Type*) : DecidableEq α :=
  Classical.decEq α

namespace BranchOrbitABCReflectionLabeling

variable {h : D19ActsOnMoore57 V Γ}

namespace MidpointEquationAFixingCoordinateBoundary

variable {labeling : BranchOrbitABCReflectionLabeling h}

/-- The raw midpoint-equation coordinate invariance boundary gives the existing
singleton-fixedness boundary once the midpoint reflection criterion is
available. -/
def toMidpointExceptionAFixingSupportSingletonFixedBoundary
    (boundary : MidpointEquationAFixingCoordinateBoundary labeling)
    (criterion : MidpointReflectionCriterionBoundary labeling) :
    MidpointExceptionAFixingSupportSingletonFixedBoundary labeling :=
  boundary.toMidpointEquationSetAFixingInvariantBoundary
    |>.toMidpointExceptionAFixingSupportSingletonFixedBoundary criterion

/-- Coordinate invariance gives the existing no-card-one boundary for the
midpoint-exception/A-fixing-support intersection. -/
def toMidpointExceptionAFixingSupportNoCardOneBoundary
    (boundary : MidpointEquationAFixingCoordinateBoundary labeling)
    (criterion : MidpointReflectionCriterionBoundary labeling) :
    MidpointExceptionAFixingSupportNoCardOneBoundary labeling :=
  boundary.toMidpointEquationSetAFixingInvariantBoundary
    |>.toMidpointExceptionAFixingSupportNoCardOneBoundary criterion

/-- Coordinate invariance supplies the `no_card_one` fact consumed by the
finite case split. -/
theorem no_card_one
    (boundary : MidpointEquationAFixingCoordinateBoundary labeling)
    (criterion : MidpointReflectionCriterionBoundary labeling)
    (d : ZMod 19) (hd : d ≠ 0) :
    (labeling.midpointExceptionAFixingSupportIntersection
      (midpointOf d) (midpointOf_ne_zero hd)).card ≠ 1 :=
  (boundary.toMidpointExceptionAFixingSupportNoCardOneBoundary criterion)
    |>.no_card_one d hd

end MidpointEquationAFixingCoordinateBoundary

namespace EndpointMatchingAFixingCoordinateBoundary

variable {labeling : BranchOrbitABCReflectionLabeling h}

/-- Endpoint matching compatibility under the A-fixing reflection gives the
existing singleton-fixedness boundary via midpoint-equation invariance. -/
def toMidpointExceptionAFixingSupportSingletonFixedBoundary
    (boundary : EndpointMatchingAFixingCoordinateBoundary labeling)
    (criterion : MidpointReflectionCriterionBoundary labeling) :
    MidpointExceptionAFixingSupportSingletonFixedBoundary labeling :=
  boundary.toMidpointEquationSetAFixingInvariantBoundary
    |>.toMidpointExceptionAFixingSupportSingletonFixedBoundary criterion

/-- Endpoint matching compatibility gives the existing no-card-one boundary. -/
def toMidpointExceptionAFixingSupportNoCardOneBoundary
    (boundary : EndpointMatchingAFixingCoordinateBoundary labeling)
    (criterion : MidpointReflectionCriterionBoundary labeling) :
    MidpointExceptionAFixingSupportNoCardOneBoundary labeling :=
  boundary.toMidpointEquationSetAFixingInvariantBoundary
    |>.toMidpointExceptionAFixingSupportNoCardOneBoundary criterion

/-- Endpoint matching compatibility supplies the `no_card_one` fact consumed by
the finite case split. -/
theorem no_card_one
    (boundary : EndpointMatchingAFixingCoordinateBoundary labeling)
    (criterion : MidpointReflectionCriterionBoundary labeling)
    (d : ZMod 19) (hd : d ≠ 0) :
    (labeling.midpointExceptionAFixingSupportIntersection
      (midpointOf d) (midpointOf_ne_zero hd)).card ≠ 1 :=
  (boundary.toMidpointExceptionAFixingSupportNoCardOneBoundary criterion)
    |>.no_card_one d hd

end EndpointMatchingAFixingCoordinateBoundary

end BranchOrbitABCReflectionLabeling

variable {h : D19ActsOnMoore57 V Γ}

/-- Local obstruction package where the card-one input is midpoint-equation-set
invariance, not singleton fixedness. -/
structure MidpointExceptionAFixingSupportLocalObstructionEquationInvariantBoundary
    (star : ReflectionFixedStarBoundary h)
    (labeling : BranchOrbitABCReflectionLabeling h) : Prop where
  aFixing :
    BranchOrbitABCReflectionLabeling.ReflectionFixedStarAFixingBoundary
      star labeling
  equationInvariant :
    BranchOrbitABCReflectionLabeling.MidpointEquationSetAFixingInvariantBoundary
      labeling
  noAllEndpointAdj :
    BranchOrbitABCReflectionLabeling.MidpointExceptionAFixingSupportNoAllEndpointAdjBoundary
      labeling

namespace MidpointExceptionAFixingSupportLocalObstructionEquationInvariantBoundary

variable {star : ReflectionFixedStarBoundary h}
variable {labeling : BranchOrbitABCReflectionLabeling h}

/-- The equation-invariance field supplies the existing singleton-fixedness
boundary through the midpoint reflection criterion attached to the fixed-star
boundary. -/
def singletonFixed
    (boundary :
      MidpointExceptionAFixingSupportLocalObstructionEquationInvariantBoundary
        star labeling) :
    BranchOrbitABCReflectionLabeling.MidpointExceptionAFixingSupportSingletonFixedBoundary
      labeling :=
  boundary.equationInvariant
    |>.toMidpointExceptionAFixingSupportSingletonFixedBoundary
      (labeling.midpointReflectionCriterionBoundary_of_fixedCenterLeaf
        star.toReflectionFixedCenterLeafBoundary)

/-- Local equation invariance supplies the no-card-one fact needed by the
finite case split. -/
theorem no_card_one
    (boundary :
      MidpointExceptionAFixingSupportLocalObstructionEquationInvariantBoundary
        star labeling)
    (d : ZMod 19) (hd : d ≠ 0) :
    (labeling.midpointExceptionAFixingSupportIntersection
      (midpointOf d) (midpointOf_ne_zero hd)).card ≠ 1 :=
  boundary.singletonFixed.no_card_one d hd

/-- Convert the equation-invariant local package to the existing local
obstruction package. -/
def toMidpointExceptionAFixingSupportLocalObstructionBoundary
    (boundary :
      MidpointExceptionAFixingSupportLocalObstructionEquationInvariantBoundary
        star labeling) :
    MidpointExceptionAFixingSupportLocalObstructionBoundary star labeling where
  aFixing := boundary.aFixing
  singletonFixed := boundary.singletonFixed
  noAllEndpointAdj := boundary.noAllEndpointAdj

/-- Convert directly to the finite midpoint-exception case boundary. -/
def toMidpointExceptionAFixingSupportCaseBoundary
    (boundary :
      MidpointExceptionAFixingSupportLocalObstructionEquationInvariantBoundary
        star labeling) :
    BranchOrbitABCReflectionLabeling.MidpointExceptionAFixingSupportCaseBoundary
      labeling :=
  boundary.toMidpointExceptionAFixingSupportLocalObstructionBoundary
    |>.toMidpointExceptionAFixingSupportCaseBoundary

end MidpointExceptionAFixingSupportLocalObstructionEquationInvariantBoundary

/-- Action-level local obstruction package where the singleton/card-one field
is replaced by midpoint-equation-set invariance. -/
structure BranchOrbitABCActionLevelLocalObstructionEquationInvariantBoundary
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
  exceptionDoublingGeometry :
    BranchOrbitABCReflectionLabeling.MidpointExceptionDoublingGeometryBoundary
      labeling
  equationInvariant :
    BranchOrbitABCReflectionLabeling.MidpointEquationSetAFixingInvariantBoundary
      labeling
  noAllEndpointAdj :
    BranchOrbitABCReflectionLabeling.MidpointExceptionAFixingSupportNoAllEndpointAdjBoundary
      labeling

namespace BranchOrbitABCActionLevelLocalObstructionEquationInvariantBoundary

variable {h : D19ActsOnMoore57 V Γ}

/-- The action-level equation-invariance field supplies the existing
singleton-fixedness boundary. -/
def singletonFixed
    (boundary :
      BranchOrbitABCActionLevelLocalObstructionEquationInvariantBoundary h) :
    BranchOrbitABCReflectionLabeling.MidpointExceptionAFixingSupportSingletonFixedBoundary
      boundary.labeling :=
  boundary.equationInvariant
    |>.toMidpointExceptionAFixingSupportSingletonFixedBoundary
      boundary.referenceMatching.criterion

/-- Action-level equation invariance supplies the no-card-one fact needed by
the finite case split. -/
theorem no_card_one
    (boundary :
      BranchOrbitABCActionLevelLocalObstructionEquationInvariantBoundary h)
    (d : ZMod 19) (hd : d ≠ 0) :
    (boundary.labeling.midpointExceptionAFixingSupportIntersection
      (midpointOf d) (midpointOf_ne_zero hd)).card ≠ 1 :=
  boundary.singletonFixed.no_card_one d hd

/-- Forget to the local equation-invariant package. -/
def toMidpointExceptionAFixingSupportLocalObstructionEquationInvariantBoundary
    (boundary :
      BranchOrbitABCActionLevelLocalObstructionEquationInvariantBoundary h) :
    MidpointExceptionAFixingSupportLocalObstructionEquationInvariantBoundary
      boundary.starCounts.toReflectionFixedStarBoundary boundary.labeling where
  aFixing := boundary.aFixing
  equationInvariant := boundary.equationInvariant
  noAllEndpointAdj := boundary.noAllEndpointAdj

/-- Convert to the existing action-level local obstruction package by deriving
singleton fixedness from equation invariance. -/
def toActionLevelLocalObstructionBoundary
    (boundary :
      BranchOrbitABCActionLevelLocalObstructionEquationInvariantBoundary h) :
    BranchOrbitABCActionLevelLocalObstructionBoundary h where
  starCounts := boundary.starCounts
  labeling := boundary.labeling
  middle := boundary.middle
  aFixing := boundary.aFixing
  referenceMatching := boundary.referenceMatching
  exceptionDoublingGeometry := boundary.exceptionDoublingGeometry
  singletonFixed := boundary.singletonFixed
  noAllEndpointAdj := boundary.noAllEndpointAdj

/-- Convert to the existing action-level case package. -/
noncomputable def toActionLevelCaseBoundary
    (boundary :
      BranchOrbitABCActionLevelLocalObstructionEquationInvariantBoundary h) :
    BranchOrbitABCActionLevelCaseBoundary h :=
  boundary.toActionLevelLocalObstructionBoundary
    |>.toActionLevelCaseBoundary

/-- Convert to the Lean-aware fixed-star final package consumed by the final
contradiction. -/
noncomputable def toLeanAwareFixedStarFinalBoundary
    (boundary :
      BranchOrbitABCActionLevelLocalObstructionEquationInvariantBoundary h) :
    BranchOrbitABCReflectionLabeling.LeanAwareFixedStarFinalBoundary
      boundary.starCounts.toReflectionFixedStarBoundary boundary.labeling :=
  boundary.toActionLevelLocalObstructionBoundary
    |>.toLeanAwareFixedStarFinalBoundary

end BranchOrbitABCActionLevelLocalObstructionEquationInvariantBoundary

/-- No action-level equation-invariant local obstruction package can coexist
with the representation component boundary. -/
theorem no_D19_actionLevelLocalObstructionEquationInvariantBoundary
    (h : D19ActsOnMoore57 V Γ) :
    ¬ ∃ _representationComponents :
          D19ActsOnMoore57.RepresentationCharacterComponentsBoundary h,
        Nonempty
          (BranchOrbitABCActionLevelLocalObstructionEquationInvariantBoundary
            h) := by
  rintro ⟨representationComponents, ⟨boundary⟩⟩
  exact no_D19_actionLevelLocalObstructionBoundary h
    ⟨representationComponents,
      ⟨boundary.toActionLevelLocalObstructionBoundary⟩⟩

end

end Moore57
