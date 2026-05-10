import Moore57.BranchOrbitABCReferenceMatchingLocalObstructionBridge
import Moore57.BranchOrbitABCMidpointDisjointnessFrontier
import Moore57.D19LabeledReflectionMatchingEquationFromDisjoint

/-!
# Reference matching/local obstruction frontier

This file connects `ReferenceMatchingLocalObstructionBoundary` to the
reference-fiber matching-equation frontier.  The local obstruction already
supplies the finite midpoint-exception case split; the midpoint-disjointness
frontier turns that case split into the raw disjointness package consumed by
`ReferenceFiberMatchingEquationFrontierBoundary`.
-/

namespace Moore57

open Finset

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

local instance instReferenceMatchingLocalObstructionFrontierPFintype
    {h : D19ActsOnMoore57 V Γ}
    (labeling : BranchOrbitABCReflectionLabeling h) :
    Fintype labeling.data.toAFiberCoordinates.P :=
  labeling.data.toAFiberCoordinates.P_fintype

local instance instReferenceMatchingLocalObstructionFrontierBranchDataPFintype
    {h : D19ActsOnMoore57 V Γ}
    (labeling : BranchOrbitABCReflectionLabeling h) :
    Fintype labeling.data.toBranchOrbitABCData.toAFiberCoordinates.P :=
  labeling.data.toBranchOrbitABCData.toAFiberCoordinates.P_fintype

local instance instReferenceMatchingLocalObstructionFrontierDecidableEq
    (α : Type*) : DecidableEq α :=
  Classical.decEq α

namespace BranchOrbitABCReflectionLabeling

variable {h : D19ActsOnMoore57 V Γ}

namespace ReferenceMatchingLocalObstructionBoundary

variable {star : ReflectionFixedStarBoundary h}
variable {labeling : BranchOrbitABCReflectionLabeling h}

/-- Reference matching plus the local obstruction supplies the raw
midpoint-exception/A-fixing-support disjointness boundary required by the
reference-fiber matching-equation frontier. -/
def toMidpointExceptionDisjointAFixingSupportBoundary
    (boundary : ReferenceMatchingLocalObstructionBoundary star labeling) :
    MidpointExceptionDisjointAFixingSupportBoundary labeling :=
  boundary.toMidpointExceptionAFixingSupportCaseBoundary
    |>.toMidpointExceptionDisjointAFixingSupportBoundary

/-- Reference matching plus the local obstruction supplies the complete
reference-fiber matching-equation frontier package. -/
def toReferenceFiberMatchingEquationFrontierBoundary
    (boundary : ReferenceMatchingLocalObstructionBoundary star labeling) :
    ReferenceFiberMatchingEquationFrontierBoundary labeling :=
  boundary.toMidpointExceptionAFixingSupportCaseBoundary
    |>.toReferenceFiberMatchingEquationFrontierBoundary
      boundary.referenceMatching

/-- Collapse the local-obstruction frontier package to the exact
reference-fiber matching equation in promoted branch coordinates. -/
theorem toReferenceFiberMatchingEquationCardTwo
    (boundary : ReferenceMatchingLocalObstructionBoundary star labeling) :
    ∀ d : ZMod 19, ∀ hd : d ≠ 0,
      ((Finset.univ :
          Finset
            labeling.data.toBranchOrbitABCData.toAFiberCoordinates.P).filter fun p =>
        AFiberCoordinates.matchingEquiv h.isMoore
            labeling.data.toBranchOrbitABCData.toAFiberCoordinates
            0 (0 + d) (index_ne_add_of_ne_zero hd) p =
          (labeling.data.toBranchOrbitABCData.toAFiberRotationEquivariance).coordPerm
            d 0 p).card =
        2 :=
  boundary.toReferenceFiberMatchingEquationFrontierBoundary
    |>.toReferenceFiberMatchingEquationCardTwo

end ReferenceMatchingLocalObstructionBoundary

/-- Canonical labeled-pair specialization: a local obstruction boundary on the
labeling induced by a labeled reflection pair gives the public
reference-fiber matching equation for that pair. -/
theorem referenceFiberMatchingEquationCardTwoOfPair_of_referenceMatchingLocalObstruction
    (hp : HasLabeledReflectionPair h)
    {star : ReflectionFixedStarBoundary h}
    (boundary :
      ReferenceMatchingLocalObstructionBoundary star
        (ofHasLabeledReflectionPair (h := h) hp)) :
    ReferenceFiberMatchingEquationCardTwoOfPair (h := h) hp :=
  boundary.toReferenceFiberMatchingEquationFrontierBoundary
    |>.toReferenceFiberMatchingEquationCardTwoOfPair hp

end BranchOrbitABCReflectionLabeling

/-- A labeled reflection pair plus a reference-matching local obstruction
boundary on its canonical labeling supplies the remaining public
labeled-reflection matching-equation connector. -/
theorem remainingLabeledReflectionMatchingEquationConnector_of_referenceMatchingLocalObstruction
    {h : D19ActsOnMoore57 V Γ}
    (hp : BranchOrbitABCReflectionLabeling.HasLabeledReflectionPair h)
    {star : ReflectionFixedStarBoundary h}
    (boundary :
      BranchOrbitABCReflectionLabeling.ReferenceMatchingLocalObstructionBoundary
        star
        (BranchOrbitABCReflectionLabeling.ofHasLabeledReflectionPair
          (h := h) hp)) :
    RemainingLabeledReflectionMatchingEquationConnector h :=
  remainingLabeledReflectionMatchingEquationConnector_of_referenceMatchingPipeline_disjoint
    (h := h) hp boundary.referenceMatching
    boundary.toMidpointExceptionDisjointAFixingSupportBoundary

end

end Moore57
