import Moore57.D19OnMoore57.BranchOrbit.ABCReferenceFiberMatchingEquationFrontier
import Moore57.D19OnMoore57.BranchOrbit.ABCExceptionCaseLocalObstruction
import Moore57.D19OnMoore57.BranchOrbit.ABCExceptionCaseWitnessBoundary

/-!
# Midpoint-disjointness frontier

This file exposes the current non-representation reductions for the
`MidpointExceptionDisjointAFixingSupportBoundary` input used by
`BranchOrbitABCReferenceFiberMatchingEquationFrontier`.

The raw disjointness field is already implied by the finite
`MidpointExceptionAFixingSupportCaseBoundary`: the A-fixing support has size
two, and the one- and two-point intersections with the midpoint exception set
are excluded.  The endpoint diagnostic package below records the slightly more
targeted inputs needed at the reference-fiber equation frontier: the existing
reference-matching pipeline supplies the midpoint criterion, so the card-two
exclusion may be supplied by the existing all-support endpoint-adjacency
obstruction.
-/

namespace Moore57

open Finset

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

local instance instMidpointDisjointnessFrontierPFintype
    {h : D19ActsOnMoore57 V Γ}
    (labeling : BranchOrbitABCReflectionLabeling h) :
    Fintype labeling.data.toAFiberCoordinates.P :=
  labeling.data.toAFiberCoordinates.P_fintype

local instance instMidpointDisjointnessFrontierDecidableEq
    (α : Type*) : DecidableEq α :=
  Classical.decEq α

namespace BranchOrbitABCReflectionLabeling

variable {h : D19ActsOnMoore57 V Γ}

namespace MidpointExceptionAFixingSupportCaseBoundary

variable {labeling : BranchOrbitABCReflectionLabeling h}

/-- Stable frontier alias: the finite case boundary is exactly enough to
supply the raw midpoint-exception/A-fixing-support disjointness boundary. -/
def toMidpointExceptionDisjointAFixingSupportBoundaryFrontier
    (boundary : MidpointExceptionAFixingSupportCaseBoundary labeling) :
    MidpointExceptionDisjointAFixingSupportBoundary labeling :=
  boundary.toMidpointExceptionDisjointAFixingSupportBoundary

/-- Package the reference-matching pipeline together with the disjointness
derived from the finite case boundary. -/
def toReferenceFiberMatchingEquationFrontierBoundary
    (boundary : MidpointExceptionAFixingSupportCaseBoundary labeling)
    (referenceMatching : ReferenceMatchingPipelineBoundary labeling) :
    ReferenceFiberMatchingEquationFrontierBoundary labeling where
  referenceMatching := referenceMatching
  midpointExceptionDisjoint :=
    boundary.toMidpointExceptionDisjointAFixingSupportBoundary

end MidpointExceptionAFixingSupportCaseBoundary

namespace MidpointExceptionAFixingSupportCaseWitnessBoundary

variable {star : ReflectionFixedStarBoundary h}
variable {labeling : BranchOrbitABCReflectionLabeling h}

/-- The witness-level package implies the raw midpoint-exception disjointness
boundary through the local obstruction and finite case split. -/
def toMidpointExceptionDisjointAFixingSupportBoundary
    (boundary :
      MidpointExceptionAFixingSupportCaseWitnessBoundary star labeling) :
    MidpointExceptionDisjointAFixingSupportBoundary labeling :=
  boundary.toMidpointExceptionAFixingSupportCaseBoundary
    |>.toMidpointExceptionDisjointAFixingSupportBoundary

/-- The witness-level package plus reference matching supplies the full
reference-fiber matching-equation frontier package. -/
def toReferenceFiberMatchingEquationFrontierBoundary
    (boundary :
      MidpointExceptionAFixingSupportCaseWitnessBoundary star labeling)
    (referenceMatching : ReferenceMatchingPipelineBoundary labeling) :
    ReferenceFiberMatchingEquationFrontierBoundary labeling where
  referenceMatching := referenceMatching
  midpointExceptionDisjoint :=
    boundary.toMidpointExceptionDisjointAFixingSupportBoundary

end MidpointExceptionAFixingSupportCaseWitnessBoundary

/-- Target-side diagnostic wrapper for the non-representation inputs that
currently replace the raw disjointness assumption at the reference-fiber
matching-equation frontier.

The `referenceMatching` field supplies the midpoint criterion used to turn the
endpoint-adjacency obstruction into the card-two exclusion.  The remaining
fields are the A-fixing support-size input and the card-one exclusion. -/
structure ReferenceFiberMatchingEquationMidpointDisjointnessBoundary
    (labeling : BranchOrbitABCReflectionLabeling h) : Prop where
  referenceMatching : ReferenceMatchingPipelineBoundary labeling
  support_card_boundary : AFixingReflectionFixedNeighborCardBoundary labeling
  no_card_one :
    ∀ d : ZMod 19, ∀ hd : d ≠ 0,
      (labeling.midpointExceptionAFixingSupportIntersection
        (midpointOf d) (midpointOf_ne_zero hd)).card ≠ 1
  noAllEndpointAdj :
    MidpointExceptionAFixingSupportNoAllEndpointAdjBoundary labeling

namespace ReferenceFiberMatchingEquationMidpointDisjointnessBoundary

variable {labeling : BranchOrbitABCReflectionLabeling h}

/-- The endpoint diagnostic wrapper supplies the existing card-two exclusion
through the midpoint criterion already present in the reference-matching
pipeline. -/
def toMidpointExceptionAFixingSupportNoCardTwoBoundary
    (boundary :
      ReferenceFiberMatchingEquationMidpointDisjointnessBoundary labeling) :
    MidpointExceptionAFixingSupportNoCardTwoBoundary labeling :=
  boundary.noAllEndpointAdj.toMidpointExceptionAFixingSupportNoCardTwoBoundary
    boundary.referenceMatching.criterion

/-- Collapse the diagnostic wrapper to the finite case boundary that already
implies disjointness. -/
def toMidpointExceptionAFixingSupportCaseBoundary
    (boundary :
      ReferenceFiberMatchingEquationMidpointDisjointnessBoundary labeling) :
    MidpointExceptionAFixingSupportCaseBoundary labeling where
  support_card_boundary := boundary.support_card_boundary
  no_card_one := boundary.no_card_one
  no_card_two := by
    intro d hd
    exact
      boundary.toMidpointExceptionAFixingSupportNoCardTwoBoundary.no_card_two
        boundary.support_card_boundary d hd

/-- Diagnostic wrapper to raw disjointness. -/
def toMidpointExceptionDisjointAFixingSupportBoundary
    (boundary :
      ReferenceFiberMatchingEquationMidpointDisjointnessBoundary labeling) :
    MidpointExceptionDisjointAFixingSupportBoundary labeling :=
  boundary.toMidpointExceptionAFixingSupportCaseBoundary
    |>.toMidpointExceptionDisjointAFixingSupportBoundary

/-- Diagnostic wrapper to the package consumed by
`BranchOrbitABCReferenceFiberMatchingEquationFrontier`. -/
def toReferenceFiberMatchingEquationFrontierBoundary
    (boundary :
      ReferenceFiberMatchingEquationMidpointDisjointnessBoundary labeling) :
    ReferenceFiberMatchingEquationFrontierBoundary labeling where
  referenceMatching := boundary.referenceMatching
  midpointExceptionDisjoint :=
    boundary.toMidpointExceptionDisjointAFixingSupportBoundary

end ReferenceFiberMatchingEquationMidpointDisjointnessBoundary

end BranchOrbitABCReflectionLabeling

namespace MidpointExceptionAFixingSupportLocalObstructionBoundary

variable {h : D19ActsOnMoore57 V Γ}
variable {star : ReflectionFixedStarBoundary h}
variable {labeling : BranchOrbitABCReflectionLabeling h}

/-- The local obstruction package implies the raw midpoint-exception
disjointness boundary via the finite case split. -/
def toMidpointExceptionDisjointAFixingSupportBoundary
    (boundary :
      MidpointExceptionAFixingSupportLocalObstructionBoundary star labeling) :
    BranchOrbitABCReflectionLabeling.MidpointExceptionDisjointAFixingSupportBoundary
      labeling :=
  boundary.toMidpointExceptionAFixingSupportCaseBoundary
    |>.toMidpointExceptionDisjointAFixingSupportBoundary

/-- The local obstruction package plus reference matching supplies the full
reference-fiber matching-equation frontier package. -/
def toReferenceFiberMatchingEquationFrontierBoundary
    (boundary :
      MidpointExceptionAFixingSupportLocalObstructionBoundary star labeling)
    (referenceMatching :
      BranchOrbitABCReflectionLabeling.ReferenceMatchingPipelineBoundary
        labeling) :
    BranchOrbitABCReflectionLabeling.ReferenceFiberMatchingEquationFrontierBoundary
      labeling where
  referenceMatching := referenceMatching
  midpointExceptionDisjoint :=
    boundary.toMidpointExceptionDisjointAFixingSupportBoundary

end MidpointExceptionAFixingSupportLocalObstructionBoundary

end

end Moore57
