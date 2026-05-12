import Moore57.D19OnMoore57.BranchOrbit.BranchOrbitABCExceptionCardOneBoundary

/-!
# Invariant singleton boundary for the midpoint exception/support intersection

This file isolates the finite-set connector from invariance of
`S_(d/2) ∩ E` under the A-fixing coordinate reflection to the existing
singleton-fixedness boundary.  If the intersection is `{p}`, then `p` belongs
to it; invariance puts its reflected image back in the same singleton, so the
reflected image is `p`.
-/

namespace Moore57

open Finset

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

local instance instExceptionSingletonInvariantBoundaryPFintype
    {h : D19ActsOnMoore57 V Γ}
    (labeling : BranchOrbitABCReflectionLabeling h) :
    Fintype labeling.data.toAFiberCoordinates.P :=
  labeling.data.toAFiberCoordinates.P_fintype

local instance instExceptionSingletonInvariantBoundaryDecidableEq
    (α : Type*) : DecidableEq α :=
  Classical.decEq α

namespace BranchOrbitABCReflectionLabeling

variable {h : D19ActsOnMoore57 V Γ}

/-- Boundary input: each midpoint-exception/A-fixing-support intersection is
closed under the A-fixing coordinate reflection. -/
structure MidpointExceptionAFixingSupportIntersectionInvariantBoundary
    (labeling : BranchOrbitABCReflectionLabeling h) : Prop where
  aFiberReflection_mem_intersection :
    ∀ d : ZMod 19, ∀ hd : d ≠ 0,
      ∀ p : labeling.data.toAFiberCoordinates.P,
        p ∈ labeling.midpointExceptionAFixingSupportIntersection
          (midpointOf d) (midpointOf_ne_zero hd) →
        labeling.aFiberReflectionCoordPerm p ∈
          labeling.midpointExceptionAFixingSupportIntersection
            (midpointOf d) (midpointOf_ne_zero hd)

namespace MidpointExceptionAFixingSupportIntersectionInvariantBoundary

variable {labeling : BranchOrbitABCReflectionLabeling h}

/-- Invariance of a singleton finite set forces its unique point to be fixed. -/
def toMidpointExceptionAFixingSupportSingletonFixedBoundary
    (boundary :
      MidpointExceptionAFixingSupportIntersectionInvariantBoundary labeling) :
    MidpointExceptionAFixingSupportSingletonFixedBoundary labeling where
  fixed_of_singleton d hd p hsingleton := by
    have hp :
        p ∈ labeling.midpointExceptionAFixingSupportIntersection
          (midpointOf d) (midpointOf_ne_zero hd) := by
      simp [hsingleton]
    have himage :
        labeling.aFiberReflectionCoordPerm p ∈
          labeling.midpointExceptionAFixingSupportIntersection
            (midpointOf d) (midpointOf_ne_zero hd) :=
      boundary.aFiberReflection_mem_intersection d hd p hp
    simpa [hsingleton] using himage

/-- The invariant-boundary connector also supplies the existing no-card-one
boundary. -/
def toMidpointExceptionAFixingSupportNoCardOneBoundary
    (boundary :
      MidpointExceptionAFixingSupportIntersectionInvariantBoundary labeling) :
    MidpointExceptionAFixingSupportNoCardOneBoundary labeling :=
  boundary.toMidpointExceptionAFixingSupportSingletonFixedBoundary
    |>.toMidpointExceptionAFixingSupportNoCardOneBoundary

/-- Convert intersection invariance into the `no_card_one` field used by the
case boundary. -/
theorem no_card_one
    (boundary :
      MidpointExceptionAFixingSupportIntersectionInvariantBoundary labeling)
    (d : ZMod 19) (hd : d ≠ 0) :
    (labeling.midpointExceptionAFixingSupportIntersection
      (midpointOf d) (midpointOf_ne_zero hd)).card ≠ 1 :=
  boundary.toMidpointExceptionAFixingSupportNoCardOneBoundary.no_card_one d hd

end MidpointExceptionAFixingSupportIntersectionInvariantBoundary

/-- Direct connector from intersection invariance to singleton fixedness. -/
def midpointExceptionAFixingSupportSingletonFixedBoundary_of_intersection_invariant
    (labeling : BranchOrbitABCReflectionLabeling h)
    (aFiberReflection_mem_intersection :
      ∀ d : ZMod 19, ∀ hd : d ≠ 0,
        ∀ p : labeling.data.toAFiberCoordinates.P,
          p ∈ labeling.midpointExceptionAFixingSupportIntersection
            (midpointOf d) (midpointOf_ne_zero hd) →
          labeling.aFiberReflectionCoordPerm p ∈
            labeling.midpointExceptionAFixingSupportIntersection
              (midpointOf d) (midpointOf_ne_zero hd)) :
    MidpointExceptionAFixingSupportSingletonFixedBoundary labeling :=
  (MidpointExceptionAFixingSupportIntersectionInvariantBoundary.mk
      aFiberReflection_mem_intersection)
    |>.toMidpointExceptionAFixingSupportSingletonFixedBoundary

/-- Direct no-card-one connector from intersection invariance. -/
theorem no_card_one_of_intersection_invariant
    (labeling : BranchOrbitABCReflectionLabeling h)
    (aFiberReflection_mem_intersection :
      ∀ d : ZMod 19, ∀ hd : d ≠ 0,
        ∀ p : labeling.data.toAFiberCoordinates.P,
          p ∈ labeling.midpointExceptionAFixingSupportIntersection
            (midpointOf d) (midpointOf_ne_zero hd) →
          labeling.aFiberReflectionCoordPerm p ∈
            labeling.midpointExceptionAFixingSupportIntersection
              (midpointOf d) (midpointOf_ne_zero hd)) :
    ∀ d : ZMod 19, ∀ hd : d ≠ 0,
      (labeling.midpointExceptionAFixingSupportIntersection
        (midpointOf d) (midpointOf_ne_zero hd)).card ≠ 1 := by
  intro d hd
  exact
    (MidpointExceptionAFixingSupportIntersectionInvariantBoundary.mk
        aFiberReflection_mem_intersection).no_card_one d hd

end BranchOrbitABCReflectionLabeling

end

end Moore57
