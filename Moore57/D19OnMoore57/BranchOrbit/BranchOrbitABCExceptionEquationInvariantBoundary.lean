import Moore57.D19OnMoore57.BranchOrbit.BranchOrbitABCExceptionIntersectionInvariantDecomp

/-!
# Reducing midpoint-exception invariance to midpoint-equation invariance

This file packages the boundary step that replaces direct invariance of the
midpoint-exception set by invariance of the equivalent midpoint-equation set,
assuming the existing midpoint reflection criterion.
-/

namespace Moore57

open Finset

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

namespace BranchOrbitABCReflectionLabeling

variable {h : D19ActsOnMoore57 V Γ}

/-- Boundary input: each midpoint-equation set is closed under the A-fixing
coordinate reflection. -/
structure MidpointEquationSetAFixingInvariantBoundary
    (labeling : BranchOrbitABCReflectionLabeling h) : Prop where
  aFiberReflection_mem_midpointEquationSet :
    ∀ d : ZMod 19, ∀ hd : d ≠ 0,
      ∀ p : labeling.data.toAFiberCoordinates.P,
        p ∈ labeling.midpointEquationSet
          (midpointOf d) (midpointOf_ne_zero hd) →
        labeling.aFiberReflectionCoordPerm p ∈
          labeling.midpointEquationSet
            (midpointOf d) (midpointOf_ne_zero hd)

namespace MidpointEquationSetAFixingInvariantBoundary

variable {labeling : BranchOrbitABCReflectionLabeling h}

/-- Under the midpoint criterion, midpoint-equation-set invariance gives
midpoint-exception-set invariance. -/
def toMidpointExceptionSetAFixingInvariantBoundary
    (boundary : MidpointEquationSetAFixingInvariantBoundary labeling)
    (criterion : MidpointReflectionCriterionBoundary labeling) :
    MidpointExceptionSetAFixingInvariantBoundary labeling where
  aFiberReflection_mem_midpointExceptionSet d hd p hp := by
    exact
      (criterion.midpoint_equation_iff_exception
        (midpointOf d) (midpointOf_ne_zero hd)
        (labeling.aFiberReflectionCoordPerm p)).1
        (boundary.aFiberReflection_mem_midpointEquationSet d hd p
          ((criterion.midpoint_equation_iff_exception
            (midpointOf d) (midpointOf_ne_zero hd) p).2 hp))

/-- Direct connector to invariance of the midpoint-exception/A-fixing-support
intersection. -/
def toMidpointExceptionAFixingSupportIntersectionInvariantBoundary
    (boundary : MidpointEquationSetAFixingInvariantBoundary labeling)
    (criterion : MidpointReflectionCriterionBoundary labeling) :
    MidpointExceptionAFixingSupportIntersectionInvariantBoundary labeling :=
  (boundary.toMidpointExceptionSetAFixingInvariantBoundary criterion)
    |>.toMidpointExceptionAFixingSupportIntersectionInvariantBoundary

/-- Direct connector to the existing singleton-fixedness boundary. -/
def toMidpointExceptionAFixingSupportSingletonFixedBoundary
    (boundary : MidpointEquationSetAFixingInvariantBoundary labeling)
    (criterion : MidpointReflectionCriterionBoundary labeling) :
    MidpointExceptionAFixingSupportSingletonFixedBoundary labeling :=
  (boundary.toMidpointExceptionSetAFixingInvariantBoundary criterion)
    |>.toMidpointExceptionAFixingSupportSingletonFixedBoundary

/-- Direct connector to the existing no-card-one boundary. -/
def toMidpointExceptionAFixingSupportNoCardOneBoundary
    (boundary : MidpointEquationSetAFixingInvariantBoundary labeling)
    (criterion : MidpointReflectionCriterionBoundary labeling) :
    MidpointExceptionAFixingSupportNoCardOneBoundary labeling :=
  (boundary.toMidpointExceptionSetAFixingInvariantBoundary criterion)
    |>.toMidpointExceptionAFixingSupportNoCardOneBoundary

/-- The midpoint-equation-set invariance boundary, together with the midpoint
criterion, supplies the existing no-card-one theorem for the intersection. -/
theorem no_card_one
    (boundary : MidpointEquationSetAFixingInvariantBoundary labeling)
    (criterion : MidpointReflectionCriterionBoundary labeling)
    (d : ZMod 19) (hd : d ≠ 0) :
    (labeling.midpointExceptionAFixingSupportIntersection
      (midpointOf d) (midpointOf_ne_zero hd)).card ≠ 1 :=
  (boundary.toMidpointExceptionAFixingSupportNoCardOneBoundary criterion)
    |>.no_card_one d hd

end MidpointEquationSetAFixingInvariantBoundary

/-- Direct constructor from pointwise midpoint-equation-set invariance to
midpoint-exception-set invariance, assuming the midpoint criterion. -/
def midpointExceptionSetAFixingInvariantBoundary_of_equationSet_invariant
    (labeling : BranchOrbitABCReflectionLabeling h)
    (criterion : MidpointReflectionCriterionBoundary labeling)
    (aFiberReflection_mem_midpointEquationSet :
      ∀ d : ZMod 19, ∀ hd : d ≠ 0,
        ∀ p : labeling.data.toAFiberCoordinates.P,
          p ∈ labeling.midpointEquationSet
            (midpointOf d) (midpointOf_ne_zero hd) →
          labeling.aFiberReflectionCoordPerm p ∈
            labeling.midpointEquationSet
              (midpointOf d) (midpointOf_ne_zero hd)) :
    MidpointExceptionSetAFixingInvariantBoundary labeling :=
  (MidpointEquationSetAFixingInvariantBoundary.mk
      aFiberReflection_mem_midpointEquationSet)
    |>.toMidpointExceptionSetAFixingInvariantBoundary criterion

/-- Direct constructor from pointwise midpoint-equation-set invariance to the
existing intersection-invariance boundary, assuming the midpoint criterion. -/
def midpointExceptionAFixingSupportIntersectionInvariantBoundary_of_equationSet_invariant
    (labeling : BranchOrbitABCReflectionLabeling h)
    (criterion : MidpointReflectionCriterionBoundary labeling)
    (aFiberReflection_mem_midpointEquationSet :
      ∀ d : ZMod 19, ∀ hd : d ≠ 0,
        ∀ p : labeling.data.toAFiberCoordinates.P,
          p ∈ labeling.midpointEquationSet
            (midpointOf d) (midpointOf_ne_zero hd) →
          labeling.aFiberReflectionCoordPerm p ∈
            labeling.midpointEquationSet
              (midpointOf d) (midpointOf_ne_zero hd)) :
    MidpointExceptionAFixingSupportIntersectionInvariantBoundary labeling :=
  (MidpointEquationSetAFixingInvariantBoundary.mk
      aFiberReflection_mem_midpointEquationSet)
    |>.toMidpointExceptionAFixingSupportIntersectionInvariantBoundary criterion

/-- Direct singleton-fixedness connector from pointwise
midpoint-equation-set invariance, assuming the midpoint criterion. -/
def midpointExceptionAFixingSupportSingletonFixedBoundary_of_equationSet_invariant
    (labeling : BranchOrbitABCReflectionLabeling h)
    (criterion : MidpointReflectionCriterionBoundary labeling)
    (aFiberReflection_mem_midpointEquationSet :
      ∀ d : ZMod 19, ∀ hd : d ≠ 0,
        ∀ p : labeling.data.toAFiberCoordinates.P,
          p ∈ labeling.midpointEquationSet
            (midpointOf d) (midpointOf_ne_zero hd) →
          labeling.aFiberReflectionCoordPerm p ∈
            labeling.midpointEquationSet
              (midpointOf d) (midpointOf_ne_zero hd)) :
    MidpointExceptionAFixingSupportSingletonFixedBoundary labeling :=
  (MidpointEquationSetAFixingInvariantBoundary.mk
      aFiberReflection_mem_midpointEquationSet)
    |>.toMidpointExceptionAFixingSupportSingletonFixedBoundary criterion

/-- Direct no-card-one connector from pointwise midpoint-equation-set
invariance, assuming the midpoint criterion. -/
theorem no_card_one_of_equationSet_invariant
    (labeling : BranchOrbitABCReflectionLabeling h)
    (criterion : MidpointReflectionCriterionBoundary labeling)
    (aFiberReflection_mem_midpointEquationSet :
      ∀ d : ZMod 19, ∀ hd : d ≠ 0,
        ∀ p : labeling.data.toAFiberCoordinates.P,
          p ∈ labeling.midpointEquationSet
            (midpointOf d) (midpointOf_ne_zero hd) →
          labeling.aFiberReflectionCoordPerm p ∈
            labeling.midpointEquationSet
              (midpointOf d) (midpointOf_ne_zero hd)) :
    ∀ d : ZMod 19, ∀ hd : d ≠ 0,
      (labeling.midpointExceptionAFixingSupportIntersection
        (midpointOf d) (midpointOf_ne_zero hd)).card ≠ 1 := by
  intro d hd
  exact
    (MidpointEquationSetAFixingInvariantBoundary.mk
        aFiberReflection_mem_midpointEquationSet).no_card_one criterion d hd

end BranchOrbitABCReflectionLabeling

end

end Moore57
