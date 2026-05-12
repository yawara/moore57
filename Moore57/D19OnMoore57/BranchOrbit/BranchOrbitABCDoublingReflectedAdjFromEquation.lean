import Moore57.D19OnMoore57.BranchOrbit.BranchOrbitABCDoublingRemainingBoundary
import Moore57.D19OnMoore57.BranchOrbit.BranchOrbitABCExceptionAllSupportBoundary

/-!
# Reflected-middle adjacency from a matching equation

This file converts the last reflected-reference adjacency in the doubling
common-neighbor boundary into a coordinate matching equation.  The equation
says exactly that the original middle mate is also the matching mate of the
midpoint-reflected reference endpoint.
-/

namespace Moore57

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

namespace BranchOrbitABCReflectionLabeling

variable {h : D19ActsOnMoore57 V Γ}

/-- The reflected endpoint index `0 + (m + m)` is distinct from the middle
index `0 + m` when `m` is nonzero. -/
theorem midpoint_reflectedReference_index_ne_middle
    {m : ZMod 19} (hm : m ≠ 0) :
    (0 + (m + m) : ZMod 19) ≠ 0 + m := by
  simpa [add_assoc] using
    (index_ne_add_of_ne_zero (i := 0 + m) (d := m) hm).symm

/-- If the original middle mate is also the matching mate of the reflected
reference endpoint, then the missing reflected-reference adjacency follows
formally from the A-fiber matching adjacency criterion. -/
theorem midpoint_middle_adj_reflected_reference_of_reflected_middle_matching
    (labeling : BranchOrbitABCReflectionLabeling h)
    (m : ZMod 19) (hm : m ≠ 0)
    (p : labeling.data.toAFiberCoordinates.P)
    (hmatch :
      AFiberCoordinates.matchingEquiv h.isMoore
          labeling.data.toAFiberCoordinates (0 + (m + m)) (0 + m)
          (midpoint_reflectedReference_index_ne_middle hm)
          (labeling.midpointReflectionCoordPerm m p) =
        labeling.midpointExceptionMiddleMate m hm p) :
    Γ.Adj
      (labeling.midpointExceptionReflectedReferenceVertex m p)
      (labeling.midpointExceptionMiddleMateVertex m hm p) := by
  exact
    (AFiberCoordinates.adj_iff_matchingEquiv_eq h.isMoore
      labeling.data.toAFiberCoordinates
      (midpoint_reflectedReference_index_ne_middle hm)
      (labeling.midpointReflectionCoordPerm m p)
      (labeling.midpointExceptionMiddleMate m hm p)).2
      (by
        simpa [midpointExceptionReflectedReferenceVertex,
          midpointExceptionMiddleMateVertex] using hmatch)

/-- Matching-equation form of the remaining reflected-reference adjacency. -/
structure MidpointExceptionDoublingMiddleReflectedMatchingBoundary
    (labeling : BranchOrbitABCReflectionLabeling h) : Prop where
  midpoint_reflected_middle_matching :
    ∀ m : ZMod 19, ∀ hm : m ≠ 0,
      ∀ p : labeling.data.toAFiberCoordinates.P,
        p ∈ labeling.aFiberReflectionSupport →
          AFiberCoordinates.matchingEquiv h.isMoore
              labeling.data.toAFiberCoordinates (0 + (m + m)) (0 + m)
              (midpoint_reflectedReference_index_ne_middle hm)
              (labeling.midpointReflectionCoordPerm m p) =
            labeling.midpointExceptionMiddleMate m hm p

namespace MidpointExceptionDoublingMiddleReflectedMatchingBoundary

variable {labeling : BranchOrbitABCReflectionLabeling h}

/-- Convert the reflected-to-middle matching equation into the remaining
reflected-reference adjacency boundary. -/
def toMidpointExceptionDoublingMiddleReflectedAdjBoundary
    (boundary :
      MidpointExceptionDoublingMiddleReflectedMatchingBoundary labeling) :
    MidpointExceptionDoublingMiddleReflectedAdjBoundary labeling where
  midpoint_middle_adj_reflected_reference := by
    intro m hm p hpSupport
    exact
      labeling.midpoint_middle_adj_reflected_reference_of_reflected_middle_matching
        m hm p
        (boundary.midpoint_reflected_middle_matching m hm p hpSupport)

end MidpointExceptionDoublingMiddleReflectedMatchingBoundary

/-- Equation-set form of the remaining reflected-reference adjacency: once a
support point satisfies the midpoint equation, it is enough to identify the
middle mate as the reflected endpoint's matching mate. -/
structure MidpointExceptionDoublingMiddleReflectedAdjFromEquationBoundary
    (labeling : BranchOrbitABCReflectionLabeling h) : Prop where
  midpoint_reflected_middle_matching_of_midpointEquation :
    ∀ m : ZMod 19, ∀ hm : m ≠ 0,
      ∀ p : labeling.data.toAFiberCoordinates.P,
        p ∈ labeling.aFiberReflectionSupport →
          p ∈ labeling.midpointEquationSet m hm →
            AFiberCoordinates.matchingEquiv h.isMoore
                labeling.data.toAFiberCoordinates (0 + (m + m)) (0 + m)
                (midpoint_reflectedReference_index_ne_middle hm)
                (labeling.midpointReflectionCoordPerm m p) =
              labeling.midpointExceptionMiddleMate m hm p

namespace MidpointExceptionDoublingMiddleReflectedAdjFromEquationBoundary

variable {labeling : BranchOrbitABCReflectionLabeling h}

/-- Supply the pointwise midpoint-equation fact separately, producing the
matching-equation boundary for the reflected-reference adjacency. -/
def toMidpointExceptionDoublingMiddleReflectedMatchingBoundary
    (boundary :
      MidpointExceptionDoublingMiddleReflectedAdjFromEquationBoundary labeling)
    (midpointEquation :
      ∀ m : ZMod 19, ∀ hm : m ≠ 0,
        ∀ p : labeling.data.toAFiberCoordinates.P,
          p ∈ labeling.aFiberReflectionSupport →
            p ∈ labeling.midpointEquationSet m hm) :
    MidpointExceptionDoublingMiddleReflectedMatchingBoundary labeling where
  midpoint_reflected_middle_matching := by
    intro m hm p hpSupport
    exact
      boundary.midpoint_reflected_middle_matching_of_midpointEquation
        m hm p hpSupport (midpointEquation m hm p hpSupport)

/-- Direct conversion to the remaining reflected-reference adjacency boundary
when midpoint-equation membership is already available pointwise. -/
def toMidpointExceptionDoublingMiddleReflectedAdjBoundary
    (boundary :
      MidpointExceptionDoublingMiddleReflectedAdjFromEquationBoundary labeling)
    (midpointEquation :
      ∀ m : ZMod 19, ∀ hm : m ≠ 0,
        ∀ p : labeling.data.toAFiberCoordinates.P,
          p ∈ labeling.aFiberReflectionSupport →
            p ∈ labeling.midpointEquationSet m hm) :
    MidpointExceptionDoublingMiddleReflectedAdjBoundary labeling :=
  (boundary.toMidpointExceptionDoublingMiddleReflectedMatchingBoundary
      midpointEquation)
    |>.toMidpointExceptionDoublingMiddleReflectedAdjBoundary

/-- If the midpoint criterion has converted exception-set membership into the
midpoint equation for every support point, then the equation-set boundary
supplies the remaining reflected-reference adjacency. -/
def toMidpointExceptionDoublingMiddleReflectedAdjBoundary_of_midpointCriterion
    (boundary :
      MidpointExceptionDoublingMiddleReflectedAdjFromEquationBoundary labeling)
    (criterion : MidpointReflectionCriterionBoundary labeling)
    (support_subset_exception :
      ∀ m : ZMod 19, ∀ hm : m ≠ 0,
        labeling.aFiberReflectionSupport ⊆
          labeling.midpointExceptionSet m hm) :
    MidpointExceptionDoublingMiddleReflectedAdjBoundary labeling :=
  boundary.toMidpointExceptionDoublingMiddleReflectedAdjBoundary
    (by
      intro m hm p hpSupport
      exact
        labeling.mem_midpointEquationSet_of_mem_aFiberReflectionSupport_of_subset_midpointExceptionSet
          criterion (support_subset_exception m hm) hpSupport)

end MidpointExceptionDoublingMiddleReflectedAdjFromEquationBoundary

end BranchOrbitABCReflectionLabeling

end

end Moore57
