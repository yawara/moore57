import Moore57.D19OnMoore57.BranchOrbit.ABCExceptionEquationInvariantBoundary
import Moore57.D19OnMoore57.BranchOrbit.ABCMidpointExceptionSetBoundary

/-!
# Coordinate form of midpoint-equation invariance

This file records the pointwise coordinate statement behind invariance of the
midpoint-equation set under the A-fixing coordinate reflection.  The boundary
is deliberately stated as the raw matching/reflection equality, so the
remaining hard step is visible without going through Finset membership.
-/

namespace Moore57

open Finset

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

namespace BranchOrbitABCReflectionLabeling

variable {h : D19ActsOnMoore57 V Γ}

/-- Boundary input: the raw midpoint matching equation is preserved by the
A-fixing coordinate reflection on the reference A-fiber. -/
structure MidpointEquationAFixingCoordinateBoundary
    (labeling : BranchOrbitABCReflectionLabeling h) : Prop where
  aFiberReflection_preserves_midpointEquation :
    ∀ d : ZMod 19, ∀ hd : d ≠ 0,
      ∀ p : labeling.data.toAFiberCoordinates.P,
        AFiberCoordinates.matchingEquiv h.isMoore
            labeling.data.toAFiberCoordinates 0
            (0 + (midpointOf d + midpointOf d))
            (index_ne_add_of_ne_zero
              (add_self_ne_zero_zmod19 (midpointOf_ne_zero hd))) p =
          labeling.midpointReflectionCoordPerm (midpointOf d) p →
        AFiberCoordinates.matchingEquiv h.isMoore
            labeling.data.toAFiberCoordinates 0
            (0 + (midpointOf d + midpointOf d))
            (index_ne_add_of_ne_zero
              (add_self_ne_zero_zmod19 (midpointOf_ne_zero hd)))
            (labeling.aFiberReflectionCoordPerm p) =
          labeling.midpointReflectionCoordPerm (midpointOf d)
            (labeling.aFiberReflectionCoordPerm p)

namespace MidpointEquationAFixingCoordinateBoundary

variable {labeling : BranchOrbitABCReflectionLabeling h}

/-- The raw coordinate boundary gives the existing midpoint-equation-set
invariance boundary by unfolding membership in `midpointEquationSet`. -/
def toMidpointEquationSetAFixingInvariantBoundary
    (boundary : MidpointEquationAFixingCoordinateBoundary labeling) :
    MidpointEquationSetAFixingInvariantBoundary labeling where
  aFiberReflection_mem_midpointEquationSet d hd p hp := by
    rw [mem_midpointEquationSet] at hp ⊢
    exact boundary.aFiberReflection_preserves_midpointEquation d hd p hp

/-- Direct connector from the raw coordinate boundary to midpoint-exception-set
invariance, assuming the midpoint criterion. -/
def toMidpointExceptionSetAFixingInvariantBoundary
    (boundary : MidpointEquationAFixingCoordinateBoundary labeling)
    (criterion : MidpointReflectionCriterionBoundary labeling) :
    MidpointExceptionSetAFixingInvariantBoundary labeling :=
  boundary.toMidpointEquationSetAFixingInvariantBoundary
    |>.toMidpointExceptionSetAFixingInvariantBoundary criterion

/-- Direct connector from the raw coordinate boundary to invariance of the
midpoint-exception/A-fixing-support intersection. -/
def toMidpointExceptionAFixingSupportIntersectionInvariantBoundary
    (boundary : MidpointEquationAFixingCoordinateBoundary labeling)
    (criterion : MidpointReflectionCriterionBoundary labeling) :
    MidpointExceptionAFixingSupportIntersectionInvariantBoundary labeling :=
  boundary.toMidpointEquationSetAFixingInvariantBoundary
    |>.toMidpointExceptionAFixingSupportIntersectionInvariantBoundary criterion

end MidpointEquationAFixingCoordinateBoundary

/-- Direct constructor from the raw coordinate equation to the existing
midpoint-equation-set invariance boundary. -/
def midpointEquationSetAFixingInvariantBoundary_of_coordinate
    (labeling : BranchOrbitABCReflectionLabeling h)
    (aFiberReflection_preserves_midpointEquation :
      ∀ d : ZMod 19, ∀ hd : d ≠ 0,
        ∀ p : labeling.data.toAFiberCoordinates.P,
          AFiberCoordinates.matchingEquiv h.isMoore
              labeling.data.toAFiberCoordinates 0
              (0 + (midpointOf d + midpointOf d))
              (index_ne_add_of_ne_zero
                (add_self_ne_zero_zmod19 (midpointOf_ne_zero hd))) p =
            labeling.midpointReflectionCoordPerm (midpointOf d) p →
          AFiberCoordinates.matchingEquiv h.isMoore
              labeling.data.toAFiberCoordinates 0
              (0 + (midpointOf d + midpointOf d))
              (index_ne_add_of_ne_zero
                (add_self_ne_zero_zmod19 (midpointOf_ne_zero hd)))
              (labeling.aFiberReflectionCoordPerm p) =
            labeling.midpointReflectionCoordPerm (midpointOf d)
              (labeling.aFiberReflectionCoordPerm p)) :
    MidpointEquationSetAFixingInvariantBoundary labeling :=
  (MidpointEquationAFixingCoordinateBoundary.mk
      aFiberReflection_preserves_midpointEquation)
    |>.toMidpointEquationSetAFixingInvariantBoundary

/-- Applying the midpoint reflection to an A-reflected reference coordinate is
the same as rotating the original coordinate to the endpoint fiber. -/
theorem midpointReflectionCoordPerm_aFiberReflectionCoordPerm_eq_rotationCoordPerm
    (labeling : BranchOrbitABCReflectionLabeling h)
    (m : ZMod 19) (p : labeling.data.toAFiberCoordinates.P) :
    labeling.midpointReflectionCoordPerm m
        (labeling.aFiberReflectionCoordPerm p) =
      labeling.data.toAFiberRotationEquivariance.coordPerm (m + m) 0 p := by
  rw [labeling.midpointReflectionCoordPerm_eq_rotationCoordPerm_aFiberReflectionCoordPerm]
  rw [labeling.aFiberReflectionCoordPerm_involutive]

/-- A still more concrete boundary: under the A-fixing coordinate reflection,
the endpoint matching equation with right side `rotation d (A p)` is sent to
the endpoint matching equation with right side `rotation d p`. -/
structure EndpointMatchingAFixingCoordinateBoundary
    (labeling : BranchOrbitABCReflectionLabeling h) : Prop where
  aFiberReflection_matching_eq_rotation :
    ∀ d : ZMod 19, ∀ hd : d ≠ 0,
      ∀ p : labeling.data.toAFiberCoordinates.P,
        AFiberCoordinates.matchingEquiv h.isMoore
            labeling.data.toAFiberCoordinates 0 (0 + d)
            (index_ne_add_of_ne_zero hd) p =
          labeling.data.toAFiberRotationEquivariance.coordPerm d 0
            (labeling.aFiberReflectionCoordPerm p) →
        AFiberCoordinates.matchingEquiv h.isMoore
            labeling.data.toAFiberCoordinates 0 (0 + d)
            (index_ne_add_of_ne_zero hd)
            (labeling.aFiberReflectionCoordPerm p) =
          labeling.data.toAFiberRotationEquivariance.coordPerm d 0 p

namespace EndpointMatchingAFixingCoordinateBoundary

variable {labeling : BranchOrbitABCReflectionLabeling h}

/-- The endpoint matching/reflection boundary implies the raw midpoint-equation
coordinate boundary.  The only conversion is the established identity
`midpointReflectionCoordPerm = rotationCoordPerm ∘ aFiberReflectionCoordPerm`. -/
def toMidpointEquationAFixingCoordinateBoundary
    (boundary : EndpointMatchingAFixingCoordinateBoundary labeling) :
    MidpointEquationAFixingCoordinateBoundary labeling where
  aFiberReflection_preserves_midpointEquation := by
    intro d hd p hp
    have hdd : midpointOf d + midpointOf d = d := midpointOf_add_self d
    have hp_rotation :
        AFiberCoordinates.matchingEquiv h.isMoore
            labeling.data.toAFiberCoordinates 0 (0 + d)
            (index_ne_add_of_ne_zero hd) p =
          labeling.data.toAFiberRotationEquivariance.coordPerm d 0
            (labeling.aFiberReflectionCoordPerm p) := by
      simpa [hdd] using
        hp.trans
          (labeling.midpointReflectionCoordPerm_eq_rotationCoordPerm_aFiberReflectionCoordPerm
            (midpointOf d) p)
    have hmatching :
        AFiberCoordinates.matchingEquiv h.isMoore
            labeling.data.toAFiberCoordinates 0 (0 + d)
            (index_ne_add_of_ne_zero hd)
            (labeling.aFiberReflectionCoordPerm p) =
          labeling.data.toAFiberRotationEquivariance.coordPerm d 0 p :=
      boundary.aFiberReflection_matching_eq_rotation d hd p hp_rotation
    have hrhs :
        labeling.midpointReflectionCoordPerm (midpointOf d)
            (labeling.aFiberReflectionCoordPerm p) =
          labeling.data.toAFiberRotationEquivariance.coordPerm d 0 p := by
      simpa [hdd] using
        labeling.midpointReflectionCoordPerm_aFiberReflectionCoordPerm_eq_rotationCoordPerm
          (midpointOf d) p
    simpa [hdd, hrhs] using hmatching

/-- The endpoint matching/reflection boundary gives the existing
midpoint-equation-set invariance boundary. -/
def toMidpointEquationSetAFixingInvariantBoundary
    (boundary : EndpointMatchingAFixingCoordinateBoundary labeling) :
    MidpointEquationSetAFixingInvariantBoundary labeling :=
  boundary.toMidpointEquationAFixingCoordinateBoundary
    |>.toMidpointEquationSetAFixingInvariantBoundary

end EndpointMatchingAFixingCoordinateBoundary

end BranchOrbitABCReflectionLabeling

end

end Moore57
