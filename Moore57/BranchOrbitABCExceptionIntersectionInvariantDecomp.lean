import Moore57.BranchOrbitABCExceptionSingletonInvariantBoundary

/-!
# Decomposing midpoint-exception/support intersection invariance

This file separates invariance of
`midpointExceptionAFixingSupportIntersection` under the A-fixing coordinate
reflection into two formal pieces:

* the A-fixing coordinate reflection preserves its own moving support;
* it remains to prove invariance of the midpoint-exception set.
-/

namespace Moore57

open Finset

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

local instance instExceptionIntersectionInvariantDecompPFintype
    {h : D19ActsOnMoore57 V Γ}
    (labeling : BranchOrbitABCReflectionLabeling h) :
    Fintype labeling.data.toAFiberCoordinates.P :=
  labeling.data.toAFiberCoordinates.P_fintype

local instance instExceptionIntersectionInvariantDecompDecidableEq
    (α : Type*) : DecidableEq α :=
  Classical.decEq α

namespace BranchOrbitABCReflectionLabeling

variable {h : D19ActsOnMoore57 V Γ}

/-- The A-fixing coordinate reflection is an involution on reference
A-fiber coordinates. -/
theorem aFiberReflectionCoordPerm_involutive
    (labeling : BranchOrbitABCReflectionLabeling h)
    (p : labeling.data.toAFiberCoordinates.P) :
    labeling.aFiberReflectionCoordPerm
        (labeling.aFiberReflectionCoordPerm p) = p := by
  rw [labeling.aFiberReflectionCoordPerm_eq_iff]
  rw [labeling.coord_aFiberReflectionCoordPerm_apply_val]
  exact h.reflection_smul_reflection_smul labeling.aFixingReflectionIndex
    (((labeling.data.toAFiberCoordinates.coord 0 p :
      {x : V // x ∈
        branchFiber Γ labeling.data.toAFiberCoordinates.u
          (labeling.data.toAFiberCoordinates.a 0)}) : V))

/-- The A-fixing coordinate reflection preserves its moving support. -/
theorem aFiberReflectionCoordPerm_mem_support_iff
    (labeling : BranchOrbitABCReflectionLabeling h)
    (p : labeling.data.toAFiberCoordinates.P) :
    labeling.aFiberReflectionCoordPerm p ∈ labeling.aFiberReflectionSupport ↔
      p ∈ labeling.aFiberReflectionSupport := by
  classical
  rw [labeling.mem_aFiberReflectionSupport,
    labeling.mem_aFiberReflectionSupport]
  rw [labeling.aFiberReflectionCoordPerm_involutive]
  exact ne_comm

/-- Forward form of support invariance under the A-fixing coordinate
reflection. -/
theorem aFiberReflectionCoordPerm_mem_support_of_mem
    (labeling : BranchOrbitABCReflectionLabeling h)
    {p : labeling.data.toAFiberCoordinates.P}
    (hp : p ∈ labeling.aFiberReflectionSupport) :
    labeling.aFiberReflectionCoordPerm p ∈ labeling.aFiberReflectionSupport :=
  (labeling.aFiberReflectionCoordPerm_mem_support_iff p).2 hp

/-- Boundary input: each midpoint-exception set is closed under the A-fixing
coordinate reflection. -/
structure MidpointExceptionSetAFixingInvariantBoundary
    (labeling : BranchOrbitABCReflectionLabeling h) : Prop where
  aFiberReflection_mem_midpointExceptionSet :
    ∀ d : ZMod 19, ∀ hd : d ≠ 0,
      ∀ p : labeling.data.toAFiberCoordinates.P,
        p ∈ labeling.midpointExceptionSet
          (midpointOf d) (midpointOf_ne_zero hd) →
        labeling.aFiberReflectionCoordPerm p ∈
          labeling.midpointExceptionSet
            (midpointOf d) (midpointOf_ne_zero hd)

namespace MidpointExceptionSetAFixingInvariantBoundary

variable {labeling : BranchOrbitABCReflectionLabeling h}

/-- Midpoint-exception-set invariance implies invariance of the intersection
with the A-fixing reflection support, because that support is itself
reflection-invariant. -/
def toMidpointExceptionAFixingSupportIntersectionInvariantBoundary
    (boundary : MidpointExceptionSetAFixingInvariantBoundary labeling) :
    MidpointExceptionAFixingSupportIntersectionInvariantBoundary labeling where
  aFiberReflection_mem_intersection d hd p hp := by
    rcases
      (labeling.mem_midpointExceptionAFixingSupportIntersection
        (midpointOf d) (midpointOf_ne_zero hd) p).1 hp with
      ⟨hpException, hpSupport⟩
    exact
      (labeling.mem_midpointExceptionAFixingSupportIntersection
        (midpointOf d) (midpointOf_ne_zero hd)
          (labeling.aFiberReflectionCoordPerm p)).2
        ⟨boundary.aFiberReflection_mem_midpointExceptionSet d hd p
            hpException,
          labeling.aFiberReflectionCoordPerm_mem_support_of_mem hpSupport⟩

/-- Direct connector to the existing singleton-fixedness boundary. -/
def toMidpointExceptionAFixingSupportSingletonFixedBoundary
    (boundary : MidpointExceptionSetAFixingInvariantBoundary labeling) :
    MidpointExceptionAFixingSupportSingletonFixedBoundary labeling :=
  boundary.toMidpointExceptionAFixingSupportIntersectionInvariantBoundary
    |>.toMidpointExceptionAFixingSupportSingletonFixedBoundary

/-- Direct connector to the existing no-card-one boundary. -/
def toMidpointExceptionAFixingSupportNoCardOneBoundary
    (boundary : MidpointExceptionSetAFixingInvariantBoundary labeling) :
    MidpointExceptionAFixingSupportNoCardOneBoundary labeling :=
  boundary.toMidpointExceptionAFixingSupportIntersectionInvariantBoundary
    |>.toMidpointExceptionAFixingSupportNoCardOneBoundary

/-- The midpoint-exception-set invariance boundary supplies the existing
no-card-one theorem for the intersection. -/
theorem no_card_one
    (boundary : MidpointExceptionSetAFixingInvariantBoundary labeling)
    (d : ZMod 19) (hd : d ≠ 0) :
    (labeling.midpointExceptionAFixingSupportIntersection
      (midpointOf d) (midpointOf_ne_zero hd)).card ≠ 1 :=
  boundary.toMidpointExceptionAFixingSupportNoCardOneBoundary.no_card_one d hd

end MidpointExceptionSetAFixingInvariantBoundary

/-- Direct constructor from pointwise midpoint-exception-set invariance to the
existing intersection-invariance boundary. -/
def midpointExceptionAFixingSupportIntersectionInvariantBoundary_of_exceptionSet_invariant
    (labeling : BranchOrbitABCReflectionLabeling h)
    (aFiberReflection_mem_midpointExceptionSet :
      ∀ d : ZMod 19, ∀ hd : d ≠ 0,
        ∀ p : labeling.data.toAFiberCoordinates.P,
          p ∈ labeling.midpointExceptionSet
            (midpointOf d) (midpointOf_ne_zero hd) →
          labeling.aFiberReflectionCoordPerm p ∈
            labeling.midpointExceptionSet
              (midpointOf d) (midpointOf_ne_zero hd)) :
    MidpointExceptionAFixingSupportIntersectionInvariantBoundary labeling :=
  (MidpointExceptionSetAFixingInvariantBoundary.mk
      aFiberReflection_mem_midpointExceptionSet)
    |>.toMidpointExceptionAFixingSupportIntersectionInvariantBoundary

/-- Direct singleton-fixedness connector from pointwise
midpoint-exception-set invariance. -/
def midpointExceptionAFixingSupportSingletonFixedBoundary_of_exceptionSet_invariant
    (labeling : BranchOrbitABCReflectionLabeling h)
    (aFiberReflection_mem_midpointExceptionSet :
      ∀ d : ZMod 19, ∀ hd : d ≠ 0,
        ∀ p : labeling.data.toAFiberCoordinates.P,
          p ∈ labeling.midpointExceptionSet
            (midpointOf d) (midpointOf_ne_zero hd) →
          labeling.aFiberReflectionCoordPerm p ∈
            labeling.midpointExceptionSet
              (midpointOf d) (midpointOf_ne_zero hd)) :
    MidpointExceptionAFixingSupportSingletonFixedBoundary labeling :=
  (MidpointExceptionSetAFixingInvariantBoundary.mk
      aFiberReflection_mem_midpointExceptionSet)
    |>.toMidpointExceptionAFixingSupportSingletonFixedBoundary

/-- Direct no-card-one connector from pointwise midpoint-exception-set
invariance. -/
theorem no_card_one_of_exceptionSet_invariant
    (labeling : BranchOrbitABCReflectionLabeling h)
    (aFiberReflection_mem_midpointExceptionSet :
      ∀ d : ZMod 19, ∀ hd : d ≠ 0,
        ∀ p : labeling.data.toAFiberCoordinates.P,
          p ∈ labeling.midpointExceptionSet
            (midpointOf d) (midpointOf_ne_zero hd) →
          labeling.aFiberReflectionCoordPerm p ∈
            labeling.midpointExceptionSet
              (midpointOf d) (midpointOf_ne_zero hd)) :
    ∀ d : ZMod 19, ∀ hd : d ≠ 0,
      (labeling.midpointExceptionAFixingSupportIntersection
        (midpointOf d) (midpointOf_ne_zero hd)).card ≠ 1 := by
  intro d hd
  exact
    (MidpointExceptionSetAFixingInvariantBoundary.mk
        aFiberReflection_mem_midpointExceptionSet).no_card_one d hd

end BranchOrbitABCReflectionLabeling

end

end Moore57
