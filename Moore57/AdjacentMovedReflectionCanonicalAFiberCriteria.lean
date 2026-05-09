import Moore57.AdjacentMovedReflectionFixedAFiberCriteria

/-!
# Canonical A-fiber side for the rotation-fixed residual split

This file packages the strongest canonical version of the split criterion:
the fixed side is `rotationOneFixedResidualPart`, and the moving side is
identified with a selected A-fiber union.
-/

namespace Moore57

open Finset

universe u uP

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- Canonical fixed/A-fiber criterion for the reflection residual.

The field `moving_eq_aFiber` is the canonical identification of the moving
residual complement with the chosen A-fiber union.  From this equality we
derive the `ReflectionResidualAFiberSide` residual containment, moved-side
condition, and residual split equation. -/
structure AdjacentMovedReflectionCanonicalAFiberCriteria38Witness
    (h : D19ActsOnMoore57 V Γ) (input : OrbitBaseSelectionInput h) where
  k : ZMod 19
  reflection_not_mem_orbitFamilyUnion :
    ∀ r : Fin 56,
      h.smul (DihedralGroup.sr k) (input.base r) ∉ input.orbitFamilyUnion
  coords : AFiberCoordinates.{u, uP} Γ
  indices : Finset (ZMod 19)
  moving_eq_aFiber :
    rotationOneMovingResidualPart h input k = coords.fiberUnion indices
  residual_contribution :
    ∀ d : ZMod 19, ∀ _hd : d ≠ 0,
      ((rotationOneFixedResidualPart h input k).filter fun y =>
          Γ.Adj y (h.rotation d y)).card +
        ((coords.fiberUnion indices).filter fun y =>
          Γ.Adj y (h.rotation d y)).card =
        38

namespace AdjacentMovedReflectionCanonicalAFiberCriteria38Witness

variable {h : D19ActsOnMoore57 V Γ}
variable {input : OrbitBaseSelectionInput h}

/-- The selected A-fiber union is contained in the reflection-copy residual,
because it is the canonical moving residual part. -/
theorem subset_residual
    (w : AdjacentMovedReflectionCanonicalAFiberCriteria38Witness h input) :
    w.coords.fiberUnion w.indices ≤ reflectionCopyResidual h input.base w.k := by
  intro y hy
  have hyMoving : y ∈ rotationOneMovingResidualPart h input w.k := by
    simpa [w.moving_eq_aFiber] using hy
  exact (mem_rotationOneMovingResidualPart_iff.mp hyMoving).1

/-- The selected A-fiber union lies on the moved side of `rotation 1`, again
because it is the canonical moving residual part. -/
theorem aFiber_moved
    (w : AdjacentMovedReflectionCanonicalAFiberCriteria38Witness h input) :
    ∀ ⦃y : V⦄, y ∈ w.coords.fiberUnion w.indices →
      h.rotation 1 y ≠ y := by
  intro y hy hyFixed
  have hyMoving : y ∈ rotationOneMovingResidualPart h input w.k := by
    simpa [w.moving_eq_aFiber] using hy
  exact (mem_rotationOneMovingResidualPart_iff.mp hyMoving).2
    (mem_fixedVertexSet.mpr hyFixed)

/-- Build the `ReflectionResidualAFiberSide` required by the existing
fixed/A-fiber criterion. -/
noncomputable def toReflectionResidualAFiberSide
    (w : AdjacentMovedReflectionCanonicalAFiberCriteria38Witness h input) :
    ReflectionResidualAFiberSide.{u, uP} h input w.k where
  coords := w.coords
  indices := w.indices
  subset_residual := w.subset_residual
  moved := w.aFiber_moved

/-- The reflection-copy residual is the canonical fixed side together with the
chosen A-fiber union. -/
theorem residual_eq
    (w : AdjacentMovedReflectionCanonicalAFiberCriteria38Witness h input) :
    reflectionCopyResidual h input.base w.k =
      rotationOneFixedResidualPart h input w.k ∪
        w.coords.fiberUnion w.indices := by
  rw [reflectionCopyResidual_eq_rotationOneFixed_union_moving h input w.k,
    w.moving_eq_aFiber]

/-- Convert the canonical A-fiber criterion to the existing fixed/A-fiber
criterion. -/
noncomputable def toFixedAFiberCriteria38Witness
    (w : AdjacentMovedReflectionCanonicalAFiberCriteria38Witness h input) :
    AdjacentMovedReflectionFixedAFiberCriteria38Witness h input where
  k := w.k
  reflection_not_mem_orbitFamilyUnion :=
    w.reflection_not_mem_orbitFamilyUnion
  aSide := w.toReflectionResidualAFiberSide
  residual_eq := w.residual_eq
  residual_contribution := w.residual_contribution

/-- Convert the canonical A-fiber criterion directly to the existing avoidance
split witness. -/
noncomputable def toAvoidanceSplit38Witness
    (w : AdjacentMovedReflectionCanonicalAFiberCriteria38Witness h input) :
    AdjacentMovedReflectionAvoidanceSplit38Witness h input :=
  w.toFixedAFiberCriteria38Witness.toAvoidanceSplit38Witness

end AdjacentMovedReflectionCanonicalAFiberCriteria38Witness

namespace AdjacentMovedReflectionFixedAFiberCriteria38Witness

variable {h : D19ActsOnMoore57 V Γ}
variable {input : OrbitBaseSelectionInput h}

/-- Constructor wrapper from the canonical A-fiber criterion. -/
noncomputable def of_canonicalAFiberCriteria
    (w : AdjacentMovedReflectionCanonicalAFiberCriteria38Witness h input) :
    AdjacentMovedReflectionFixedAFiberCriteria38Witness h input :=
  w.toFixedAFiberCriteria38Witness

end AdjacentMovedReflectionFixedAFiberCriteria38Witness

namespace AdjacentMovedReflectionAvoidanceSplit38Witness

variable {h : D19ActsOnMoore57 V Γ}
variable {input : OrbitBaseSelectionInput h}

/-- Constructor wrapper from the canonical A-fiber criterion to the existing
avoidance split witness. -/
noncomputable def of_canonicalAFiberCriteria
    (w : AdjacentMovedReflectionCanonicalAFiberCriteria38Witness h input) :
    AdjacentMovedReflectionAvoidanceSplit38Witness h input :=
  w.toAvoidanceSplit38Witness

end AdjacentMovedReflectionAvoidanceSplit38Witness

end Moore57
