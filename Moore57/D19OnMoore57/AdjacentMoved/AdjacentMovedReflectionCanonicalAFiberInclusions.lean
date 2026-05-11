import Moore57.D19OnMoore57.AdjacentMoved.AdjacentMovedReflectionCanonicalAFiberCriteria
import Moore57.D19OnMoore57.Rotation.RotationOneMovingResidualProperties

/-!
# Inclusion form of the canonical A-fiber criterion

This file replaces the direct equality between the canonical moving residual
part and the selected A-fiber union by the two inclusions that imply it.
-/

namespace Moore57

open Finset

universe u uP

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- Canonical A-fiber criterion stated by mutual containment instead of a
direct equality of finsets. -/
structure AdjacentMovedReflectionCanonicalAFiberInclusionCriteria38Witness
    (h : D19ActsOnMoore57 V Γ) (input : OrbitBaseSelectionInput h) where
  k : ZMod 19
  reflection_not_mem_orbitFamilyUnion :
    ∀ r : Fin 56,
      h.smul (DihedralGroup.sr k) (input.base r) ∉ input.orbitFamilyUnion
  coords : AFiberCoordinates.{u, uP} Γ
  indices : Finset (ZMod 19)
  moving_subset_aFiber :
    rotationOneMovingResidualPart h input k ⊆ coords.fiberUnion indices
  aFiber_subset_moving :
    coords.fiberUnion indices ⊆ rotationOneMovingResidualPart h input k
  residual_contribution :
    ∀ d : ZMod 19, ∀ _hd : d ≠ 0,
      ((rotationOneFixedResidualPart h input k).filter fun y =>
          Γ.Adj y (h.rotation d y)).card +
        ((coords.fiberUnion indices).filter fun y =>
          Γ.Adj y (h.rotation d y)).card =
        38

namespace AdjacentMovedReflectionCanonicalAFiberInclusionCriteria38Witness

variable {h : D19ActsOnMoore57 V Γ}
variable {input : OrbitBaseSelectionInput h}

/-- The two inclusion hypotheses recover the canonical moving/A-fiber
equality expected by the existing criterion. -/
theorem moving_eq_aFiber
    (w : AdjacentMovedReflectionCanonicalAFiberInclusionCriteria38Witness
      h input) :
    rotationOneMovingResidualPart h input w.k =
      w.coords.fiberUnion w.indices :=
  Finset.Subset.antisymm w.moving_subset_aFiber w.aFiber_subset_moving

/-- Membership form of the canonical moving/A-fiber identification. -/
theorem mem_moving_iff_mem_aFiber
    (w : AdjacentMovedReflectionCanonicalAFiberInclusionCriteria38Witness
      h input) (y : V) :
    y ∈ rotationOneMovingResidualPart h input w.k ↔
      y ∈ w.coords.fiberUnion w.indices := by
  constructor
  · intro hy
    exact w.moving_subset_aFiber hy
  · intro hy
    exact w.aFiber_subset_moving hy

/-- Symmetric membership form, useful when the A-fiber side is the starting
point. -/
theorem mem_aFiber_iff_mem_moving
    (w : AdjacentMovedReflectionCanonicalAFiberInclusionCriteria38Witness
      h input) (y : V) :
    y ∈ w.coords.fiberUnion w.indices ↔
      y ∈ rotationOneMovingResidualPart h input w.k :=
  (w.mem_moving_iff_mem_aFiber y).symm

/-- Convert the inclusion-form criterion to the existing equality-form
canonical A-fiber criterion. -/
noncomputable def toCanonicalAFiberCriteria38Witness
    (w : AdjacentMovedReflectionCanonicalAFiberInclusionCriteria38Witness
      h input) :
    AdjacentMovedReflectionCanonicalAFiberCriteria38Witness h input where
  k := w.k
  reflection_not_mem_orbitFamilyUnion :=
    w.reflection_not_mem_orbitFamilyUnion
  coords := w.coords
  indices := w.indices
  moving_eq_aFiber := w.moving_eq_aFiber
  residual_contribution := w.residual_contribution

/-- Convert the inclusion-form criterion directly to the existing fixed/A-fiber
criterion. -/
noncomputable def toFixedAFiberCriteria38Witness
    (w : AdjacentMovedReflectionCanonicalAFiberInclusionCriteria38Witness
      h input) :
    AdjacentMovedReflectionFixedAFiberCriteria38Witness h input :=
  w.toCanonicalAFiberCriteria38Witness.toFixedAFiberCriteria38Witness

/-- Convert the inclusion-form criterion directly to the existing avoidance
split witness. -/
noncomputable def toAvoidanceSplit38Witness
    (w : AdjacentMovedReflectionCanonicalAFiberInclusionCriteria38Witness
      h input) :
    AdjacentMovedReflectionAvoidanceSplit38Witness h input :=
  w.toCanonicalAFiberCriteria38Witness.toAvoidanceSplit38Witness

end AdjacentMovedReflectionCanonicalAFiberInclusionCriteria38Witness

namespace AdjacentMovedReflectionCanonicalAFiberCriteria38Witness

variable {h : D19ActsOnMoore57 V Γ}
variable {input : OrbitBaseSelectionInput h}

/-- Constructor wrapper from the inclusion-form canonical A-fiber criterion. -/
noncomputable def of_inclusionCriteria
    (w : AdjacentMovedReflectionCanonicalAFiberInclusionCriteria38Witness
      h input) :
    AdjacentMovedReflectionCanonicalAFiberCriteria38Witness h input :=
  w.toCanonicalAFiberCriteria38Witness

end AdjacentMovedReflectionCanonicalAFiberCriteria38Witness

namespace AdjacentMovedReflectionFixedAFiberCriteria38Witness

variable {h : D19ActsOnMoore57 V Γ}
variable {input : OrbitBaseSelectionInput h}

/-- Constructor wrapper from the inclusion-form canonical A-fiber criterion. -/
noncomputable def of_canonicalAFiberInclusionCriteria
    (w : AdjacentMovedReflectionCanonicalAFiberInclusionCriteria38Witness
      h input) :
    AdjacentMovedReflectionFixedAFiberCriteria38Witness h input :=
  w.toFixedAFiberCriteria38Witness

end AdjacentMovedReflectionFixedAFiberCriteria38Witness

namespace AdjacentMovedReflectionAvoidanceSplit38Witness

variable {h : D19ActsOnMoore57 V Γ}
variable {input : OrbitBaseSelectionInput h}

/-- Constructor wrapper from the inclusion-form canonical A-fiber criterion to
the existing avoidance split witness. -/
noncomputable def of_canonicalAFiberInclusionCriteria
    (w : AdjacentMovedReflectionCanonicalAFiberInclusionCriteria38Witness
      h input) :
    AdjacentMovedReflectionAvoidanceSplit38Witness h input :=
  w.toAvoidanceSplit38Witness

end AdjacentMovedReflectionAvoidanceSplit38Witness

end Moore57
