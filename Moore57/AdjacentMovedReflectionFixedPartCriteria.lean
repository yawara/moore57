import Moore57.AdjacentMovedReflectionAvoidanceSplit
import Moore57.AdjacentMovedReflectionResidualOriginalReflected
import Moore57.FixedUpperBoundCriteria
import Moore57.RotationFixedUpperBoundFromData

/-!
# Rotation-fixed residual side for the reflection avoidance split

This file refines the split avoidance witness by making its `fixedPart`
canonical: it is the part of the reflection-copy residual lying in
`fixedVertexSet (h.rotation 1)`.  The complementary `aPart` is then the rest of
the same residual.
-/

namespace Moore57

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- The canonical rotation-fixed side of the reflection-copy residual. -/
noncomputable def rotationOneFixedResidualPart
    (h : D19ActsOnMoore57 V Γ) (input : OrbitBaseSelectionInput h)
    (k : ZMod 19) : Finset V :=
  (fixedVertexSet (h.rotation 1)).toFinset ∩
    reflectionCopyResidual h input.base k

/-- The complementary non-fixed side of the reflection-copy residual. -/
noncomputable def rotationOneMovingResidualPart
    (h : D19ActsOnMoore57 V Γ) (input : OrbitBaseSelectionInput h)
    (k : ZMod 19) : Finset V :=
  reflectionCopyResidual h input.base k \
    rotationOneFixedResidualPart h input k

theorem mem_rotationOneFixedResidualPart_iff
    {h : D19ActsOnMoore57 V Γ} {input : OrbitBaseSelectionInput h}
    {k : ZMod 19} {y : V} :
    y ∈ rotationOneFixedResidualPart h input k ↔
      y ∈ fixedVertexSet (h.rotation 1) ∧
        y ∈ reflectionCopyResidual h input.base k := by
  classical
  simp [rotationOneFixedResidualPart]

theorem mem_rotationOneFixedResidualPart_iff_fixed_and_not_original_reflected
    {h : D19ActsOnMoore57 V Γ} {input : OrbitBaseSelectionInput h}
    {k : ZMod 19} {y : V} :
    y ∈ rotationOneFixedResidualPart h input k ↔
      y ∈ fixedVertexSet (h.rotation 1) ∧
        y ∉ input.orbitFamilyUnion ∧
          y ∉ input.reflectionOrbitFamilyUnion k := by
  rw [mem_rotationOneFixedResidualPart_iff,
    input.mem_reflectionCopyResidual_iff_not_orbitFamilyUnion_and_not_reflectionOrbitFamilyUnion]

theorem rotationOneFixedResidualPart_subset_residual
    (h : D19ActsOnMoore57 V Γ) (input : OrbitBaseSelectionInput h)
    (k : ZMod 19) :
    rotationOneFixedResidualPart h input k ⊆
      reflectionCopyResidual h input.base k := by
  intro y hy
  exact (mem_rotationOneFixedResidualPart_iff.mp hy).2

theorem mem_rotationOneMovingResidualPart_iff
    {h : D19ActsOnMoore57 V Γ} {input : OrbitBaseSelectionInput h}
    {k : ZMod 19} {y : V} :
    y ∈ rotationOneMovingResidualPart h input k ↔
      y ∈ reflectionCopyResidual h input.base k ∧
        y ∉ fixedVertexSet (h.rotation 1) := by
  classical
  rw [rotationOneMovingResidualPart, Finset.mem_sdiff,
    mem_rotationOneFixedResidualPart_iff]
  tauto

/-- The canonical fixed side and its complement are disjoint. -/
theorem rotationOneFixedResidualPart_disjoint_movingResidualPart
    (h : D19ActsOnMoore57 V Γ) (input : OrbitBaseSelectionInput h)
    (k : ZMod 19) :
    Disjoint
      (rotationOneFixedResidualPart h input k)
      (rotationOneMovingResidualPart h input k) := by
  classical
  rw [rotationOneMovingResidualPart]
  exact Finset.disjoint_sdiff

/-- The canonical fixed side and its complement cover the reflection-copy
residual. -/
theorem reflectionCopyResidual_eq_rotationOneFixed_union_moving
    (h : D19ActsOnMoore57 V Γ) (input : OrbitBaseSelectionInput h)
    (k : ZMod 19) :
    reflectionCopyResidual h input.base k =
      rotationOneFixedResidualPart h input k ∪
        rotationOneMovingResidualPart h input k := by
  classical
  rw [rotationOneMovingResidualPart]
  exact (Finset.union_sdiff_of_subset
    (rotationOneFixedResidualPart_subset_residual h input k)).symm

/-- A rotation-fixed refinement of
`AdjacentMovedReflectionAvoidanceSplit38Witness`.

Compared with the older split witness, the fixed side is no longer arbitrary:
it is definitionally the residual vertices fixed by `h.rotation 1`.  The
included fixed-count upper-bound input records the usual global fixed-point
side datum used elsewhere in the final reduction. -/
structure AdjacentMovedReflectionFixedPartCriteria38Witness
    (h : D19ActsOnMoore57 V Γ) (input : OrbitBaseSelectionInput h) where
  k : ZMod 19
  fixedUpperBound : D19ActsOnMoore57.RotationFixedUpperBoundInput h
  reflection_not_mem_orbitFamilyUnion :
    ∀ r : Fin 56,
      h.smul (DihedralGroup.sr k) (input.base r) ∉ input.orbitFamilyUnion
  residual_contribution :
    ∀ d : ZMod 19, ∀ _hd : d ≠ 0,
      ((rotationOneFixedResidualPart h input k).filter fun y =>
          Γ.Adj y (h.rotation d y)).card +
        ((rotationOneMovingResidualPart h input k).filter fun y =>
          Γ.Adj y (h.rotation d y)).card =
        38

namespace AdjacentMovedReflectionFixedPartCriteria38Witness

variable {h : D19ActsOnMoore57 V Γ}
variable {input : OrbitBaseSelectionInput h}

/-- The fixed side is bounded by the rotation fixed-point input. -/
theorem fixedPart_card_le_one
    (w : AdjacentMovedReflectionFixedPartCriteria38Witness h input) :
    (rotationOneFixedResidualPart h input w.k).card ≤ 1 := by
  classical
  have hsub :
      rotationOneFixedResidualPart h input w.k ⊆
        (fixedVertexSet (h.rotation 1)).toFinset := by
    intro y hy
    simpa using (mem_rotationOneFixedResidualPart_iff.mp hy).1
  have hcard :
      (fixedVertexSet (h.rotation 1)).toFinset.card = 1 := by
    rw [Set.toFinset_card]
    rw [← fixedVertexCount_eq_card_fixedVertexSet]
    exact w.fixedUpperBound.rotation_one_fixed_count_eq_one
  exact (Finset.card_le_card hsub).trans_eq hcard

/-- Forget the canonical fixed-side presentation to the existing split
avoidance witness. -/
noncomputable def toAvoidanceSplit38Witness
    (w : AdjacentMovedReflectionFixedPartCriteria38Witness h input) :
    AdjacentMovedReflectionAvoidanceSplit38Witness h input where
  k := w.k
  reflection_not_mem_orbitFamilyUnion :=
    w.reflection_not_mem_orbitFamilyUnion
  fixedPart := rotationOneFixedResidualPart h input w.k
  aPart := rotationOneMovingResidualPart h input w.k
  parts_disjoint :=
    rotationOneFixedResidualPart_disjoint_movingResidualPart h input w.k
  residual_eq :=
    reflectionCopyResidual_eq_rotationOneFixed_union_moving h input w.k
  residual_contribution := w.residual_contribution

end AdjacentMovedReflectionFixedPartCriteria38Witness

namespace AdjacentMovedReflectionAvoidanceSplit38Witness

variable {h : D19ActsOnMoore57 V Γ}
variable {input : OrbitBaseSelectionInput h}

/-- Constructor wrapper from the rotation-fixed residual-side criterion. -/
noncomputable def of_rotationFixedPartCriteria
    (w : AdjacentMovedReflectionFixedPartCriteria38Witness h input) :
    AdjacentMovedReflectionAvoidanceSplit38Witness h input :=
  w.toAvoidanceSplit38Witness

end AdjacentMovedReflectionAvoidanceSplit38Witness

end Moore57
