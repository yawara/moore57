import Moore57.D19OnMoore57.AdjacentMoved.ReflectionFixedPartCriteria
import Moore57.D19OnMoore57.AdjacentMoved.ReflectionAFiberCriteria

/-!
# Canonical fixed side with an A-fiber residual side

This file combines the two refinements of
`AdjacentMovedReflectionAvoidanceSplit38Witness`: the fixed side is the
canonical `rotationOneFixedResidualPart`, and the A-side is supplied by a
`ReflectionResidualAFiberSide`.
-/

namespace Moore57

open Finset

universe u uP

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- Avoidance split data with the canonical rotation-fixed residual side and
an A-fiber moved side. -/
structure AdjacentMovedReflectionFixedAFiberCriteria38Witness
    (h : D19ActsOnMoore57 V Γ) (input : OrbitBaseSelectionInput h) where
  k : ZMod 19
  reflection_not_mem_orbitFamilyUnion :
    ∀ r : Fin 56,
      h.smul (DihedralGroup.sr k) (input.base r) ∉ input.orbitFamilyUnion
  aSide : ReflectionResidualAFiberSide.{u, uP} h input k
  residual_eq :
    reflectionCopyResidual h input.base k =
      rotationOneFixedResidualPart h input k ∪ aSide.aPart
  residual_contribution :
    ∀ d : ZMod 19, ∀ _hd : d ≠ 0,
      ((rotationOneFixedResidualPart h input k).filter fun y =>
          Γ.Adj y (h.rotation d y)).card +
        ((aSide.aPart).filter fun y =>
          Γ.Adj y (h.rotation d y)).card =
        38

namespace AdjacentMovedReflectionFixedAFiberCriteria38Witness

variable {h : D19ActsOnMoore57 V Γ}
variable {input : OrbitBaseSelectionInput h}

/-- The canonical fixed side consists of vertices fixed by `h.rotation 1`. -/
theorem fixedPart_fixed
    (w : AdjacentMovedReflectionFixedAFiberCriteria38Witness h input)
    {y : V} (hy : y ∈ rotationOneFixedResidualPart h input w.k) :
    h.rotation 1 y = y := by
  exact mem_fixedVertexSet.mp (mem_rotationOneFixedResidualPart_iff.mp hy).1

/-- The canonical fixed side is disjoint from the A-fiber moved side. -/
theorem parts_disjoint
    (w : AdjacentMovedReflectionFixedAFiberCriteria38Witness h input) :
    Disjoint (rotationOneFixedResidualPart h input w.k) w.aSide.aPart :=
  h.disjoint_of_rotation_one_fixed_moved
    (by
      intro y hy
      exact w.fixedPart_fixed hy)
    w.aSide.moved

/-- The recorded A-fiber side is exactly the canonical moving complement of
the fixed residual side. -/
theorem aPart_eq_rotationOneMovingResidualPart
    (w : AdjacentMovedReflectionFixedAFiberCriteria38Witness h input) :
    w.aSide.aPart = rotationOneMovingResidualPart h input w.k := by
  classical
  ext y
  constructor
  · intro hy
    rw [mem_rotationOneMovingResidualPart_iff]
    refine ⟨w.aSide.aPart_subset_residual hy, ?_⟩
    intro hfixed
    exact w.aSide.moved hy (mem_fixedVertexSet.mp hfixed)
  · intro hy
    have hmem := mem_rotationOneMovingResidualPart_iff.mp hy
    have hyUnion :
        y ∈ rotationOneFixedResidualPart h input w.k ∪ w.aSide.aPart := by
      rw [← w.residual_eq]
      exact hmem.1
    rcases Finset.mem_union.mp hyUnion with hyFixed | hyA
    · exact False.elim (hmem.2 (mem_rotationOneFixedResidualPart_iff.mp hyFixed).1)
    · exact hyA

/-- Convert the combined fixed/A-fiber criterion to the existing avoidance
split witness. -/
noncomputable def toAvoidanceSplit38Witness
    (w : AdjacentMovedReflectionFixedAFiberCriteria38Witness h input) :
    AdjacentMovedReflectionAvoidanceSplit38Witness h input where
  k := w.k
  reflection_not_mem_orbitFamilyUnion :=
    w.reflection_not_mem_orbitFamilyUnion
  fixedPart := rotationOneFixedResidualPart h input w.k
  aPart := w.aSide.aPart
  parts_disjoint := w.parts_disjoint
  residual_eq := w.residual_eq
  residual_contribution := w.residual_contribution

end AdjacentMovedReflectionFixedAFiberCriteria38Witness

namespace AdjacentMovedReflectionAvoidanceSplit38Witness

variable {h : D19ActsOnMoore57 V Γ}
variable {input : OrbitBaseSelectionInput h}

/-- Constructor wrapper from the combined canonical fixed/A-fiber criterion. -/
noncomputable def of_fixedAFiberCriteria
    (w : AdjacentMovedReflectionFixedAFiberCriteria38Witness h input) :
    AdjacentMovedReflectionAvoidanceSplit38Witness h input :=
  w.toAvoidanceSplit38Witness

end AdjacentMovedReflectionAvoidanceSplit38Witness

end Moore57
