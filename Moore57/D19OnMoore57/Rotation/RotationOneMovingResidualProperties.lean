import Moore57.D19OnMoore57.AdjacentMoved.AdjacentMovedReflectionFixedPartCriteria

/-!
# Basic properties of the rotation-one moving residual part

This file collects small API lemmas for the canonical decomposition of the
reflection-copy residual into the `rotation 1` fixed part and its moving
complement.
-/

namespace Moore57

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- A point outside the `rotation 1` fixed set is moved by `rotation 1`. -/
theorem rotation_one_moved_of_not_mem_fixedVertexSet
    {h : D19ActsOnMoore57 V Γ} {y : V}
    (hy : y ∉ fixedVertexSet (h.rotation 1)) :
    h.rotation 1 y ≠ y := by
  intro hfixed
  exact hy (mem_fixedVertexSet.mpr hfixed)

/-- The moving residual part is contained in the canonical reflection-copy
residual. -/
theorem rotationOneMovingResidualPart_subset_residual
    (h : D19ActsOnMoore57 V Γ) (input : OrbitBaseSelectionInput h)
    (k : ZMod 19) :
    rotationOneMovingResidualPart h input k ⊆
      reflectionCopyResidual h input.base k := by
  intro y hy
  exact (mem_rotationOneMovingResidualPart_iff.mp hy).1

/-- A residual vertex moved by `rotation 1` lies in the moving residual part. -/
theorem mem_rotationOneMovingResidualPart_of_mem_residual_and_moved
    {h : D19ActsOnMoore57 V Γ} {input : OrbitBaseSelectionInput h}
    {k : ZMod 19} {y : V}
    (hres : y ∈ reflectionCopyResidual h input.base k)
    (hmoved : h.rotation 1 y ≠ y) :
    y ∈ rotationOneMovingResidualPart h input k := by
  exact mem_rotationOneMovingResidualPart_iff.mpr
    ⟨hres, by
      intro hyfixed
      exact hmoved (mem_fixedVertexSet.mp hyfixed)⟩

/-- Membership in the moving residual part is residual membership together
with being moved by `rotation 1`. -/
theorem mem_rotationOneMovingResidualPart_iff_mem_residual_and_moved
    {h : D19ActsOnMoore57 V Γ} {input : OrbitBaseSelectionInput h}
    {k : ZMod 19} {y : V} :
    y ∈ rotationOneMovingResidualPart h input k ↔
      y ∈ reflectionCopyResidual h input.base k ∧ h.rotation 1 y ≠ y := by
  constructor
  · intro hy
    exact ⟨(mem_rotationOneMovingResidualPart_iff.mp hy).1,
      rotation_one_moved_of_not_mem_fixedVertexSet
        (mem_rotationOneMovingResidualPart_iff.mp hy).2⟩
  · rintro ⟨hres, hmoved⟩
    exact mem_rotationOneMovingResidualPart_of_mem_residual_and_moved hres hmoved

/-- A finite set contained in the residual whose vertices are all moved by
`rotation 1` is contained in the moving residual part. -/
theorem subset_rotationOneMovingResidualPart_of_subset_residual_and_moved
    {h : D19ActsOnMoore57 V Γ} {input : OrbitBaseSelectionInput h}
    {k : ZMod 19} (s : Finset V)
    (hsub : s ⊆ reflectionCopyResidual h input.base k)
    (hmoved : ∀ ⦃y⦄, y ∈ s → h.rotation 1 y ≠ y) :
    s ⊆ rotationOneMovingResidualPart h input k := by
  intro y hy
  exact mem_rotationOneMovingResidualPart_of_mem_residual_and_moved
    (hsub hy) (hmoved hy)

/-- Membership in the moving residual part, with the residual condition
expanded into avoidance of the original and reflected orbit-family unions. -/
theorem mem_rotationOneMovingResidualPart_iff_not_orbitFamilyUnion_and_not_reflectionOrbitFamilyUnion_and_not_fixed
    {h : D19ActsOnMoore57 V Γ} {input : OrbitBaseSelectionInput h}
    {k : ZMod 19} {y : V} :
    y ∈ rotationOneMovingResidualPart h input k ↔
      y ∉ input.orbitFamilyUnion ∧
        y ∉ input.reflectionOrbitFamilyUnion k ∧
          y ∉ fixedVertexSet (h.rotation 1) := by
  rw [mem_rotationOneMovingResidualPart_iff,
    input.mem_reflectionCopyResidual_iff_not_orbitFamilyUnion_and_not_reflectionOrbitFamilyUnion]
  constructor
  · rintro ⟨⟨horig, href⟩, hnotfixed⟩
    exact ⟨horig, href, hnotfixed⟩
  · rintro ⟨horig, href, hnotfixed⟩
    exact ⟨⟨horig, href⟩, hnotfixed⟩

/-- Every vertex in the moving residual part is moved by `rotation 1`. -/
theorem rotationOneMovingResidualPart_moved
    (h : D19ActsOnMoore57 V Γ) (input : OrbitBaseSelectionInput h)
    (k : ZMod 19) {y : V}
    (hy : y ∈ rotationOneMovingResidualPart h input k) :
    h.rotation 1 y ≠ y :=
  rotation_one_moved_of_not_mem_fixedVertexSet
    (mem_rotationOneMovingResidualPart_iff.mp hy).2

/-- The moving residual part is disjoint from the canonical fixed residual
part. -/
theorem rotationOneMovingResidualPart_disjoint_fixedPart
    (h : D19ActsOnMoore57 V Γ) (input : OrbitBaseSelectionInput h)
    (k : ZMod 19) :
    Disjoint
      (rotationOneMovingResidualPart h input k)
      (rotationOneFixedResidualPart h input k) :=
  (rotationOneFixedResidualPart_disjoint_movingResidualPart h input k).symm

/-- Filtering the canonical residual splits as the sum of the filtered fixed
and moving residual parts. -/
theorem reflectionCopyResidual_filter_card_eq_fixed_plus_moving
    (h : D19ActsOnMoore57 V Γ) (input : OrbitBaseSelectionInput h)
    (k : ZMod 19) (p : V → Prop) [DecidablePred p] :
    ((reflectionCopyResidual h input.base k).filter p).card =
      ((rotationOneFixedResidualPart h input k).filter p).card +
        ((rotationOneMovingResidualPart h input k).filter p).card := by
  rw [reflectionCopyResidual_eq_rotationOneFixed_union_moving h input k,
    Finset.filter_union]
  have hdisjoint :
      Disjoint
        ((rotationOneFixedResidualPart h input k).filter p)
        ((rotationOneMovingResidualPart h input k).filter p) := by
    rw [Finset.disjoint_left]
    intro y hyFixed hyMoving
    exact Finset.disjoint_left.mp
      (rotationOneFixedResidualPart_disjoint_movingResidualPart h input k)
      (Finset.mem_filter.mp hyFixed).1
      (Finset.mem_filter.mp hyMoving).1
  exact Finset.card_union_of_disjoint
    hdisjoint

end Moore57
