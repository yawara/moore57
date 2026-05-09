import Moore57.AFiberOrbitMovingResidual

/-!
# A-fiber residual split bridges

This file derives the canonical moving/A-fiber inclusions from a split equality
of the reflection-copy residual into the canonical fixed part and an A-fiber
side.
-/

namespace Moore57

open Finset

universe u uP

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- If the reflection-copy residual splits as the canonical fixed residual and
`aPart`, then the canonical moving residual is contained in `aPart`. -/
theorem rotationOneMovingResidualPart_subset_of_residual_eq_fixed_union
    {h : D19ActsOnMoore57 V Γ}
    {input : OrbitBaseSelectionInput h} {k : ZMod 19}
    {aPart : Finset V}
    (hres :
      reflectionCopyResidual h input.base k =
        rotationOneFixedResidualPart h input k ∪ aPart) :
    rotationOneMovingResidualPart h input k ⊆ aPart := by
  intro y hyMoving
  have hyResidual : y ∈ reflectionCopyResidual h input.base k :=
    (mem_rotationOneMovingResidualPart_iff.mp hyMoving).1
  have hyUnion :
      y ∈ rotationOneFixedResidualPart h input k ∪ aPart := by
    simpa [hres] using hyResidual
  rcases Finset.mem_union.mp hyUnion with hyFixed | hyA
  · exact False.elim
      ((mem_rotationOneMovingResidualPart_iff.mp hyMoving).2
        (mem_rotationOneFixedResidualPart_iff.mp hyFixed).1)
  · exact hyA

/-- The A-fiber side of a fixed/A-fiber residual split is contained in the
reflection-copy residual. -/
theorem aFiber_subset_residual_of_residual_eq_fixed_union
    {h : D19ActsOnMoore57 V Γ}
    {input : OrbitBaseSelectionInput h} {k : ZMod 19}
    {coords : AFiberCoordinates.{u, uP} Γ}
    {indices : Finset (ZMod 19)}
    (hres :
      reflectionCopyResidual h input.base k =
        rotationOneFixedResidualPart h input k ∪ coords.fiberUnion indices) :
    coords.fiberUnion indices ⊆ reflectionCopyResidual h input.base k := by
  intro y hy
  have hyUnion :
      y ∈ rotationOneFixedResidualPart h input k ∪
        coords.fiberUnion indices :=
    Finset.mem_union.mpr (Or.inr hy)
  simpa [hres] using hyUnion

/-- A residual split equality plus rotation equivariance recovers the
canonical moving/A-fiber equality. -/
theorem moving_eq_aFiber_of_residual_eq_fixed_union_and_equivariant
    {h : D19ActsOnMoore57 V Γ}
    {input : OrbitBaseSelectionInput h} {k : ZMod 19}
    {coords : AFiberCoordinates.{u, uP} Γ}
    {indices : Finset (ZMod 19)}
    (hres :
      reflectionCopyResidual h input.base k =
        rotationOneFixedResidualPart h input k ∪ coords.fiberUnion indices)
    (rot : AFiberRotationEquivariance h coords) :
    rotationOneMovingResidualPart h input k = coords.fiberUnion indices :=
  Finset.Subset.antisymm
    (rotationOneMovingResidualPart_subset_of_residual_eq_fixed_union hres)
    (rot.fiberUnion_subset_movingResidual_of_subset_residual input k indices
      (aFiber_subset_residual_of_residual_eq_fixed_union hres))

end Moore57
