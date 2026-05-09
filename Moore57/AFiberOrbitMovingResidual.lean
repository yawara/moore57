import Moore57.AFiberOrbitMoved
import Moore57.RotationOneMovingResidualProperties

/-!
# Rotation-orbit A-fibers inside the moving residual

This file bridges the geometric movedness of rotation-equivariant A-fibers to
the canonical `rotation 1` moving part of a reflection-copy residual.  Once a
selected A-fiber union is known to lie in the residual, equivariance supplies
the non-fixed condition needed for membership in the moving residual.
-/

namespace Moore57

universe u uP

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

namespace AFiberRotationEquivariance

variable {h : D19ActsOnMoore57 V Γ}
variable {coords : AFiberCoordinates.{u, uP} Γ}

/-- Every vertex in a selected union of equivariant A-fibers is moved by
`rotation 1`. -/
theorem fiberUnion_moved_by_rotation_one
    (rot : AFiberRotationEquivariance h coords) {indices : Finset (ZMod 19)}
    {y : V} (hy : y ∈ coords.fiberUnion indices) :
    h.rotation 1 y ≠ y := by
  classical
  rcases (coords.mem_fiberUnion_iff indices y).mp hy with ⟨i, _hi, hyi⟩
  exact rot.moved_by_nonzero_rotation_of_mem_fiber
    (d := 1) (i := i) (by decide) hyi

/-- For an equivariant A-fiber union, containment in the residual is the only
remaining condition for containment in the `rotation 1` moving residual. -/
theorem fiberUnion_subset_movingResidual_of_subset_residual
    (rot : AFiberRotationEquivariance h coords)
    (input : OrbitBaseSelectionInput h) (k : ZMod 19)
    (indices : Finset (ZMod 19))
    (hres : coords.fiberUnion indices ⊆ reflectionCopyResidual h input.base k) :
    coords.fiberUnion indices ⊆ rotationOneMovingResidualPart h input k := by
  intro y hy
  rw [mem_rotationOneMovingResidualPart_iff]
  refine ⟨hres hy, ?_⟩
  intro hyFixed
  exact (rot.fiberUnion_moved_by_rotation_one hy)
    (mem_fixedVertexSet.mp hyFixed)

end AFiberRotationEquivariance

namespace AFiberCoordinates

/-- Rotation-orbit A-fiber unions are moved by `rotation 1`. -/
theorem ofRotationOrbit_fiberUnion_moved_by_rotation_one
    (h : D19ActsOnMoore57 V Γ) (u a0 : V)
    (hu : ∀ d : ZMod 19, h.rotation d u = u)
    (hub0 : Γ.Adj u a0)
    (hinj : Function.Injective fun i : ZMod 19 => h.rotation i a0)
    {indices : Finset (ZMod 19)} {y : V}
    (hy : y ∈ (ofRotationOrbit h u a0 hu hub0 hinj).fiberUnion indices) :
    h.rotation 1 y ≠ y :=
  AFiberRotationEquivariance.fiberUnion_moved_by_rotation_one
    (ofRotationOrbit_rotationEquivariance h u a0 hu hub0 hinj) hy

/-- Rotation-orbit A-fiber unions built from a moved branch are moved by
`rotation 1`. -/
theorem ofRotationOrbitOfMoved_fiberUnion_moved_by_rotation_one
    (h : D19ActsOnMoore57 V Γ) (u a0 : V)
    (hu : ∀ d : ZMod 19, h.rotation d u = u)
    (hub0 : Γ.Adj u a0)
    {d0 : ZMod 19} (hd0 : d0 ≠ 0) (hmove : h.rotation d0 a0 ≠ a0)
    {indices : Finset (ZMod 19)} {y : V}
    (hy : y ∈
      (ofRotationOrbitOfMoved h u a0 hu hub0 hd0 hmove).fiberUnion indices) :
    h.rotation 1 y ≠ y :=
  AFiberRotationEquivariance.fiberUnion_moved_by_rotation_one
    (ofRotationOrbitOfMoved_rotationEquivariance h u a0 hu hub0 hd0 hmove) hy

/-- For rotation-orbit A-fiber unions, residual containment implies moving
residual containment. -/
theorem ofRotationOrbit_fiberUnion_subset_movingResidual_of_subset_residual
    (h : D19ActsOnMoore57 V Γ) (u a0 : V)
    (hu : ∀ d : ZMod 19, h.rotation d u = u)
    (hub0 : Γ.Adj u a0)
    (hinj : Function.Injective fun i : ZMod 19 => h.rotation i a0)
    (input : OrbitBaseSelectionInput h) (k : ZMod 19)
    (indices : Finset (ZMod 19))
    (hres :
      (ofRotationOrbit h u a0 hu hub0 hinj).fiberUnion indices ⊆
        reflectionCopyResidual h input.base k) :
    (ofRotationOrbit h u a0 hu hub0 hinj).fiberUnion indices ⊆
      rotationOneMovingResidualPart h input k :=
  AFiberRotationEquivariance.fiberUnion_subset_movingResidual_of_subset_residual
      (ofRotationOrbit_rotationEquivariance h u a0 hu hub0 hinj)
      input k indices hres

/-- For moved-branch rotation-orbit A-fiber unions, residual containment
implies moving residual containment. -/
theorem ofRotationOrbitOfMoved_fiberUnion_subset_movingResidual_of_subset_residual
    (h : D19ActsOnMoore57 V Γ) (u a0 : V)
    (hu : ∀ d : ZMod 19, h.rotation d u = u)
    (hub0 : Γ.Adj u a0)
    {d0 : ZMod 19} (hd0 : d0 ≠ 0) (hmove : h.rotation d0 a0 ≠ a0)
    (input : OrbitBaseSelectionInput h) (k : ZMod 19)
    (indices : Finset (ZMod 19))
    (hres :
      (ofRotationOrbitOfMoved h u a0 hu hub0 hd0 hmove).fiberUnion
          indices ⊆
        reflectionCopyResidual h input.base k) :
    (ofRotationOrbitOfMoved h u a0 hu hub0 hd0 hmove).fiberUnion indices ⊆
      rotationOneMovingResidualPart h input k :=
  AFiberRotationEquivariance.fiberUnion_subset_movingResidual_of_subset_residual
      (ofRotationOrbitOfMoved_rotationEquivariance h u a0 hu hub0 hd0 hmove)
      input k indices hres

end AFiberCoordinates

end Moore57
