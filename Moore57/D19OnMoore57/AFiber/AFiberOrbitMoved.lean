import Moore57.D19OnMoore57.AFiber.AFiberCoordinateOrbit

/-!
# Moved points in rotation-orbit A-fibers

This file records the geometric obstruction that a point in one branch fiber
of a rotation-equivariant A-fiber coordinate system cannot be fixed by a
nonzero rotation step.  Rotating the fiber membership would put the same point
in a distinct branch fiber over the same center, contradicting the Moore graph
common-neighbor uniqueness property.
-/

namespace Moore57

universe u uP

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

namespace AFiberRotationEquivariance

variable {h : D19ActsOnMoore57 V Γ}
variable {coords : AFiberCoordinates.{u, uP} Γ}

/-- A vertex in an equivariant A-fiber is moved by every nonzero rotation
step. -/
theorem moved_by_nonzero_rotation_of_mem_fiber
    (rot : AFiberRotationEquivariance h coords)
    {d i : ZMod 19} (hd : d ≠ 0) {y : V}
    (hy : y ∈ coords.fiber i) :
    h.rotation d y ≠ y := by
  intro hfixed
  have hyTarget : y ∈ coords.fiber (i + d) := by
    simpa [hfixed] using rot.rotation_mem_fiber_of_mem d i hy
  have hbranch_ne : coords.a i ≠ coords.a (i + d) :=
    coords.a_ne (index_ne_add_of_ne_zero hd)
  have hnot_adj : ¬ Γ.Adj y (coords.a (i + d)) :=
    h.isMoore.not_adj_other_branch_of_mem_branchFiber
      (coords.hub i) (coords.hub (i + d)) hbranch_ne hy
  exact hnot_adj (mem_branchFiber.mp hyTarget).2.symm

end AFiberRotationEquivariance

namespace AFiberCoordinates

/-- In A-fiber coordinates built from an injective rotation orbit, every point
in every branch fiber is moved by rotation `1`. -/
theorem ofRotationOrbit_fiber_moved_by_rotation_one
    (h : D19ActsOnMoore57 V Γ) (u a0 : V)
    (hu : ∀ d : ZMod 19, h.rotation d u = u)
    (hub0 : Γ.Adj u a0)
    (hinj : Function.Injective fun i : ZMod 19 => h.rotation i a0)
    {i : ZMod 19} {y : V}
    (hy : y ∈ (ofRotationOrbit h u a0 hu hub0 hinj).fiber i) :
    h.rotation 1 y ≠ y :=
  AFiberRotationEquivariance.moved_by_nonzero_rotation_of_mem_fiber
    (ofRotationOrbit_rotationEquivariance h u a0 hu hub0 hinj)
    (d := 1) (i := i) (by decide) hy

/-- The same movedness statement for the convenience constructor whose orbit
injectivity is obtained from a moved nonzero rotation of the branch. -/
theorem ofRotationOrbitOfMoved_fiber_moved_by_rotation_one
    (h : D19ActsOnMoore57 V Γ) (u a0 : V)
    (hu : ∀ d : ZMod 19, h.rotation d u = u)
    (hub0 : Γ.Adj u a0)
    {d0 : ZMod 19} (hd0 : d0 ≠ 0) (hmove : h.rotation d0 a0 ≠ a0)
    {i : ZMod 19} {y : V}
    (hy : y ∈ (ofRotationOrbitOfMoved h u a0 hu hub0 hd0 hmove).fiber i) :
    h.rotation 1 y ≠ y :=
  AFiberRotationEquivariance.moved_by_nonzero_rotation_of_mem_fiber
    (ofRotationOrbitOfMoved_rotationEquivariance h u a0 hu hub0 hd0 hmove)
    (d := 1) (i := i) (by decide) hy

end AFiberCoordinates

end Moore57
