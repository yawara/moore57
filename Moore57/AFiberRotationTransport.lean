import Moore57.BranchFiberAction
import Moore57.AdjacentMovedReflectionAFiberCriteria

/-!
# Rotation transport for A-fiber coordinates

This file transports a rotation that fixes the A-fiber center and sends one
A-branch to another through the corresponding branch-fiber subtypes and then
through an `AFiberCoordinates` chart.
-/

namespace Moore57

namespace AFiberCoordinates

variable {V : Type*} [Fintype V] [DecidableEq V]
    {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- A rotation carrying `coords.a i` to `coords.a j`, while fixing the center,
gives an equivalence from the `i`-th branch fiber subtype to the `j`-th one. -/
noncomputable def rotationFiberEquivTo
    (h : D19ActsOnMoore57 V Γ) (coords : AFiberCoordinates Γ)
    (d i j : ZMod 19)
    (hu : h.rotation d coords.u = coords.u)
    (haij : h.rotation d (coords.a i) = coords.a j) :
    {x : V // x ∈ branchFiber Γ coords.u (coords.a i)} ≃
      {x : V // x ∈ branchFiber Γ coords.u (coords.a j)} :=
  (h.rotation d).subtypeEquiv fun x => by
    simpa [haij] using
      (h.rotation_mem_branchFiber_iff d
        (u := coords.u) (b := coords.a i) (x := x) hu).symm

@[simp] theorem rotationFiberEquivTo_apply_val
    (h : D19ActsOnMoore57 V Γ) (coords : AFiberCoordinates Γ)
    (d i j : ZMod 19)
    (hu : h.rotation d coords.u = coords.u)
    (haij : h.rotation d (coords.a i) = coords.a j)
    (x : {x : V // x ∈ branchFiber Γ coords.u (coords.a i)}) :
    (rotationFiberEquivTo h coords d i j hu haij x : V) =
      h.rotation d (x : V) :=
  rfl

theorem rotationFiberEquivTo_apply_eq
    (h : D19ActsOnMoore57 V Γ) (coords : AFiberCoordinates Γ)
    (d i j : ZMod 19)
    (hu : h.rotation d coords.u = coords.u)
    (haij : h.rotation d (coords.a i) = coords.a j)
    (x : {x : V // x ∈ branchFiber Γ coords.u (coords.a i)}) :
    rotationFiberEquivTo h coords d i j hu haij x =
      ⟨h.rotation d (x : V), by
        have hx :
            h.rotation d (x : V) ∈
              branchFiber Γ coords.u (h.rotation d (coords.a i)) :=
          (h.rotation_mem_branchFiber_iff d
            (u := coords.u) (b := coords.a i) (x := (x : V)) hu).2 x.property
        simpa [haij] using hx⟩ := by
  ext
  rfl

@[simp] theorem rotationFiberEquivTo_symm_apply_val
    (h : D19ActsOnMoore57 V Γ) (coords : AFiberCoordinates Γ)
    (d i j : ZMod 19)
    (hu : h.rotation d coords.u = coords.u)
    (haij : h.rotation d (coords.a i) = coords.a j)
    (x : {x : V // x ∈ branchFiber Γ coords.u (coords.a j)}) :
    ((rotationFiberEquivTo h coords d i j hu haij).symm x : V) =
      (h.rotation d).symm (x : V) :=
  rfl

/-- The rotation-induced permutation of the common A-fiber coordinate type,
using the chart at `i` as source and the chart at `j` as target. -/
noncomputable def rotationCoordEquivTo
    (h : D19ActsOnMoore57 V Γ) (coords : AFiberCoordinates Γ)
    (d i j : ZMod 19)
    (hu : h.rotation d coords.u = coords.u)
    (haij : h.rotation d (coords.a i) = coords.a j) :
    coords.P ≃ coords.P :=
  ((coords.coord i).trans
      (rotationFiberEquivTo h coords d i j hu haij)).trans
    (coords.coord j).symm

@[simp] theorem rotationCoordEquivTo_apply
    (h : D19ActsOnMoore57 V Γ) (coords : AFiberCoordinates Γ)
    (d i j : ZMod 19)
    (hu : h.rotation d coords.u = coords.u)
    (haij : h.rotation d (coords.a i) = coords.a j)
    (p : coords.P) :
    rotationCoordEquivTo h coords d i j hu haij p =
      (coords.coord j).symm
        (rotationFiberEquivTo h coords d i j hu haij (coords.coord i p)) :=
  rfl

@[simp] theorem coord_rotationCoordEquivTo_apply_val
    (h : D19ActsOnMoore57 V Γ) (coords : AFiberCoordinates Γ)
    (d i j : ZMod 19)
    (hu : h.rotation d coords.u = coords.u)
    (haij : h.rotation d (coords.a i) = coords.a j)
    (p : coords.P) :
    ((coords.coord j (rotationCoordEquivTo h coords d i j hu haij p) :
      {x : V // x ∈ branchFiber Γ coords.u (coords.a j)}) : V) =
        h.rotation d
          (((coords.coord i p :
            {x : V // x ∈ branchFiber Γ coords.u (coords.a i)}) : V)) := by
  simp [rotationCoordEquivTo]

@[simp] theorem coord_rotationCoordEquivTo_symm_apply_val
    (h : D19ActsOnMoore57 V Γ) (coords : AFiberCoordinates Γ)
    (d i j : ZMod 19)
    (hu : h.rotation d coords.u = coords.u)
    (haij : h.rotation d (coords.a i) = coords.a j)
    (p : coords.P) :
    ((coords.coord i ((rotationCoordEquivTo h coords d i j hu haij).symm p) :
      {x : V // x ∈ branchFiber Γ coords.u (coords.a i)}) : V) =
        (h.rotation d).symm
          (((coords.coord j p :
            {x : V // x ∈ branchFiber Γ coords.u (coords.a j)}) : V)) := by
  simp [rotationCoordEquivTo]

/-- Coordinate equality after rotation is the same as equality of the rotated
source representative with the target representative. -/
theorem rotationCoordEquivTo_eq_iff
    (h : D19ActsOnMoore57 V Γ) (coords : AFiberCoordinates Γ)
    (d i j : ZMod 19)
    (hu : h.rotation d coords.u = coords.u)
    (haij : h.rotation d (coords.a i) = coords.a j)
    (p q : coords.P) :
    rotationCoordEquivTo h coords d i j hu haij p = q ↔
      h.rotation d
          (((coords.coord i p :
            {x : V // x ∈ branchFiber Γ coords.u (coords.a i)}) : V)) =
        (((coords.coord j q :
          {x : V // x ∈ branchFiber Γ coords.u (coords.a j)}) : V)) := by
  constructor
  · intro hpq
    rw [← hpq]
    exact (coord_rotationCoordEquivTo_apply_val h coords d i j hu haij p).symm
  · intro hpq
    apply (coords.coord j).injective
    ext
    exact (coord_rotationCoordEquivTo_apply_val h coords d i j hu haij p).trans hpq

/-- Membership in A-fibers is transported by a rotation carrying the source
branch to the target branch. -/
theorem rotation_mem_fiber_iff
    (h : D19ActsOnMoore57 V Γ) (coords : AFiberCoordinates Γ)
    (d i j : ZMod 19)
    (hu : h.rotation d coords.u = coords.u)
    (haij : h.rotation d (coords.a i) = coords.a j)
    (x : V) :
    h.rotation d x ∈ coords.fiber j ↔ x ∈ coords.fiber i := by
  simpa [fiber, haij] using
    h.rotation_mem_branchFiber_iff d
      (u := coords.u) (b := coords.a i) (x := x) hu

theorem rotation_mem_fiber_of_mem
    (h : D19ActsOnMoore57 V Γ) (coords : AFiberCoordinates Γ)
    (d i j : ZMod 19)
    (hu : h.rotation d coords.u = coords.u)
    (haij : h.rotation d (coords.a i) = coords.a j)
    {x : V} (hx : x ∈ coords.fiber i) :
    h.rotation d x ∈ coords.fiber j :=
  (rotation_mem_fiber_iff h coords d i j hu haij x).2 hx

theorem mem_fiber_of_rotation_mem_fiber
    (h : D19ActsOnMoore57 V Γ) (coords : AFiberCoordinates Γ)
    (d i j : ZMod 19)
    (hu : h.rotation d coords.u = coords.u)
    (haij : h.rotation d (coords.a i) = coords.a j)
    {x : V} (hx : h.rotation d x ∈ coords.fiber j) :
    x ∈ coords.fiber i :=
  (rotation_mem_fiber_iff h coords d i j hu haij x).1 hx

end AFiberCoordinates

end Moore57
