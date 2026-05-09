import Moore57.AFiberRotationTransport

/-!
# Reflection transport for A-fiber coordinates

This file is the reflection analogue of `AFiberRotationTransport`: if a
reflection fixes the A-fiber center and sends one A-branch to another, it
transports the corresponding branch-fiber subtypes and the shared coordinate
type.
-/

namespace Moore57

namespace AFiberCoordinates

variable {V : Type*} [Fintype V] [DecidableEq V]
    {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- A reflection carrying `coords.a i` to `coords.a j`, while fixing the
center, gives an equivalence from the `i`-th branch fiber subtype to the
`j`-th one. -/
noncomputable def reflectionFiberEquivTo
    (h : D19ActsOnMoore57 V Γ) (coords : AFiberCoordinates Γ)
    (k i j : ZMod 19)
    (hu : h.smul (DihedralGroup.sr k) coords.u = coords.u)
    (haij : h.smul (DihedralGroup.sr k) (coords.a i) = coords.a j) :
    {x : V // x ∈ branchFiber Γ coords.u (coords.a i)} ≃
      {x : V // x ∈ branchFiber Γ coords.u (coords.a j)} :=
  (h.smulEquiv (DihedralGroup.sr k)).subtypeEquiv fun x => by
    simpa [haij] using
      (h.smul_mem_branchFiber_iff (DihedralGroup.sr k)
        (u := coords.u) (b := coords.a i) (x := x) hu).symm

@[simp] theorem reflectionFiberEquivTo_apply_val
    (h : D19ActsOnMoore57 V Γ) (coords : AFiberCoordinates Γ)
    (k i j : ZMod 19)
    (hu : h.smul (DihedralGroup.sr k) coords.u = coords.u)
    (haij : h.smul (DihedralGroup.sr k) (coords.a i) = coords.a j)
    (x : {x : V // x ∈ branchFiber Γ coords.u (coords.a i)}) :
    (reflectionFiberEquivTo h coords k i j hu haij x : V) =
      h.smul (DihedralGroup.sr k) (x : V) :=
  rfl

theorem reflectionFiberEquivTo_apply_eq
    (h : D19ActsOnMoore57 V Γ) (coords : AFiberCoordinates Γ)
    (k i j : ZMod 19)
    (hu : h.smul (DihedralGroup.sr k) coords.u = coords.u)
    (haij : h.smul (DihedralGroup.sr k) (coords.a i) = coords.a j)
    (x : {x : V // x ∈ branchFiber Γ coords.u (coords.a i)}) :
    reflectionFiberEquivTo h coords k i j hu haij x =
      ⟨h.smul (DihedralGroup.sr k) (x : V), by
        have hx :
            h.smul (DihedralGroup.sr k) (x : V) ∈
              branchFiber Γ coords.u
                (h.smul (DihedralGroup.sr k) (coords.a i)) :=
          (h.smul_mem_branchFiber_iff (DihedralGroup.sr k)
            (u := coords.u) (b := coords.a i) (x := (x : V)) hu).2 x.property
        simpa [haij] using hx⟩ := by
  ext
  rfl

@[simp] theorem reflectionFiberEquivTo_symm_apply_val
    (h : D19ActsOnMoore57 V Γ) (coords : AFiberCoordinates Γ)
    (k i j : ZMod 19)
    (hu : h.smul (DihedralGroup.sr k) coords.u = coords.u)
    (haij : h.smul (DihedralGroup.sr k) (coords.a i) = coords.a j)
    (x : {x : V // x ∈ branchFiber Γ coords.u (coords.a j)}) :
    ((reflectionFiberEquivTo h coords k i j hu haij).symm x : V) =
      (h.smulEquiv (DihedralGroup.sr k)).symm (x : V) :=
  rfl

/-- The reflection-induced permutation of the common A-fiber coordinate type,
using the chart at `i` as source and the chart at `j` as target. -/
noncomputable def reflectionCoordEquivTo
    (h : D19ActsOnMoore57 V Γ) (coords : AFiberCoordinates Γ)
    (k i j : ZMod 19)
    (hu : h.smul (DihedralGroup.sr k) coords.u = coords.u)
    (haij : h.smul (DihedralGroup.sr k) (coords.a i) = coords.a j) :
    coords.P ≃ coords.P :=
  ((coords.coord i).trans
      (reflectionFiberEquivTo h coords k i j hu haij)).trans
    (coords.coord j).symm

@[simp] theorem reflectionCoordEquivTo_apply
    (h : D19ActsOnMoore57 V Γ) (coords : AFiberCoordinates Γ)
    (k i j : ZMod 19)
    (hu : h.smul (DihedralGroup.sr k) coords.u = coords.u)
    (haij : h.smul (DihedralGroup.sr k) (coords.a i) = coords.a j)
    (p : coords.P) :
    reflectionCoordEquivTo h coords k i j hu haij p =
      (coords.coord j).symm
        (reflectionFiberEquivTo h coords k i j hu haij (coords.coord i p)) :=
  rfl

@[simp] theorem coord_reflectionCoordEquivTo_apply_val
    (h : D19ActsOnMoore57 V Γ) (coords : AFiberCoordinates Γ)
    (k i j : ZMod 19)
    (hu : h.smul (DihedralGroup.sr k) coords.u = coords.u)
    (haij : h.smul (DihedralGroup.sr k) (coords.a i) = coords.a j)
    (p : coords.P) :
    ((coords.coord j (reflectionCoordEquivTo h coords k i j hu haij p) :
      {x : V // x ∈ branchFiber Γ coords.u (coords.a j)}) : V) =
        h.smul (DihedralGroup.sr k)
          (((coords.coord i p :
            {x : V // x ∈ branchFiber Γ coords.u (coords.a i)}) : V)) := by
  simp [reflectionCoordEquivTo]

@[simp] theorem coord_reflectionCoordEquivTo_symm_apply_val
    (h : D19ActsOnMoore57 V Γ) (coords : AFiberCoordinates Γ)
    (k i j : ZMod 19)
    (hu : h.smul (DihedralGroup.sr k) coords.u = coords.u)
    (haij : h.smul (DihedralGroup.sr k) (coords.a i) = coords.a j)
    (p : coords.P) :
    ((coords.coord i ((reflectionCoordEquivTo h coords k i j hu haij).symm p) :
      {x : V // x ∈ branchFiber Γ coords.u (coords.a i)}) : V) =
        (h.smulEquiv (DihedralGroup.sr k)).symm
          (((coords.coord j p :
            {x : V // x ∈ branchFiber Γ coords.u (coords.a j)}) : V)) := by
  simp [reflectionCoordEquivTo]

/-- Coordinate equality after reflection is the same as equality of the
reflected source representative with the target representative. -/
theorem reflectionCoordEquivTo_eq_iff
    (h : D19ActsOnMoore57 V Γ) (coords : AFiberCoordinates Γ)
    (k i j : ZMod 19)
    (hu : h.smul (DihedralGroup.sr k) coords.u = coords.u)
    (haij : h.smul (DihedralGroup.sr k) (coords.a i) = coords.a j)
    (p q : coords.P) :
    reflectionCoordEquivTo h coords k i j hu haij p = q ↔
      h.smul (DihedralGroup.sr k)
          (((coords.coord i p :
            {x : V // x ∈ branchFiber Γ coords.u (coords.a i)}) : V)) =
        (((coords.coord j q :
          {x : V // x ∈ branchFiber Γ coords.u (coords.a j)}) : V)) := by
  constructor
  · intro hpq
    rw [← hpq]
    exact (coord_reflectionCoordEquivTo_apply_val h coords k i j hu haij p).symm
  · intro hpq
    apply (coords.coord j).injective
    ext
    exact (coord_reflectionCoordEquivTo_apply_val h coords k i j hu haij p).trans hpq

/-- Membership in A-fibers is transported by a reflection carrying the source
branch to the target branch. -/
theorem reflection_mem_fiber_iff
    (h : D19ActsOnMoore57 V Γ) (coords : AFiberCoordinates Γ)
    (k i j : ZMod 19)
    (hu : h.smul (DihedralGroup.sr k) coords.u = coords.u)
    (haij : h.smul (DihedralGroup.sr k) (coords.a i) = coords.a j)
    (x : V) :
    h.smul (DihedralGroup.sr k) x ∈ coords.fiber j ↔ x ∈ coords.fiber i := by
  simpa [fiber, haij] using
    h.smul_mem_branchFiber_iff (DihedralGroup.sr k)
      (u := coords.u) (b := coords.a i) (x := x) hu

theorem reflection_mem_fiber_of_mem
    (h : D19ActsOnMoore57 V Γ) (coords : AFiberCoordinates Γ)
    (k i j : ZMod 19)
    (hu : h.smul (DihedralGroup.sr k) coords.u = coords.u)
    (haij : h.smul (DihedralGroup.sr k) (coords.a i) = coords.a j)
    {x : V} (hx : x ∈ coords.fiber i) :
    h.smul (DihedralGroup.sr k) x ∈ coords.fiber j :=
  (reflection_mem_fiber_iff h coords k i j hu haij x).2 hx

theorem mem_fiber_of_reflection_mem_fiber
    (h : D19ActsOnMoore57 V Γ) (coords : AFiberCoordinates Γ)
    (k i j : ZMod 19)
    (hu : h.smul (DihedralGroup.sr k) coords.u = coords.u)
    (haij : h.smul (DihedralGroup.sr k) (coords.a i) = coords.a j)
    {x : V} (hx : h.smul (DihedralGroup.sr k) x ∈ coords.fiber j) :
    x ∈ coords.fiber i :=
  (reflection_mem_fiber_iff h coords k i j hu haij x).1 hx

end AFiberCoordinates

end Moore57
