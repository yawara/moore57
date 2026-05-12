import Moore57.D19OnMoore57.AFiber.RotationTransport

/-!
# A-fiber coordinate rotation equivariance

This file packages the minimal hypotheses saying that the chosen A-fiber
coordinates are equivariant with respect to rotations: the center is fixed and
the branch indexed by `i` is sent to the branch indexed by `i + d`.

The package deliberately stores only these geometric facts.  Coordinate
permutations are derived from `AFiberCoordinates.rotationCoordEquivTo`.
-/

namespace Moore57

universe u uP

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- The minimal rotation equivariance hypotheses for an A-fiber coordinate
system.  No coordinate permutations are stored: they are derived on demand from
the rotation transport API. -/
structure AFiberRotationEquivariance
    (h : D19ActsOnMoore57 V Γ) (coords : AFiberCoordinates.{u, uP} Γ) : Prop where
  /-- Rotations fix the A-fiber center. -/
  rotation_u : ∀ d : ZMod 19, h.rotation d coords.u = coords.u
  /-- Rotation by `d` sends the branch at `i` to the branch at `i + d`. -/
  rotation_a : ∀ d i : ZMod 19, h.rotation d (coords.a i) = coords.a (i + d)

/-- A nonzero step changes an index when added on the right. -/
theorem index_ne_add_of_ne_zero {i d : ZMod 19} (hd : d ≠ 0) :
    i ≠ i + d := by
  intro hidx
  apply hd
  have hcancel : i + d = i + 0 := by
    simpa using hidx.symm
  exact add_left_cancel (a := i) hcancel

namespace AFiberRotationEquivariance

variable {h : D19ActsOnMoore57 V Γ}
variable {coords : AFiberCoordinates.{u, uP} Γ}

/-- The coordinate permutation induced by rotation by `d`, using the chart at
`i` as source and the chart at `i + d` as target. -/
noncomputable def coordPerm (rot : AFiberRotationEquivariance h coords)
    (d i : ZMod 19) : Equiv.Perm coords.P :=
  AFiberCoordinates.rotationCoordEquivTo h coords d i (i + d)
    (rot.rotation_u d) (rot.rotation_a d i)

@[simp] theorem coordPerm_apply
    (rot : AFiberRotationEquivariance h coords)
    (d i : ZMod 19) (p : coords.P) :
    rot.coordPerm d i p =
      (coords.coord (i + d)).symm
        (AFiberCoordinates.rotationFiberEquivTo h coords d i (i + d)
          (rot.rotation_u d) (rot.rotation_a d i) (coords.coord i p)) :=
  rfl

/-- Applying the derived coordinate permutation and then reading the target
chart gives the underlying rotated vertex. -/
@[simp] theorem coord_coordPerm_apply_val
    (rot : AFiberRotationEquivariance h coords)
    (d i : ZMod 19) (p : coords.P) :
    ((coords.coord (i + d) (rot.coordPerm d i p) :
      {x : V // x ∈ branchFiber Γ coords.u (coords.a (i + d))}) : V) =
        h.rotation d
          (((coords.coord i p :
            {x : V // x ∈ branchFiber Γ coords.u (coords.a i)}) : V)) := by
  simp [coordPerm]

/-- Coordinate equality after the derived rotation permutation is equivalent
to equality of the underlying rotated source representative with the target
representative. -/
theorem coordPerm_eq_iff
    (rot : AFiberRotationEquivariance h coords)
    (d i : ZMod 19) (p q : coords.P) :
    rot.coordPerm d i p = q ↔
      h.rotation d
          (((coords.coord i p :
            {x : V // x ∈ branchFiber Γ coords.u (coords.a i)}) : V)) =
        (((coords.coord (i + d) q :
          {x : V // x ∈ branchFiber Γ coords.u (coords.a (i + d))}) : V)) := by
  simpa [coordPerm] using
    AFiberCoordinates.rotationCoordEquivTo_eq_iff h coords d i (i + d)
      (rot.rotation_u d) (rot.rotation_a d i) p q

/-- Rotation transports membership from the `i`-th A-fiber to the
`i + d`-th A-fiber, and reflects it back. -/
theorem rotation_mem_fiber_iff
    (rot : AFiberRotationEquivariance h coords)
    (d i : ZMod 19) (x : V) :
    h.rotation d x ∈ coords.fiber (i + d) ↔ x ∈ coords.fiber i :=
  AFiberCoordinates.rotation_mem_fiber_iff h coords d i (i + d)
    (rot.rotation_u d) (rot.rotation_a d i) x

/-- Forward membership transport for the rotation-induced A-fiber shift. -/
theorem rotation_mem_fiber_of_mem
    (rot : AFiberRotationEquivariance h coords)
    (d i : ZMod 19) {x : V} (hx : x ∈ coords.fiber i) :
    h.rotation d x ∈ coords.fiber (i + d) :=
  (rot.rotation_mem_fiber_iff d i x).2 hx

/-- Backward membership transport for the rotation-induced A-fiber shift. -/
theorem mem_fiber_of_rotation_mem_fiber
    (rot : AFiberRotationEquivariance h coords)
    (d i : ZMod 19) {x : V} (hx : h.rotation d x ∈ coords.fiber (i + d)) :
    x ∈ coords.fiber i :=
  (rot.rotation_mem_fiber_iff d i x).1 hx

/-- A coordinate representative, after rotation, lies in the target A-fiber. -/
theorem rotation_coord_mem_fiber
    (rot : AFiberRotationEquivariance h coords)
    (d i : ZMod 19) (p : coords.P) :
    h.rotation d
        (((coords.coord i p :
          {x : V // x ∈ branchFiber Γ coords.u (coords.a i)}) : V)) ∈
      coords.fiber (i + d) :=
  rot.rotation_mem_fiber_of_mem d i (coords.coord_mem i p)

end AFiberRotationEquivariance

end Moore57
