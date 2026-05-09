import Moore57.AFiberCoordinateConstruction
import Moore57.AFiberCoordinateRotation
import Moore57.RotationOrbitFinset

/-!
# A-fiber coordinates from a rotation orbit

This file constructs A-side fiber coordinates from a single branch vertex whose
rotation orbit supplies the `ZMod 19`-indexed A-branches.  The resulting
coordinates automatically satisfy `AFiberRotationEquivariance`.
-/

namespace Moore57

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

namespace D19ActsOnMoore57

/-- If rotations fix the center `u`, then rotating a branch adjacent to `u`
keeps it adjacent to `u`. -/
theorem adj_rotation_of_fixed_center
    (h : D19ActsOnMoore57 V Γ) {u a0 : V}
    (hu : ∀ d : ZMod 19, h.rotation d u = u)
    (hub0 : Γ.Adj u a0) (i : ZMod 19) :
    Γ.Adj u (h.rotation i a0) := by
  have hadj : Γ.Adj (h.rotation i u) (h.rotation i a0) := by
    simpa [D19ActsOnMoore57.rotation] using
      (h.smul_adj (DihedralGroup.r i) u a0).mp hub0
  simpa [hu i] using hadj

end D19ActsOnMoore57

namespace AFiberCoordinates

/-- Build A-side fiber coordinates from one branch vertex and its rotation
orbit around a rotation-fixed center. -/
noncomputable def ofRotationOrbit
    (h : D19ActsOnMoore57 V Γ) (u a0 : V)
    (hu : ∀ d : ZMod 19, h.rotation d u = u)
    (hub0 : Γ.Adj u a0)
    (hinj : Function.Injective fun i : ZMod 19 => h.rotation i a0) :
    AFiberCoordinates Γ :=
  ofBranches h.isMoore u (fun i : ZMod 19 => h.rotation i a0)
    (fun i => h.adj_rotation_of_fixed_center hu hub0 i) hinj

/-- Build A-side fiber coordinates from one branch vertex and its rotation
orbit when a nonzero rotation moves the branch vertex. -/
noncomputable def ofRotationOrbitOfMoved
    (h : D19ActsOnMoore57 V Γ) (u a0 : V)
    (hu : ∀ d : ZMod 19, h.rotation d u = u)
    (hub0 : Γ.Adj u a0)
    {d : ZMod 19} (hd : d ≠ 0) (hmove : h.rotation d a0 ≠ a0) :
    AFiberCoordinates Γ :=
  ofRotationOrbit h u a0 hu hub0
    (h.rotationOrbitW_injective_of_nonzero_moved hd hmove)

@[simp] theorem ofRotationOrbit_u
    (h : D19ActsOnMoore57 V Γ) (u a0 : V)
    (hu : ∀ d : ZMod 19, h.rotation d u = u)
    (hub0 : Γ.Adj u a0)
    (hinj : Function.Injective fun i : ZMod 19 => h.rotation i a0) :
    (ofRotationOrbit h u a0 hu hub0 hinj).u = u :=
  rfl

@[simp] theorem ofRotationOrbit_a
    (h : D19ActsOnMoore57 V Γ) (u a0 : V)
    (hu : ∀ d : ZMod 19, h.rotation d u = u)
    (hub0 : Γ.Adj u a0)
    (hinj : Function.Injective fun i : ZMod 19 => h.rotation i a0) :
    (ofRotationOrbit h u a0 hu hub0 hinj).a =
      fun i : ZMod 19 => h.rotation i a0 :=
  rfl

@[simp] theorem ofRotationOrbit_a_apply
    (h : D19ActsOnMoore57 V Γ) (u a0 : V)
    (hu : ∀ d : ZMod 19, h.rotation d u = u)
    (hub0 : Γ.Adj u a0)
    (hinj : Function.Injective fun i : ZMod 19 => h.rotation i a0)
    (i : ZMod 19) :
    (ofRotationOrbit h u a0 hu hub0 hinj).a i = h.rotation i a0 :=
  rfl

@[simp] theorem ofRotationOrbit_a_zero
    (h : D19ActsOnMoore57 V Γ) (u a0 : V)
    (hu : ∀ d : ZMod 19, h.rotation d u = u)
    (hub0 : Γ.Adj u a0)
    (hinj : Function.Injective fun i : ZMod 19 => h.rotation i a0) :
    (ofRotationOrbit h u a0 hu hub0 hinj).a 0 = a0 := by
  simp

@[simp] theorem ofRotationOrbitOfMoved_u
    (h : D19ActsOnMoore57 V Γ) (u a0 : V)
    (hu : ∀ d : ZMod 19, h.rotation d u = u)
    (hub0 : Γ.Adj u a0)
    {d : ZMod 19} (hd : d ≠ 0) (hmove : h.rotation d a0 ≠ a0) :
    (ofRotationOrbitOfMoved h u a0 hu hub0 hd hmove).u = u :=
  rfl

@[simp] theorem ofRotationOrbitOfMoved_a
    (h : D19ActsOnMoore57 V Γ) (u a0 : V)
    (hu : ∀ d : ZMod 19, h.rotation d u = u)
    (hub0 : Γ.Adj u a0)
    {d : ZMod 19} (hd : d ≠ 0) (hmove : h.rotation d a0 ≠ a0) :
    (ofRotationOrbitOfMoved h u a0 hu hub0 hd hmove).a =
      fun i : ZMod 19 => h.rotation i a0 :=
  rfl

@[simp] theorem ofRotationOrbitOfMoved_a_apply
    (h : D19ActsOnMoore57 V Γ) (u a0 : V)
    (hu : ∀ d : ZMod 19, h.rotation d u = u)
    (hub0 : Γ.Adj u a0)
    {d : ZMod 19} (hd : d ≠ 0) (hmove : h.rotation d a0 ≠ a0)
    (i : ZMod 19) :
    (ofRotationOrbitOfMoved h u a0 hu hub0 hd hmove).a i = h.rotation i a0 :=
  rfl

@[simp] theorem ofRotationOrbitOfMoved_a_zero
    (h : D19ActsOnMoore57 V Γ) (u a0 : V)
    (hu : ∀ d : ZMod 19, h.rotation d u = u)
    (hub0 : Γ.Adj u a0)
    {d : ZMod 19} (hd : d ≠ 0) (hmove : h.rotation d a0 ≠ a0) :
    (ofRotationOrbitOfMoved h u a0 hu hub0 hd hmove).a 0 = a0 := by
  simp

/-- Rotation-orbit A-fiber coordinates are equivariant under rotations. -/
theorem ofRotationOrbit_rotationEquivariance
    (h : D19ActsOnMoore57 V Γ) (u a0 : V)
    (hu : ∀ d : ZMod 19, h.rotation d u = u)
    (hub0 : Γ.Adj u a0)
    (hinj : Function.Injective fun i : ZMod 19 => h.rotation i a0) :
    AFiberRotationEquivariance h (ofRotationOrbit h u a0 hu hub0 hinj) := by
  refine ⟨?_, ?_⟩
  · intro d
    exact hu d
  · intro d i
    change h.rotation d (h.rotation i a0) = h.rotation (i + d) a0
    calc
      h.rotation d (h.rotation i a0)
          = (h.rotation d * h.rotation i) a0 := by
              simp [Equiv.Perm.mul_apply]
      _ = h.rotation (d + i) a0 := by
              rw [← h.rotation_add]
      _ = h.rotation (i + d) a0 := by
              rw [add_comm]

/-- Rotation-orbit A-fiber coordinates built from a moved branch are
equivariant under rotations. -/
theorem ofRotationOrbitOfMoved_rotationEquivariance
    (h : D19ActsOnMoore57 V Γ) (u a0 : V)
    (hu : ∀ d : ZMod 19, h.rotation d u = u)
    (hub0 : Γ.Adj u a0)
    {d : ZMod 19} (hd : d ≠ 0) (hmove : h.rotation d a0 ≠ a0) :
    AFiberRotationEquivariance h
      (ofRotationOrbitOfMoved h u a0 hu hub0 hd hmove) :=
  ofRotationOrbit_rotationEquivariance h u a0 hu hub0
    (h.rotationOrbitW_injective_of_nonzero_moved hd hmove)

/-- The coordinate permutation for rotation-orbit coordinates is the generic
rotation transport permutation specialized to the constructed coordinates. -/
theorem ofRotationOrbit_coordPerm
    (h : D19ActsOnMoore57 V Γ) (u a0 : V)
    (hu : ∀ d : ZMod 19, h.rotation d u = u)
    (hub0 : Γ.Adj u a0)
    (hinj : Function.Injective fun i : ZMod 19 => h.rotation i a0)
    (d i : ZMod 19) :
    (ofRotationOrbit_rotationEquivariance h u a0 hu hub0 hinj).coordPerm d i =
      rotationCoordEquivTo h (ofRotationOrbit h u a0 hu hub0 hinj) d i (i + d)
        ((ofRotationOrbit_rotationEquivariance h u a0 hu hub0 hinj).rotation_u d)
        ((ofRotationOrbit_rotationEquivariance h u a0 hu hub0 hinj).rotation_a d i) :=
  rfl

/-- The coordinate permutation for moved-branch rotation-orbit coordinates is
the generic rotation transport permutation specialized to those coordinates. -/
theorem ofRotationOrbitOfMoved_coordPerm
    (h : D19ActsOnMoore57 V Γ) (u a0 : V)
    (hu : ∀ d : ZMod 19, h.rotation d u = u)
    (hub0 : Γ.Adj u a0)
    {d₀ : ZMod 19} (hd₀ : d₀ ≠ 0) (hmove : h.rotation d₀ a0 ≠ a0)
    (d i : ZMod 19) :
    (ofRotationOrbitOfMoved_rotationEquivariance h u a0 hu hub0 hd₀ hmove).coordPerm d i =
      rotationCoordEquivTo h (ofRotationOrbitOfMoved h u a0 hu hub0 hd₀ hmove) d i (i + d)
        ((ofRotationOrbitOfMoved_rotationEquivariance h u a0 hu hub0 hd₀ hmove).rotation_u d)
        ((ofRotationOrbitOfMoved_rotationEquivariance h u a0 hu hub0 hd₀ hmove).rotation_a d i) :=
  rfl

end AFiberCoordinates

end Moore57
