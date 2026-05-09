import Moore57.AFiberCoordinateConstruction
import Moore57.AFiberCoordinateRotation

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

end AFiberCoordinates

end Moore57
