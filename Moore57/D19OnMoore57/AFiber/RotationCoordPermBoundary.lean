import Moore57.D19OnMoore57.AFiber.CoordinateRotation

/-!
# Algebra of rotation coordinate permutations

This file records the composition law for the coordinate permutations induced
by the D19 rotations on the A-fiber coordinate system.
-/

namespace Moore57

namespace AFiberRotationEquivariance

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]
variable {h : D19ActsOnMoore57 V Γ}
variable {coords : AFiberCoordinates Γ}

/-- Rotation coordinate permutations compose as the underlying rotations do. -/
theorem coordPerm_comp_apply
    (rot : AFiberRotationEquivariance h coords)
    (d e i : ZMod 19) (p : coords.P) :
    rot.coordPerm e (i + d) (rot.coordPerm d i p) =
      rot.coordPerm (d + e) i p := by
  apply (coords.coord ((i + d) + e)).injective
  ext
  have hleft :
      (((coords.coord ((i + d) + e)
          (rot.coordPerm e (i + d) (rot.coordPerm d i p)) :
        {x : V // x ∈ branchFiber Γ coords.u (coords.a ((i + d) + e))}) :
        V)) =
        h.rotation e
          (h.rotation d
            (((coords.coord i p :
              {x : V // x ∈ branchFiber Γ coords.u (coords.a i)}) : V))) := by
    rw [coord_coordPerm_apply_val]
    rw [coord_coordPerm_apply_val]
  have hrot :
      h.rotation e
          (h.rotation d
            (((coords.coord i p :
              {x : V // x ∈ branchFiber Γ coords.u (coords.a i)}) : V))) =
        h.rotation (d + e)
          (((coords.coord i p :
            {x : V // x ∈ branchFiber Γ coords.u (coords.a i)}) : V)) := by
    calc
      h.rotation e
          (h.rotation d
            (((coords.coord i p :
              {x : V // x ∈ branchFiber Γ coords.u (coords.a i)}) : V)))
          = h.rotation (e + d)
              (((coords.coord i p :
                {x : V // x ∈ branchFiber Γ coords.u (coords.a i)}) : V)) := by
              rw [h.rotation_add e d]
              rfl
      _ = h.rotation (d + e)
              (((coords.coord i p :
                {x : V // x ∈ branchFiber Γ coords.u (coords.a i)}) : V)) := by
              congr 1
              ring_nf
  have hright :
      (((coords.coord ((i + d) + e)
          (rot.coordPerm (d + e) i p) :
        {x : V // x ∈ branchFiber Γ coords.u (coords.a ((i + d) + e))}) :
        V)) =
        h.rotation (d + e)
          (((coords.coord i p :
            {x : V // x ∈ branchFiber Γ coords.u (coords.a i)}) : V)) := by
    have hright0 :=
      coord_coordPerm_apply_val (rot := rot) (d := d + e) (i := i) (p := p)
    have hidx : i + (d + e) = (i + d) + e := by
      ring_nf
    rw [hidx] at hright0
    exact hright0
  exact hleft.trans (hrot.trans hright.symm)

/-- Symmetric spelling of `coordPerm_comp_apply`, often convenient when the
second offset is written first. -/
theorem coordPerm_add_apply
    (rot : AFiberRotationEquivariance h coords)
    (d e i : ZMod 19) (p : coords.P) :
    rot.coordPerm d (i + e) (rot.coordPerm e i p) =
      rot.coordPerm (e + d) i p := by
  simpa using rot.coordPerm_comp_apply e d i p

end AFiberRotationEquivariance

end Moore57
