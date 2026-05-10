import Moore57.AFiberCoordinateRotation
import Moore57.AFiberMatchingPerm

/-!
# Rotation transport for A-fiber matching equations

The branch-fiber matching is equivariant under graph automorphisms.  This file
records the coordinate form needed later for the card-two common-neighbor
construction: a matching equation between fibers `i` and `j` can be rotated to
the matching equation between `i + k` and `j + k`.
-/

namespace Moore57

namespace AFiberCoordinates

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]
variable {h : D19ActsOnMoore57 V Γ}
variable {coords : AFiberCoordinates Γ}

/-- Rotating a matching equation gives the matching equation between the
rotated A-fibers. -/
theorem matchingEquiv_rotationCoordPerm_eq_rotationCoordPerm_of_matchingEquiv_eq
    (hΓ : IsMoore57 Γ)
    (rot : AFiberRotationEquivariance h coords)
    {i j k : ZMod 19} (hij : i ≠ j)
    (p q : coords.P)
    (hm :
      matchingEquiv hΓ coords i j hij p = q) :
    matchingEquiv hΓ coords (i + k) (j + k)
        (by
          intro hidx
          exact hij (add_right_cancel hidx)) (rot.coordPerm k i p) =
      rot.coordPerm k j q := by
  have hadj :
      Γ.Adj
        (((coords.coord i p :
          {x : V // x ∈ branchFiber Γ coords.u (coords.a i)}) : V))
        (((coords.coord j q :
          {x : V // x ∈ branchFiber Γ coords.u (coords.a j)}) : V)) :=
    (adj_iff_matchingEquiv_eq hΓ coords hij p q).2 hm
  have hadj_rot :
      Γ.Adj
        (h.rotation k
          (((coords.coord i p :
            {x : V // x ∈ branchFiber Γ coords.u (coords.a i)}) : V)))
        (h.rotation k
          (((coords.coord j q :
            {x : V // x ∈ branchFiber Γ coords.u (coords.a j)}) : V))) := by
    simpa [D19ActsOnMoore57.rotation] using
      (h.smul_adj (DihedralGroup.r k)
        (((coords.coord i p :
          {x : V // x ∈ branchFiber Γ coords.u (coords.a i)}) : V))
        (((coords.coord j q :
          {x : V // x ∈ branchFiber Γ coords.u (coords.a j)}) : V))).mp hadj
  exact
    (adj_iff_matchingEquiv_eq hΓ coords
      (by
        intro hidx
        exact hij (add_right_cancel hidx))
      (rot.coordPerm k i p) (rot.coordPerm k j q)).1
      (by
        simpa [AFiberRotationEquivariance.coord_coordPerm_apply_val] using
          hadj_rot)

/-- Endpoint-offset specialization: a matching equation from `0` to `d`
rotates to one from `k` to `k + d`. -/
theorem matchingEquiv_rotationCoordPerm_eq_rotationCoordPerm_of_endpoint_matching
    (hΓ : IsMoore57 Γ)
    (rot : AFiberRotationEquivariance h coords)
    {d k : ZMod 19} (hd : d ≠ 0)
    (p q : coords.P)
    (hm :
      matchingEquiv hΓ coords 0 (0 + d)
        (index_ne_add_of_ne_zero hd) p = q) :
    matchingEquiv hΓ coords (0 + k) ((0 + d) + k)
        (by
          intro hidx
          exact (index_ne_add_of_ne_zero hd)
            (add_right_cancel hidx)) (rot.coordPerm k 0 p) =
      rot.coordPerm k (0 + d) q := by
  exact
    matchingEquiv_rotationCoordPerm_eq_rotationCoordPerm_of_matchingEquiv_eq
      hΓ rot (index_ne_add_of_ne_zero hd) p q hm

end AFiberCoordinates

end Moore57
