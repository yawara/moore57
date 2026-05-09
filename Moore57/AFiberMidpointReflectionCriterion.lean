import Moore57.AFiberCoordinateReflection
import Moore57.AFiberCoordinateRotation
import Moore57.AFiberMatchingPermAdjacency
import Moore57.ZMod19Lemmas

/-!
# Forward midpoint-reflection criterion

This file proves the easy half of the midpoint-reflection criterion: if the
matching from `L_0` to the reflected endpoint agrees with the reflection image,
then the midpoint mate is moved by the midpoint reflection.
-/

namespace Moore57

universe u uP

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

namespace AFiberReflectionEquivariance

variable {h : D19ActsOnMoore57 V Γ}
variable {coords : AFiberCoordinates.{u, uP} Γ}

/-- Forward half of the midpoint-reflection criterion.  If the endpoint
matching equation holds, then the mate in the middle fiber cannot be fixed by
the midpoint reflection; otherwise the three vertices form a triangle. -/
theorem midpoint_matching_eq_reflection_imp_midpoint_mate_moved
    {k : ZMod 19} {sigma : ZMod 19 → ZMod 19}
    (ref : AFiberReflectionEquivariance h coords k sigma)
    (m : ZMod 19) (hm : m ≠ 0)
    (hsigma0 : sigma 0 = 0 + (m + m))
    (hsigmam : sigma (0 + m) = 0 + m)
    (p : coords.P) :
    AFiberCoordinates.matchingEquiv h.isMoore coords
        0 (0 + (m + m))
        (index_ne_add_of_ne_zero (add_self_ne_zero_zmod19 hm)) p =
      ref.coordPerm 0 p →
    ref.coordPerm (0 + m)
        (AFiberCoordinates.matchingEquiv h.isMoore coords
          0 (0 + m) (index_ne_add_of_ne_zero hm) p) ≠
      AFiberCoordinates.matchingEquiv h.isMoore coords
        0 (0 + m) (index_ne_add_of_ne_zero hm) p := by
  intro hmatch hfixed
  let q : coords.P :=
    AFiberCoordinates.matchingEquiv h.isMoore coords
      0 (0 + m) (index_ne_add_of_ne_zero hm) p
  let x : V :=
    ((coords.coord 0 p :
      {x : V // x ∈ branchFiber Γ coords.u (coords.a 0)}) : V)
  let z : V :=
    ((coords.coord (0 + m) q :
      {x : V // x ∈ branchFiber Γ coords.u (coords.a (0 + m))}) : V)
  let y : V :=
    ((coords.coord (0 + (m + m)) (ref.coordPerm 0 p) :
      {x : V // x ∈ branchFiber Γ coords.u (coords.a (0 + (m + m)))}) : V)
  have hxz : Γ.Adj x z := by
    simpa [x, z, q] using
      AFiberCoordinates.adj_coord_matchingEquiv
        h.isMoore coords (index_ne_add_of_ne_zero hm) p
  have hxy : Γ.Adj x y := by
    exact
      (AFiberCoordinates.adj_iff_matchingEquiv_eq
        h.isMoore coords
        (index_ne_add_of_ne_zero (add_self_ne_zero_zmod19 hm))
        p (ref.coordPerm 0 p)).2 (by
          simpa [q] using hmatch)
  have hx_ref : h.smul (DihedralGroup.sr k) x = y := by
    have hx_raw :
        h.smul (DihedralGroup.sr k)
            (((coords.coord 0 p :
              {x : V // x ∈ branchFiber Γ coords.u (coords.a 0)}) : V)) =
          ((coords.coord (sigma 0) (ref.coordPerm 0 p) :
            {x : V // x ∈ branchFiber Γ coords.u (coords.a (sigma 0))}) : V) :=
      (AFiberReflectionEquivariance.coord_coordPerm_apply_val
        (ref := ref) (i := 0) (p := p)).symm
    rw [hsigma0] at hx_raw
    simpa only [x, y] using hx_raw
  have hz_ref : h.smul (DihedralGroup.sr k) z = z := by
    have hz_raw :
        h.smul (DihedralGroup.sr k)
            (((coords.coord (0 + m) q :
              {x : V // x ∈ branchFiber Γ coords.u (coords.a (0 + m))}) : V)) =
          ((coords.coord (sigma (0 + m)) (ref.coordPerm (0 + m) q) :
            {x : V // x ∈ branchFiber Γ coords.u (coords.a (sigma (0 + m)))}) : V) :=
      (AFiberReflectionEquivariance.coord_coordPerm_apply_val
        (ref := ref) (i := 0 + m) (p := q)).symm
    rw [hsigmam] at hz_raw
    rw [hfixed] at hz_raw
    simpa only [z] using hz_raw
  have hyz : Γ.Adj y z := by
    have hAdj := (h.smul_adj (DihedralGroup.sr k) x z).mp hxz
    simpa [hx_ref, hz_ref] using hAdj
  exact h.isMoore.no_triangle hxy hyz hxz.symm

/-- Support-set spelling of
`midpoint_matching_eq_reflection_imp_midpoint_mate_moved`. -/
theorem midpoint_matching_eq_reflection_imp_midpoint_mate_mem_support
    [DecidableEq coords.P] [Fintype coords.P]
    {k : ZMod 19} {sigma : ZMod 19 → ZMod 19}
    (ref : AFiberReflectionEquivariance h coords k sigma)
    (m : ZMod 19) (hm : m ≠ 0)
    (hsigma0 : sigma 0 = 0 + (m + m))
    (hsigmam : sigma (0 + m) = 0 + m)
    (p : coords.P) :
    AFiberCoordinates.matchingEquiv h.isMoore coords
        0 (0 + (m + m))
        (index_ne_add_of_ne_zero (add_self_ne_zero_zmod19 hm)) p =
      ref.coordPerm 0 p →
    AFiberCoordinates.matchingEquiv h.isMoore coords
        0 (0 + m) (index_ne_add_of_ne_zero hm) p ∈
      ref.supportAt (0 + m) := by
  intro hmatch
  exact (Equiv.Perm.mem_support).mpr
    (ref.midpoint_matching_eq_reflection_imp_midpoint_mate_moved
      m hm hsigma0 hsigmam p hmatch)

end AFiberReflectionEquivariance

end Moore57
