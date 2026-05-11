import Moore57.AFiberCoordinateReflection
import Moore57.AFiberCoordinateRotation
import Moore57.AFiberMatchingPermAdjacency
import Moore57.FixedCommonNeighbors
import Moore57.Foundations.ZMod19.Lemmas

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

/-- Reverse half of the midpoint-reflection criterion, with the genuinely
geometric step isolated as `hfixedCommon_mem_middle`.  If every fixed common
neighbor of the reflected endpoint pair lies in the middle A-fiber, then a
moved midpoint mate forces the endpoint matching equation. -/
theorem midpoint_mate_moved_imp_matching_eq_reflection_of_fixedCommon_mem_middle
    {k : ZMod 19} {sigma : ZMod 19 → ZMod 19}
    (ref : AFiberReflectionEquivariance h coords k sigma)
    (m : ZMod 19) (hm : m ≠ 0)
    (hsigma0 : sigma 0 = 0 + (m + m))
    (hsigmam : sigma (0 + m) = 0 + m)
    (hfixedCommon_mem_middle :
      ∀ p : coords.P, ∀ {w : V},
        h.smul (DihedralGroup.sr k) w = w →
        Γ.Adj
          (((coords.coord 0 p :
            {x : V // x ∈ branchFiber Γ coords.u (coords.a 0)}) : V)) w →
        Γ.Adj
          (((coords.coord (0 + (m + m)) (ref.coordPerm 0 p) :
            {x : V // x ∈
              branchFiber Γ coords.u (coords.a (0 + (m + m)))}) : V)) w →
        w ∈ coords.fiber (0 + m))
    (p : coords.P) :
    ref.coordPerm (0 + m)
        (AFiberCoordinates.matchingEquiv h.isMoore coords
          0 (0 + m) (index_ne_add_of_ne_zero hm) p) ≠
      AFiberCoordinates.matchingEquiv h.isMoore coords
        0 (0 + m) (index_ne_add_of_ne_zero hm) p →
    AFiberCoordinates.matchingEquiv h.isMoore coords
        0 (0 + (m + m))
        (index_ne_add_of_ne_zero (add_self_ne_zero_zmod19 hm)) p =
      ref.coordPerm 0 p := by
  intro hmove
  by_contra hnot
  let q : coords.P :=
    AFiberCoordinates.matchingEquiv h.isMoore coords
      0 (0 + m) (index_ne_add_of_ne_zero hm) p
  let x : V :=
    ((coords.coord 0 p :
      {x : V // x ∈ branchFiber Γ coords.u (coords.a 0)}) : V)
  let y : V :=
    ((coords.coord (0 + (m + m)) (ref.coordPerm 0 p) :
      {x : V // x ∈ branchFiber Γ coords.u (coords.a (0 + (m + m)))}) : V)
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
  have hy_ref : h.smul (DihedralGroup.sr k) y = x := by
    rw [← hx_ref]
    calc
      h.smul (DihedralGroup.sr k) (h.smul (DihedralGroup.sr k) x) =
          h.smul (DihedralGroup.sr k * DihedralGroup.sr k) x := by
            rw [← h.mul_smul]
      _ = h.smul 1 x := by
            rw [DihedralGroup.sr_mul_self]
      _ = x := h.one_smul x
  have hxy_ne : x ≠ y := by
    intro hxy_eq
    have hxmem :
        x ∈ branchFiber Γ coords.u (coords.a 0) := by
      exact coords.coord_mem 0 p
    have hyadj :
        Γ.Adj x (coords.a (0 + (m + m))) := by
      have hymem :
          y ∈ branchFiber Γ coords.u (coords.a (0 + (m + m))) := by
        simpa [y] using coords.coord_mem (0 + (m + m)) (ref.coordPerm 0 p)
      have hy_branch : Γ.Adj (coords.a (0 + (m + m))) y :=
        (mem_branchFiber.mp hymem).2
      simpa [hxy_eq] using hy_branch.symm
    exact
      (h.isMoore.not_adj_other_branch_of_mem_branchFiber
        (coords.hub 0) (coords.hub (0 + (m + m)))
        (coords.a_ne
          (index_ne_add_of_ne_zero (add_self_ne_zero_zmod19 hm)))
        hxmem) hyadj
  have hxy_not : ¬ Γ.Adj x y := by
    intro hxy
    exact hnot
      ((AFiberCoordinates.adj_iff_matchingEquiv_eq
        h.isMoore coords
        (index_ne_add_of_ne_zero (add_self_ne_zero_zmod19 hm))
        p (ref.coordPerm 0 p)).1 (by
          simpa [x, y] using hxy))
  rcases h.exists_fixed_commonNeighbor_of_swap_not_adj
      (DihedralGroup.sr k) hx_ref hy_ref hxy_ne hxy_not with
    ⟨w, hwfix, hxw, hyw⟩
  have hwmem : w ∈ coords.fiber (0 + m) :=
    hfixedCommon_mem_middle p hwfix hxw hyw
  let qw : coords.P := (coords.coord (0 + m)).symm ⟨w, hwmem⟩
  have hq : q = qw := by
    have hxw_coord :
        Γ.Adj
          (((coords.coord 0 p :
            {x : V // x ∈ branchFiber Γ coords.u (coords.a 0)}) : V))
          (((coords.coord (0 + m) qw :
            {x : V // x ∈ branchFiber Γ coords.u (coords.a (0 + m))}) : V)) := by
      simpa [qw] using hxw
    change
      AFiberCoordinates.matchingEquiv h.isMoore coords
          0 (0 + m) (index_ne_add_of_ne_zero hm) p = qw
    exact
      AFiberCoordinates.matchingEquiv_eq_of_adj
        h.isMoore coords (index_ne_add_of_ne_zero hm)
        (p := p) (q := qw) hxw_coord
  have hfixed_q : ref.coordPerm (0 + m) q = q := by
    apply
      (AFiberReflectionEquivariance.coordPerm_eq_iff
        (ref := ref) (i := 0 + m) q q).2
    rw [hsigmam]
    rw [hq]
    simpa [qw] using hwfix
  exact hmove hfixed_q

/-- Support-set spelling of
`midpoint_mate_moved_imp_matching_eq_reflection_of_fixedCommon_mem_middle`. -/
theorem midpoint_mate_mem_support_imp_matching_eq_reflection_of_fixedCommon_mem_middle
    [DecidableEq coords.P] [Fintype coords.P]
    {k : ZMod 19} {sigma : ZMod 19 → ZMod 19}
    (ref : AFiberReflectionEquivariance h coords k sigma)
    (m : ZMod 19) (hm : m ≠ 0)
    (hsigma0 : sigma 0 = 0 + (m + m))
    (hsigmam : sigma (0 + m) = 0 + m)
    (hfixedCommon_mem_middle :
      ∀ p : coords.P, ∀ {w : V},
        h.smul (DihedralGroup.sr k) w = w →
        Γ.Adj
          (((coords.coord 0 p :
            {x : V // x ∈ branchFiber Γ coords.u (coords.a 0)}) : V)) w →
        Γ.Adj
          (((coords.coord (0 + (m + m)) (ref.coordPerm 0 p) :
            {x : V // x ∈
              branchFiber Γ coords.u (coords.a (0 + (m + m)))}) : V)) w →
        w ∈ coords.fiber (0 + m))
    (p : coords.P) :
    AFiberCoordinates.matchingEquiv h.isMoore coords
        0 (0 + m) (index_ne_add_of_ne_zero hm) p ∈
      ref.supportAt (0 + m) →
    AFiberCoordinates.matchingEquiv h.isMoore coords
        0 (0 + (m + m))
        (index_ne_add_of_ne_zero (add_self_ne_zero_zmod19 hm)) p =
      ref.coordPerm 0 p := by
  intro hsupp
  exact
    ref.midpoint_mate_moved_imp_matching_eq_reflection_of_fixedCommon_mem_middle
      m hm hsigma0 hsigmam hfixedCommon_mem_middle p
      ((Equiv.Perm.mem_support).mp hsupp)

end AFiberReflectionEquivariance

end Moore57
