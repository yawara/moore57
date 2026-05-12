import Moore57.D19OnMoore57.Reflection.RemainingCandidateGeometryBoundary
import Moore57.D19OnMoore57.Reflection.RegularBranchExclusion
import Mathlib.Tactic

/-!
# Arithmetic consequences of the regular-10 reflection branch

This file keeps the regular-`10` branch consequences local: from the
all-center-neighbor-orbits-preserved boundary it derives the fixed count,
regular fixed-induced degree, fixed-induced edge count, adjacent-moved count,
and the resulting Higman trace value.
-/

namespace Moore57

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

namespace ReflectionRegularTenAllCenterNeighborOrbitsPreserved

variable {h : D19ActsOnMoore57 V Γ} {k : ZMod 19}

/-- Projection of the fixed-count field from the regular-`10` branch. -/
theorem fixedVertexCount_eq_ten
    (hreg : ReflectionRegularTenAllCenterNeighborOrbitsPreserved h k) :
    fixedVertexCount (h.smulEquiv (DihedralGroup.sr k)) = 10 :=
  hreg.1

/-- Projection of the center-degree field from the regular-`10` branch. -/
theorem fixedInducedGraph_rotationFixedCenter_degree_eq_three
    (hreg : ReflectionRegularTenAllCenterNeighborOrbitsPreserved h k) :
    (h.fixedInducedGraph (DihedralGroup.sr k)).degree
        (D19ActsOnMoore57.reflectionRotationFixedCenter h k) = 3 := by
  rcases hreg with
    ⟨_hcount, _base, _base_adj, _base_pairwise_disjoint, _base_cover,
      hdegree, _hneighbors, _hpreserved, _hcards⟩
  exact hdegree

/-- The regular-`10` branch makes the full fixed-induced graph cubic. -/
theorem fixedInducedGraph_degree_eq_three
    (hreg : ReflectionRegularTenAllCenterNeighborOrbitsPreserved h k)
    (x : fixedVertexSet (h.smulEquiv (DihedralGroup.sr k))) :
    (h.fixedInducedGraph (DihedralGroup.sr k)).degree x = 3 := by
  classical
  let Gfix := h.fixedInducedGraph (DihedralGroup.sr k)
  let c : fixedVertexSet (h.smulEquiv (DihedralGroup.sr k)) :=
    D19ActsOnMoore57.reflectionRotationFixedCenter h k
  have hcdeg : Gfix.degree c = 3 := by
    simpa [Gfix, c] using
      hreg.fixedInducedGraph_rotationFixedCenter_degree_eq_three
  by_contra hxdeg_ne
  have hnotRegular :
      ¬ ∃ d : ℕ,
        ∀ y : fixedVertexSet (h.smulEquiv (DihedralGroup.sr k)),
          (h.fixedInducedGraph (DihedralGroup.sr k)).degree y = d := by
    rintro ⟨d, hd⟩
    have hxd : Gfix.degree x = d := by simpa [Gfix] using hd x
    have hcd : Gfix.degree c = d := by simpa [Gfix, c] using hd c
    exact hxdeg_ne (hxd.trans hcd.symm |>.trans hcdeg)
  have hstrong := h.fixedInducedGraph_isStrongZeroOne (DihedralGroup.sr k)
  rcases hstrong.exists_isStarWithCenter_of_not_regular hnotRegular with
    ⟨s, hstar⟩
  have hcard : Fintype.card (fixedVertexSet (h.smulEquiv (DihedralGroup.sr k))) = 10 := by
    simpa [fixedVertexCount_eq_card_fixedVertexSet] using hreg.fixedVertexCount_eq_ten
  by_cases hcs : c = s
  · have hcstar : Gfix.degree c = 9 := by
      rw [hcs]
      calc
        Gfix.degree s = Fintype.card (fixedVertexSet (h.smulEquiv (DihedralGroup.sr k))) - 1 := by
          simpa [Gfix] using hstar.degree_center_eq_card_sub_one
        _ = 9 := by omega
    omega
  · have hcstar : Gfix.degree c = 1 := by
      simpa [Gfix] using hstar.degree_noncenter_eq_one hcs
    omega

/-- Constant-degree regularity form of the regular-`10` branch. -/
theorem fixedInducedGraph_regular_degree_three
    (hreg : ReflectionRegularTenAllCenterNeighborOrbitsPreserved h k) :
    ∀ x : fixedVertexSet (h.smulEquiv (DihedralGroup.sr k)),
      (h.fixedInducedGraph (DihedralGroup.sr k)).degree x = 3 :=
  hreg.fixedInducedGraph_degree_eq_three

/-- The fixed-induced graph has fifteen edges in the regular-`10` branch. -/
theorem fixedInducedGraph_edgeFinset_card_eq_fifteen
    (hreg : ReflectionRegularTenAllCenterNeighborOrbitsPreserved h k) :
    (h.fixedInducedGraph (DihedralGroup.sr k)).edgeFinset.card = 15 := by
  have htwice :=
    h.fixedInducedGraph_twice_card_edgeFinset_eq_fixedVertexCount_mul_degree
      (DihedralGroup.sr k) 3 hreg.fixedInducedGraph_regular_degree_three
  rw [hreg.fixedVertexCount_eq_ten] at htwice
  omega

/-- The regular-`10` branch gives adjacent-moved count `2700`. -/
theorem adjacentMovedCount_eq_2700
    (hreg : ReflectionRegularTenAllCenterNeighborOrbitsPreserved h k) :
    adjacentMovedCount Γ (h.smulEquiv (DihedralGroup.sr k)) = 2700 := by
  have hformula :
      (adjacentMovedCount Γ (h.smulEquiv (DihedralGroup.sr k)) : ℤ) =
        3250 -
          58 * (fixedVertexCount (h.smulEquiv (DihedralGroup.sr k)) : ℤ) +
            2 * ((h.fixedInducedGraph (DihedralGroup.sr k)).edgeFinset.card : ℤ) :=
    adjacentMovedCount_eq_involution_fixed_edge_formula
      (Γ := Γ) h.isMoore
      (h.reflection_smulEquiv_involutive k)
      (h.reflection_smulEquiv_automorphism k)
  rw [hreg.fixedVertexCount_eq_ten,
    hreg.fixedInducedGraph_edgeFinset_card_eq_fifteen] at hformula
  norm_num at hformula
  exact_mod_cast hformula

/-- Higman's trace formula evaluates to `181` on the regular-`10` branch. -/
theorem trace_E7Matrix_mul_permMatrix_eq_181
    (hreg : ReflectionRegularTenAllCenterNeighborOrbitsPreserved h k) :
    Matrix.trace (E7Matrix Γ * permMatrix (h.smulEquiv (DihedralGroup.sr k))) =
      (181 : ℚ) := by
  rw [h.isMoore.higman_trace_formula,
    hreg.fixedVertexCount_eq_ten,
    hreg.adjacentMovedCount_eq_2700]
  norm_num

end ReflectionRegularTenAllCenterNeighborOrbitsPreserved

namespace D19ActsOnMoore57

variable {h : D19ActsOnMoore57 V Γ}

/-- D19 namespace wrapper for the regular-`10` fixed count. -/
theorem reflectionRegularTen_fixedVertexCount_eq_ten
    (k : ZMod 19)
    (hreg : ReflectionRegularTenAllCenterNeighborOrbitsPreserved h k) :
    fixedVertexCount (h.smulEquiv (DihedralGroup.sr k)) = 10 :=
  hreg.fixedVertexCount_eq_ten

/-- D19 namespace wrapper for cubic regularity of the fixed-induced graph. -/
theorem reflectionRegularTen_fixedInducedGraph_degree_eq_three
    (k : ZMod 19)
    (hreg : ReflectionRegularTenAllCenterNeighborOrbitsPreserved h k)
    (x : fixedVertexSet (h.smulEquiv (DihedralGroup.sr k))) :
    (h.fixedInducedGraph (DihedralGroup.sr k)).degree x = 3 :=
  hreg.fixedInducedGraph_degree_eq_three x

/-- D19 namespace wrapper for the fixed-induced edge count. -/
theorem reflectionRegularTen_fixedInducedGraph_edgeFinset_card_eq_fifteen
    (k : ZMod 19)
    (hreg : ReflectionRegularTenAllCenterNeighborOrbitsPreserved h k) :
    (h.fixedInducedGraph (DihedralGroup.sr k)).edgeFinset.card = 15 :=
  hreg.fixedInducedGraph_edgeFinset_card_eq_fifteen

/-- D19 namespace wrapper for the adjacent-moved count. -/
theorem reflectionRegularTen_adjacentMovedCount_eq_2700
    (k : ZMod 19)
    (hreg : ReflectionRegularTenAllCenterNeighborOrbitsPreserved h k) :
    adjacentMovedCount Γ (h.smulEquiv (DihedralGroup.sr k)) = 2700 :=
  hreg.adjacentMovedCount_eq_2700

/-- D19 namespace wrapper for the Higman trace value. -/
theorem reflectionRegularTen_trace_E7Matrix_mul_permMatrix_eq_181
    (k : ZMod 19)
    (hreg : ReflectionRegularTenAllCenterNeighborOrbitsPreserved h k) :
    Matrix.trace (E7Matrix Γ * permMatrix (h.smulEquiv (DihedralGroup.sr k))) =
      (181 : ℚ) :=
  hreg.trace_E7Matrix_mul_permMatrix_eq_181

end D19ActsOnMoore57

end

end Moore57
