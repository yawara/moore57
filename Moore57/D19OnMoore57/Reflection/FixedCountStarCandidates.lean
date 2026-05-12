import Moore57.D19OnMoore57.Reflection.FixedCountBoundsBridge
import Moore57.D19OnMoore57.Fixed.InducedDegree

/-!
# Reflection fixed-count candidates for fixed-induced stars

This file records the coarse arithmetic output available from a raw reflection
whose fixed-induced graph is a star: the fixed-vertex count is one of
`6, 16, 26, 36, 46, 56`.
-/

namespace Moore57

noncomputable section

universe u

/-- Arithmetic classifier for the positive even natural numbers at most `58`
which are `1` modulo `5` after coercion to `ℤ`. -/
theorem fixed_count_candidates_of_pos_le_even_intModEq_five
    (n : ℕ) (hpos : 0 < n) (hle : n ≤ 58) (heven : 2 ∣ n)
    (hmod : (n : ℤ) ≡ 1 [ZMOD 5]) :
    n = 6 ∨ n = 16 ∨ n = 26 ∨ n = 36 ∨ n = 46 ∨ n = 56 := by
  rw [Int.modEq_iff_dvd] at hmod
  obtain ⟨p, hp⟩ := hmod
  obtain ⟨q, hq⟩ := heven
  omega

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

namespace D19ActsOnMoore57

/-- If the fixed-induced graph is a star, the center degree bounds the fixed
set by the ambient Moore degree plus one. -/
theorem fixedVertexCount_le_ambient_degree_add_one_of_fixedInduced_isStarWithCenter
    (h : D19ActsOnMoore57 V Γ) (g : DihedralGroup 19)
    {c : fixedVertexSet (h.smulEquiv g)}
    (hstar : IsStarWithCenter (h.fixedInducedGraph g) c) :
    fixedVertexCount (h.smulEquiv g) ≤ 58 := by
  classical
  have hcenter_degree :
      (h.fixedInducedGraph g).degree c =
        fixedVertexCount (h.smulEquiv g) - 1 := by
    have hstar_degree :=
      IsStarWithCenter.degree_center_eq_card_sub_one
        (G := h.fixedInducedGraph g) (c := c) hstar
    simpa [fixedVertexCount_eq_card_fixedVertexSet] using hstar_degree
  have hdegree_filter :
      (h.fixedInducedGraph g).degree c =
        ((Γ.neighborFinset (c : V)).filter fun w => h.smulEquiv g w = w).card :=
    h.fixedInducedGraph_degree_eq_fixedNeighborFinset_card g c
  have hfilter_le :
      ((Γ.neighborFinset (c : V)).filter fun w => h.smulEquiv g w = w).card ≤
        (Γ.neighborFinset (c : V)).card :=
    Finset.card_filter_le _ _
  have hdegree_le :
      (h.fixedInducedGraph g).degree c ≤ 57 := by
    rw [hdegree_filter]
    rw [SimpleGraph.card_neighborFinset_eq_degree,
      h.isMoore.regular.degree_eq (c : V)] at hfilter_le
    exact hfilter_le
  have hpos : 0 < fixedVertexCount (h.smulEquiv g) := by
    rw [fixedVertexCount_eq_card_fixedVertexSet]
    exact Fintype.card_pos_iff.mpr ⟨c⟩
  omega

/-- A raw reflection whose fixed-induced graph is a star has fixed-count
candidates `6, 16, 26, 36, 46, 56`. -/
theorem fixedVertexCount_reflection_star_candidates_of_fixedInduced_isStarWithCenter
    (h : D19ActsOnMoore57 V Γ) (k : ZMod 19)
    {c : fixedVertexSet (h.smulEquiv (DihedralGroup.sr k))}
    (hstar : IsStarWithCenter (h.fixedInducedGraph (DihedralGroup.sr k)) c) :
    fixedVertexCount (h.smulEquiv (DihedralGroup.sr k)) = 6 ∨
    fixedVertexCount (h.smulEquiv (DihedralGroup.sr k)) = 16 ∨
    fixedVertexCount (h.smulEquiv (DihedralGroup.sr k)) = 26 ∨
    fixedVertexCount (h.smulEquiv (DihedralGroup.sr k)) = 36 ∨
    fixedVertexCount (h.smulEquiv (DihedralGroup.sr k)) = 46 ∨
    fixedVertexCount (h.smulEquiv (DihedralGroup.sr k)) = 56 := by
  classical
  have hpos :
      0 < fixedVertexCount (h.smulEquiv (DihedralGroup.sr k)) := by
    rw [fixedVertexCount_eq_card_fixedVertexSet]
    exact Fintype.card_pos_iff.mpr ⟨c⟩
  have hle :
      fixedVertexCount (h.smulEquiv (DihedralGroup.sr k)) ≤ 58 :=
    h.fixedVertexCount_le_ambient_degree_add_one_of_fixedInduced_isStarWithCenter
      (DihedralGroup.sr k) hstar
  have heven :
      2 ∣ fixedVertexCount (h.smulEquiv (DihedralGroup.sr k)) := by
    have hsupport_even :
        2 ∣
          Fintype.card V -
            fixedVertexCount (h.smulEquiv (DihedralGroup.sr k)) :=
      two_dvd_card_sub_fixedVertexCount_of_involutive
        (h.smulEquiv (DihedralGroup.sr k))
        (h.reflection_smulEquiv_involutive k)
    obtain ⟨q, hq⟩ := hsupport_even
    refine ⟨1625 - q, ?_⟩
    have hcard : Fintype.card V = 3250 := h.isMoore.card
    rw [hcard] at hq
    omega
  have hformula_edge :
      (adjacentMovedCount Γ (h.smulEquiv (DihedralGroup.sr k)) : ℤ) =
        3250 -
          58 * (fixedVertexCount (h.smulEquiv (DihedralGroup.sr k)) : ℤ) +
            2 * ((h.fixedInducedGraph (DihedralGroup.sr k)).edgeFinset.card : ℤ) :=
    adjacentMovedCount_eq_involution_fixed_edge_formula
      (Γ := Γ) h.isMoore
      (h.reflection_smulEquiv_involutive k)
      (h.reflection_smulEquiv_automorphism k)
  have hformula_star :
      (adjacentMovedCount Γ (h.smulEquiv (DihedralGroup.sr k)) : ℤ) =
        3250 -
          58 * (fixedVertexCount (h.smulEquiv (DihedralGroup.sr k)) : ℤ) +
            2 * ((fixedVertexCount (h.smulEquiv (DihedralGroup.sr k)) : ℤ) - 1) :=
    h.reflection_starEdgeCountFormula_of_fixedInduced_isStarWithCenter
      k hstar hformula_edge
  obtain ⟨z, htrace⟩ :=
    h.exists_int_E7Matrix_mul_permMatrix_reflection_trace k
  have hmod :
      (fixedVertexCount (h.smulEquiv (DihedralGroup.sr k)) : ℤ) ≡ 1
        [ZMOD 5] :=
    h.isMoore.starEdgeCountFormula_fixedVertexCount_intModEq_five
      (h.smulEquiv (DihedralGroup.sr k)) htrace hformula_star
  exact
    fixed_count_candidates_of_pos_le_even_intModEq_five
      (fixedVertexCount (h.smulEquiv (DihedralGroup.sr k)))
      hpos hle heven hmod

/-- Cameron/Higman Step 4 in the reflection-star branch: a `58`-point
reflection fixed star is incompatible with the E7 trace integrality
constraints. -/
theorem fixedVertexCount_reflection_ne_fiftyEight_of_fixedInduced_isStarWithCenter
    (h : D19ActsOnMoore57 V Γ) (k : ZMod 19)
    {c : fixedVertexSet (h.smulEquiv (DihedralGroup.sr k))}
    (hstar : IsStarWithCenter (h.fixedInducedGraph (DihedralGroup.sr k)) c) :
    fixedVertexCount (h.smulEquiv (DihedralGroup.sr k)) ≠ 58 := by
  intro h58
  rcases h.fixedVertexCount_reflection_star_candidates_of_fixedInduced_isStarWithCenter
      k hstar with h6 | h16 | h26 | h36 | h46 | h56 <;> omega

/-- In the reflection-star branch, the practical lower bound `47` already
forces Cameron/Higman's `56`-point fixed star count. -/
theorem fixedVertexCount_reflection_eq_56_of_fixedInduced_isStarWithCenter_ge_fortySeven
    (h : D19ActsOnMoore57 V Γ) (k : ZMod 19)
    {c : fixedVertexSet (h.smulEquiv (DihedralGroup.sr k))}
    (hstar : IsStarWithCenter (h.fixedInducedGraph (DihedralGroup.sr k)) c)
    (hlower : 47 ≤ fixedVertexCount (h.smulEquiv (DihedralGroup.sr k))) :
    fixedVertexCount (h.smulEquiv (DihedralGroup.sr k)) = 56 := by
  rcases h.fixedVertexCount_reflection_star_candidates_of_fixedInduced_isStarWithCenter
      k hstar with h6 | h16 | h26 | h36 | h46 | h56 <;> omega

end D19ActsOnMoore57

end

end Moore57
