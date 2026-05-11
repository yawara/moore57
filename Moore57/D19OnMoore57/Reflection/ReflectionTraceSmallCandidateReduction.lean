import Moore57.D19OnMoore57.Reflection.ReflectionRegularSmallCandidateExclusion
import Moore57.D19OnMoore57.Reflection.ReflectionTraceIntegrality
import Moore57.D19OnMoore57.Involution.InvolutionHigmanCountArithmetic
import Moore57.D19OnMoore57.Reflection.ReflectionRegularBranchExclusion

/-!
# Trace reduction of small reflection candidates

The raw regular branch leaves the candidate fixed counts `2` and `10`.  E7
trace integrality rules out the `2` case through Higman's edge congruence.
-/

namespace Moore57

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

namespace D19ActsOnMoore57

variable {h : D19ActsOnMoore57 V Γ}

/-- The regular reflection candidate with two fixed vertices is incompatible
with automatic E7 trace integrality. -/
theorem reflection_regular_fixedVertexCount_ne_two
    (k : ZMod 19)
    (hregular :
      ∃ d : ℕ,
        ∀ x : fixedVertexSet (h.smulEquiv (DihedralGroup.sr k)),
          (h.fixedInducedGraph (DihedralGroup.sr k)).degree x = d) :
    fixedVertexCount (h.smulEquiv (DihedralGroup.sr k)) ≠ 2 := by
  rintro hcount
  rcases hregular with ⟨d, hreg⟩
  have hcount_degree :
      fixedVertexCount (h.smulEquiv (DihedralGroup.sr k)) = d * d + 1 :=
    h.reflection_regular_fixedVertexCount_eq_degree_sq_add_one k d hreg
  have hd : d = 1 := by
    rw [hcount] at hcount_degree
    nlinarith
  obtain ⟨z, htrace⟩ :=
    h.exists_int_E7Matrix_mul_permMatrix_reflection_trace k
  have hformula :
      (adjacentMovedCount Γ (h.smulEquiv (DihedralGroup.sr k)) : ℤ) =
        3250 -
          58 * (fixedVertexCount (h.smulEquiv (DihedralGroup.sr k)) : ℤ) +
            2 * ((h.fixedInducedGraph (DihedralGroup.sr k)).edgeFinset.card : ℤ) :=
    adjacentMovedCount_eq_involution_fixed_edge_formula
      (Γ := Γ) h.isMoore
      (h.reflection_smulEquiv_involutive k)
      (h.reflection_smulEquiv_automorphism k)
  have hmod :
      2 * ((h.fixedInducedGraph (DihedralGroup.sr k)).edgeFinset.card : ℤ) ≡
        5 * (fixedVertexCount (h.smulEquiv (DihedralGroup.sr k)) : ℤ) - 5
          [ZMOD 15] :=
    h.isMoore.edgeCountFormula_twice_edges_intModEq
      (h.smulEquiv (DihedralGroup.sr k)) htrace hformula
  have hedge_nat :=
    h.fixedInducedGraph_twice_card_edgeFinset_eq_fixedVertexCount_mul_degree
      (DihedralGroup.sr k) d hreg
  have hedge_int :
      2 * ((h.fixedInducedGraph (DihedralGroup.sr k)).edgeFinset.card : ℤ) =
        (fixedVertexCount (h.smulEquiv (DihedralGroup.sr k)) : ℤ) * (d : ℤ) := by
    exact_mod_cast hedge_nat
  have hedge_two :
      2 * ((h.fixedInducedGraph (DihedralGroup.sr k)).edgeFinset.card : ℤ) = 2 := by
    rw [hedge_int, hcount, hd]
    norm_num
  have hbad : (2 : ℤ) ≡ 5 [ZMOD 15] := by
    simpa [hedge_two, hcount] using hmod
  norm_num [Int.ModEq] at hbad

/-- Regular reflections can only have fixed count `10`. -/
theorem fixedVertexCount_reflection_regular_eq_ten
    (k : ZMod 19)
    (hregular :
      ∃ d : ℕ,
        ∀ x : fixedVertexSet (h.smulEquiv (DihedralGroup.sr k)),
          (h.fixedInducedGraph (DihedralGroup.sr k)).degree x = d) :
    fixedVertexCount (h.smulEquiv (DihedralGroup.sr k)) = 10 := by
  rcases h.fixedVertexCount_reflection_regular_candidates k hregular with htwo | hten
  · exact False.elim (h.reflection_regular_fixedVertexCount_ne_two k hregular htwo)
  · exact hten

/-- Trace-integrality-refined raw reflection fixed-count candidates. -/
theorem fixedVertexCount_reflection_trace_refined_raw_candidates
    (k : ZMod 19) :
    fixedVertexCount (h.smulEquiv (DihedralGroup.sr k)) = 6 ∨
    fixedVertexCount (h.smulEquiv (DihedralGroup.sr k)) = 10 ∨
    fixedVertexCount (h.smulEquiv (DihedralGroup.sr k)) = 16 ∨
    fixedVertexCount (h.smulEquiv (DihedralGroup.sr k)) = 26 ∨
    fixedVertexCount (h.smulEquiv (DihedralGroup.sr k)) = 36 ∨
    fixedVertexCount (h.smulEquiv (DihedralGroup.sr k)) = 46 ∨
    fixedVertexCount (h.smulEquiv (DihedralGroup.sr k)) = 56 := by
  rcases h.fixedVertexCount_reflection_raw_candidates k with
      h2 | h6 | h10 | h16 | h26 | h36 | h46 | h56
  · by_cases hregular :
      ∃ d : ℕ,
        ∀ x : fixedVertexSet (h.smulEquiv (DihedralGroup.sr k)),
          (h.fixedInducedGraph (DihedralGroup.sr k)).degree x = d
    · exact False.elim (h.reflection_regular_fixedVertexCount_ne_two k hregular h2)
    · have hstrong := h.fixedInducedGraph_isStrongZeroOne (DihedralGroup.sr k)
      rcases hstrong.exists_isStarWithCenter_of_not_regular hregular with
        ⟨c, hstar⟩
      have hcandidates :=
        h.fixedVertexCount_reflection_star_candidates_of_fixedInduced_isStarWithCenter
          k hstar
      omega
  · exact Or.inl h6
  · exact Or.inr (Or.inl h10)
  · exact Or.inr (Or.inr (Or.inl h16))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h26)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h36))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h46)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h56)))))

end D19ActsOnMoore57

end

end Moore57
