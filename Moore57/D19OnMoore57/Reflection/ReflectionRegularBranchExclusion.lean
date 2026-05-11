import Moore57.D19OnMoore57.Fixed.FixedInducedDegree
import Moore57.D19OnMoore57.Fixed.FixedInducedStarEdgeFormula
import Moore57.Moore57Graph.InvolutionEdgeCountFormula
import Mathlib.Tactic

/-!
# Reflection regular branch exclusion

This file isolates the regular fixed-induced branch for a reflection.  Under
the packaged D19 linear-character input, the raw involution edge formula and
the strongly-regular parameter equation force a cubic in the constant
fixed-induced degree.  The relevant degree range has no integer root.
-/

namespace Moore57

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

namespace D19ActsOnMoore57

variable {h : D19ActsOnMoore57 V Γ}

/-- The full reflection character value `33` rewrites Higman's trace formula
as a direct adjacent-moved count formula. -/
theorem D19LinearCharacterInput.reflection_adjacentMovedCount_int_eq
    (hin : D19LinearCharacterInput h) (k : ZMod 19) :
    (adjacentMovedCount Γ (h.smulEquiv (DihedralGroup.sr k)) : ℤ) =
      560 - 8 * (fixedVertexCount (h.smulEquiv (DihedralGroup.sr k)) : ℤ) := by
  have htrace := hin.linear_character (DihedralGroup.sr k)
  rw [h.isMoore.higman_trace_formula, d19LinearCharacter_reflection] at htrace
  have hreflectionℚ :
      (((hin.multiplicity.alpha : ℤ) - (hin.multiplicity.beta : ℤ) : ℤ) : ℚ) =
        33 := by
    exact_mod_cast hin.multiplicity.reflection
  rw [hreflectionℚ] at htrace
  have hcountℚ :
      (adjacentMovedCount Γ (h.smulEquiv (DihedralGroup.sr k)) : ℚ) =
        560 - 8 * (fixedVertexCount (h.smulEquiv (DihedralGroup.sr k)) : ℚ) := by
    linarith
  exact_mod_cast hcountℚ

/-- A constant-degree fixed-induced graph has the expected degree-sum edge
count. -/
theorem fixedInducedGraph_twice_card_edgeFinset_eq_fixedVertexCount_mul_degree
    (h : D19ActsOnMoore57 V Γ) (g : DihedralGroup 19) (d : ℕ)
    (hreg :
      ∀ x : fixedVertexSet (h.smulEquiv g),
        (h.fixedInducedGraph g).degree x = d) :
    2 * (h.fixedInducedGraph g).edgeFinset.card =
      fixedVertexCount (h.smulEquiv g) * d := by
  have hsum := SimpleGraph.sum_degrees_eq_twice_card_edges (h.fixedInducedGraph g)
  have hsum_const :
      (∑ x : fixedVertexSet (h.smulEquiv g),
          (h.fixedInducedGraph g).degree x) =
        Fintype.card (fixedVertexSet (h.smulEquiv g)) * d := by
    simp [hreg]
  calc
    2 * (h.fixedInducedGraph g).edgeFinset.card
        = ∑ x : fixedVertexSet (h.smulEquiv g),
            (h.fixedInducedGraph g).degree x := by
          exact hsum.symm
    _ = fixedVertexCount (h.smulEquiv g) * d := by
          simpa [fixedVertexCount_eq_card_fixedVertexSet] using hsum_const

/-- Regularity converts the raw involution edge formula into an equation in
the fixed count and the constant fixed-induced degree. -/
theorem D19LinearCharacterInput.reflection_regular_edge_formula
    (_hin : D19LinearCharacterInput h) (k : ZMod 19) (d : ℕ)
    (hreg :
      ∀ x : fixedVertexSet (h.smulEquiv (DihedralGroup.sr k)),
        (h.fixedInducedGraph (DihedralGroup.sr k)).degree x = d) :
    (adjacentMovedCount Γ (h.smulEquiv (DihedralGroup.sr k)) : ℤ) =
      3250 -
        58 * (fixedVertexCount (h.smulEquiv (DihedralGroup.sr k)) : ℤ) +
          (fixedVertexCount (h.smulEquiv (DihedralGroup.sr k)) : ℤ) * (d : ℤ) := by
  have hformula :
      (adjacentMovedCount Γ (h.smulEquiv (DihedralGroup.sr k)) : ℤ) =
        3250 -
          58 * (fixedVertexCount (h.smulEquiv (DihedralGroup.sr k)) : ℤ) +
            2 * ((h.fixedInducedGraph (DihedralGroup.sr k)).edgeFinset.card : ℤ) :=
    adjacentMovedCount_eq_involution_fixed_edge_formula
      (Γ := Γ) h.isMoore
      (h.reflection_smulEquiv_involutive k)
      (h.reflection_smulEquiv_automorphism k)
  have hedge_nat :=
    h.fixedInducedGraph_twice_card_edgeFinset_eq_fixedVertexCount_mul_degree
      (DihedralGroup.sr k) d hreg
  have hedge_int :
      2 * ((h.fixedInducedGraph (DihedralGroup.sr k)).edgeFinset.card : ℤ) =
        (fixedVertexCount (h.smulEquiv (DihedralGroup.sr k)) : ℤ) * (d : ℤ) := by
    exact_mod_cast hedge_nat
  rw [hformula, hedge_int]

/-- Combining the reflection trace value with the regular edge formula gives
`a₀ * (50 - d) = 2690`. -/
theorem D19LinearCharacterInput.reflection_regular_fixedVertexCount_mul_eq
    (hin : D19LinearCharacterInput h) (k : ZMod 19) (d : ℕ)
    (hreg :
      ∀ x : fixedVertexSet (h.smulEquiv (DihedralGroup.sr k)),
        (h.fixedInducedGraph (DihedralGroup.sr k)).degree x = d) :
    (fixedVertexCount (h.smulEquiv (DihedralGroup.sr k)) : ℤ) *
        (50 - (d : ℤ)) =
      2690 := by
  have htrace := hin.reflection_adjacentMovedCount_int_eq k
  have hedge := hin.reflection_regular_edge_formula k d hreg
  rw [hedge] at htrace
  nlinarith

/-- A regular reflection fixed-induced graph has positive fixed count. -/
theorem D19LinearCharacterInput.reflection_regular_fixedVertexCount_pos
    (hin : D19LinearCharacterInput h) (k : ZMod 19) (d : ℕ)
    (hreg :
      ∀ x : fixedVertexSet (h.smulEquiv (DihedralGroup.sr k)),
        (h.fixedInducedGraph (DihedralGroup.sr k)).degree x = d) :
    0 < fixedVertexCount (h.smulEquiv (DihedralGroup.sr k)) := by
  have hmul := hin.reflection_regular_fixedVertexCount_mul_eq k d hreg
  by_contra hnot
  have hzero : fixedVertexCount (h.smulEquiv (DihedralGroup.sr k)) = 0 := by
    omega
  rw [hzero] at hmul
  norm_num at hmul

/-- The strongly-regular parameter equation gives `a₀ = d^2 + 1` for a
regular reflection fixed-induced graph. -/
theorem D19LinearCharacterInput.reflection_regular_fixedVertexCount_eq_degree_sq_add_one_int
    (hin : D19LinearCharacterInput h) (k : ZMod 19) (d : ℕ)
    (hreg :
      ∀ x : fixedVertexSet (h.smulEquiv (DihedralGroup.sr k)),
        (h.fixedInducedGraph (DihedralGroup.sr k)).degree x = d) :
    (fixedVertexCount (h.smulEquiv (DihedralGroup.sr k)) : ℤ) =
      (d : ℤ) * (d : ℤ) + 1 := by
  let Gfix := h.fixedInducedGraph (DihedralGroup.sr k)
  let n := fixedVertexCount (h.smulEquiv (DihedralGroup.sr k))
  have hsrg : Gfix.IsSRGWith n d 0 1 :=
    h.fixedInducedGraph_isSRGWith_of_regular (DihedralGroup.sr k) d hreg
  have hnpos : 0 < n :=
    hin.reflection_regular_fixedVertexCount_pos k d hreg
  have hparam := SimpleGraph.IsSRGWith.param_eq Gfix hsrg hnpos
  simp at hparam
  rw [show n = fixedVertexCount (h.smulEquiv (DihedralGroup.sr k)) from rfl] at hnpos
  rcases Fintype.card_pos_iff.mp (by
      simpa [fixedVertexCount_eq_card_fixedVertexSet] using hnpos) with ⟨x⟩
  have hd_lt_n : d < n := by
    have hdegree_lt := Gfix.degree_lt_card_verts x
    rw [hreg x] at hdegree_lt
    simpa [n, fixedVertexCount_eq_card_fixedVertexSet] using hdegree_lt
  by_cases hd0 : d = 0
  · subst d
    norm_num at hparam
    have hn_eq_one : n = 1 := by omega
    simp [n, hn_eq_one]
  · have hdpos : 1 ≤ d := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hd0)
    have hsub_pos : 1 ≤ n - d := by omega
    have hdle : d ≤ n := Nat.le_of_lt hd_lt_n
    have hparam_nat : d * (d - 1) = n - d - 1 := by
      simpa [Nat.sub_zero, Nat.mul_one] using hparam
    have hparam_int := congrArg (fun m : ℕ => (m : ℤ)) hparam_nat
    change ((d * (d - 1) : ℕ) : ℤ) = ((n - d - 1 : ℕ) : ℤ) at hparam_int
    rw [Nat.cast_mul, Nat.cast_sub hdpos, Nat.cast_sub hsub_pos,
      Nat.cast_sub hdle] at hparam_int
    norm_num at hparam_int
    have hn_int : (n : ℤ) = (d : ℤ) * (d : ℤ) + 1 := by
      nlinarith
    simpa [n] using hn_int

/-- The regular branch forces the cubic
`d^3 - 50 d^2 + d + 2640 = 0`. -/
theorem D19LinearCharacterInput.reflection_regular_fixedInduced_degree_cubic
    (hin : D19LinearCharacterInput h) (k : ZMod 19) (d : ℕ)
    (hreg :
      ∀ x : fixedVertexSet (h.smulEquiv (DihedralGroup.sr k)),
        (h.fixedInducedGraph (DihedralGroup.sr k)).degree x = d) :
    (d : ℤ) ^ 3 - 50 * (d : ℤ) ^ 2 + (d : ℤ) + 2640 = 0 := by
  have hmul := hin.reflection_regular_fixedVertexCount_mul_eq k d hreg
  have hn :=
    hin.reflection_regular_fixedVertexCount_eq_degree_sq_add_one_int k d hreg
  rw [hn] at hmul
  nlinarith

/-- A fixed-induced degree is bounded by the ambient Moore57 degree. -/
theorem fixedInducedGraph_reflection_regular_degree_le_ambient
    (hin : D19LinearCharacterInput h) (k : ZMod 19) (d : ℕ)
    (hreg :
      ∀ x : fixedVertexSet (h.smulEquiv (DihedralGroup.sr k)),
        (h.fixedInducedGraph (DihedralGroup.sr k)).degree x = d) :
    d ≤ 57 := by
  have hnpos := hin.reflection_regular_fixedVertexCount_pos k d hreg
  rcases Fintype.card_pos_iff.mp (by
      simpa [fixedVertexCount_eq_card_fixedVertexSet] using hnpos) with ⟨x⟩
  have hdeg := hreg x
  have hdegree_card :
      (h.fixedInducedGraph (DihedralGroup.sr k)).degree x =
        ((Γ.neighborFinset (x : V)).filter
          fun w => h.smulEquiv (DihedralGroup.sr k) w = w).card :=
    h.fixedInducedGraph_degree_eq_fixedNeighborFinset_card (DihedralGroup.sr k) x
  have hcard_le :
      ((Γ.neighborFinset (x : V)).filter
          fun w => h.smulEquiv (DihedralGroup.sr k) w = w).card ≤
        (Γ.neighborFinset (x : V)).card :=
    Finset.card_filter_le _ _
  rw [SimpleGraph.card_neighborFinset_eq_degree, h.isMoore.regular.degree_eq] at hcard_le
  omega

/-- The cubic has no roots in the only relevant degree range. -/
theorem reflection_regular_fixedInduced_cubic_no_relevant_nat_root
    (d : ℕ) (hd : d ≤ 57) :
    (d : ℤ) ^ 3 - 50 * (d : ℤ) ^ 2 + (d : ℤ) + 2640 ≠ 0 := by
  interval_cases d <;> norm_num

/-- Under `D19LinearCharacterInput`, the regular fixed-induced graph branch
for a reflection is impossible. -/
theorem D19LinearCharacterInput.reflection_fixedInducedGraph_not_regular
    (hin : D19LinearCharacterInput h) (k : ZMod 19) :
    ¬ ∃ d : ℕ,
      ∀ x : fixedVertexSet (h.smulEquiv (DihedralGroup.sr k)),
        (h.fixedInducedGraph (DihedralGroup.sr k)).degree x = d := by
  rintro ⟨d, hreg⟩
  exact reflection_regular_fixedInduced_cubic_no_relevant_nat_root d
    (fixedInducedGraph_reflection_regular_degree_le_ambient hin k d hreg)
    (hin.reflection_regular_fixedInduced_degree_cubic k d hreg)

/-- The full reflection character value `33`, together with a star-edge
formula, forces the reflection fixed count `56`. -/
theorem D19LinearCharacterInput.fixedVertexCount_reflection_eq_56_of_starEdgeCountFormula_local
    (hin : D19LinearCharacterInput h) (k : ZMod 19)
    (hformula :
      (adjacentMovedCount Γ (h.smulEquiv (DihedralGroup.sr k)) : ℤ) =
        3250 -
          58 * (fixedVertexCount (h.smulEquiv (DihedralGroup.sr k)) : ℤ) +
            2 * ((fixedVertexCount (h.smulEquiv (DihedralGroup.sr k)) : ℤ) - 1)) :
    fixedVertexCount (h.smulEquiv (DihedralGroup.sr k)) = 56 := by
  have htrace := hin.linear_character (DihedralGroup.sr k)
  rw [h.isMoore.higman_trace_formula, d19LinearCharacter_reflection] at htrace
  have hreflectionℚ :
      (((hin.multiplicity.alpha : ℤ) - (hin.multiplicity.beta : ℤ) : ℤ) : ℚ) =
        33 := by
    exact_mod_cast hin.multiplicity.reflection
  rw [hreflectionℚ] at htrace
  have hformulaℚ :
      (adjacentMovedCount Γ (h.smulEquiv (DihedralGroup.sr k)) : ℚ) =
        3250 -
          58 * (fixedVertexCount (h.smulEquiv (DihedralGroup.sr k)) : ℚ) +
            2 * ((fixedVertexCount (h.smulEquiv (DihedralGroup.sr k)) : ℚ) - 1) := by
    exact_mod_cast hformula
  rw [hformulaℚ] at htrace
  have hcountℚ :
      (fixedVertexCount (h.smulEquiv (DihedralGroup.sr k)) : ℚ) = 56 := by
    linarith
  exact_mod_cast hcountℚ

/-- The requested endpoint: once the regular branch is excluded, the existing
non-regular strong `(0,1)` branch gives the paper-shaped fixed star. -/
theorem D19LinearCharacterInput.involutionFixedSetStar56_of_raw_reflection
    (hin : D19LinearCharacterInput h) (k : ZMod 19) :
    InvolutionFixedSetStar56 Γ (h.smulEquiv (DihedralGroup.sr k)) := by
  have hstrong := h.fixedInducedGraph_isStrongZeroOne (DihedralGroup.sr k)
  rcases hstrong.exists_isStarWithCenter_of_not_regular
      (hin.reflection_fixedInducedGraph_not_regular k) with
    ⟨c, hstar⟩
  have hformula_edge :
      (adjacentMovedCount Γ (h.smulEquiv (DihedralGroup.sr k)) : ℤ) =
        3250 -
          58 * (fixedVertexCount (h.smulEquiv (DihedralGroup.sr k)) : ℤ) +
            2 * ((h.fixedInducedGraph (DihedralGroup.sr k)).edgeFinset.card : ℤ) :=
    adjacentMovedCount_eq_involution_fixed_edge_formula
      (Γ := Γ) h.isMoore
      (h.reflection_smulEquiv_involutive k)
      (h.reflection_smulEquiv_automorphism k)
  have hstar_formula :=
    h.reflection_starEdgeCountFormula_of_fixedInduced_isStarWithCenter
      k hstar hformula_edge
  exact h.involutionFixedSetStar56_of_reflection_fixedVertexCount_eq_56 k
    (hin.fixedVertexCount_reflection_eq_56_of_starEdgeCountFormula_local
      k hstar_formula)

end D19ActsOnMoore57

end

end Moore57
