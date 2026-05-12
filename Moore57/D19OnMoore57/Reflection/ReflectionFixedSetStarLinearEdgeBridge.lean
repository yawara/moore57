import Moore57.D19OnMoore57.Fixed.FixedInducedStarEdgeFormula
import Moore57.Moore57Graph.InvolutionEdgeCountFormula

/-!
# Reflection fixed-star bridge from linear trace and edge formula

The congruence-only Higman route needs explicit `52..56` bounds.  If the full
D19 linear-character value at reflections is available, the star-edge formula
itself forces the fixed count `56`, so no separate bounds are needed.
-/

namespace Moore57

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

namespace D19ActsOnMoore57

variable {h : D19ActsOnMoore57 V Γ}

namespace D19LinearCharacterInput

/-- The full reflection character value `33`, together with the star-edge
formula, forces the reflection fixed count `56`. -/
theorem fixedVertexCount_reflection_eq_56_of_starEdgeCountFormula
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

/-- Bounds-free packaged bridge from the star-edge formula to the paper-shaped
reflection fixed star. -/
theorem involutionFixedSetStar56_of_starEdgeCountFormula
    (hin : D19LinearCharacterInput h) (k : ZMod 19)
    (hformula :
      (adjacentMovedCount Γ (h.smulEquiv (DihedralGroup.sr k)) : ℤ) =
        3250 -
          58 * (fixedVertexCount (h.smulEquiv (DihedralGroup.sr k)) : ℤ) +
            2 * ((fixedVertexCount (h.smulEquiv (DihedralGroup.sr k)) : ℤ) - 1)) :
    InvolutionFixedSetStar56 Γ (h.smulEquiv (DihedralGroup.sr k)) :=
  h.involutionFixedSetStar56_of_reflection_fixedVertexCount_eq_56 k
    (hin.fixedVertexCount_reflection_eq_56_of_starEdgeCountFormula k hformula)

/-- If the fixed-induced reflection graph is already known to be a star, the
raw involution edge-count formula supplies the star-edge formula, and the full
reflection character value forces the paper-shaped fixed star. -/
theorem involutionFixedSetStar56_of_fixedInduced_isStarWithCenter
    (hin : D19LinearCharacterInput h) (k : ZMod 19)
    {c : fixedVertexSet (h.smulEquiv (DihedralGroup.sr k))}
    (hstar : IsStarWithCenter (h.fixedInducedGraph (DihedralGroup.sr k)) c) :
    InvolutionFixedSetStar56 Γ (h.smulEquiv (DihedralGroup.sr k)) := by
  have hformula_edge :
      (adjacentMovedCount Γ (h.smulEquiv (DihedralGroup.sr k)) : ℤ) =
        3250 -
          58 * (fixedVertexCount (h.smulEquiv (DihedralGroup.sr k)) : ℤ) +
            2 * ((h.fixedInducedGraph (DihedralGroup.sr k)).edgeFinset.card : ℤ) :=
    adjacentMovedCount_eq_involution_fixed_edge_formula
      (Γ := Γ) h.isMoore
      (h.reflection_smulEquiv_involutive k)
      (h.reflection_smulEquiv_automorphism k)
  exact hin.involutionFixedSetStar56_of_starEdgeCountFormula k
    (h.reflection_starEdgeCountFormula_of_fixedInduced_isStarWithCenter
      k hstar hformula_edge)

/-- Non-regular fixed-induced branch: Lemma 1 gives a star, and the
linear-character star-edge bridge then gives `InvolutionFixedSetStar56`. -/
theorem involutionFixedSetStar56_of_fixedInduced_not_regular
    (hin : D19LinearCharacterInput h) (k : ZMod 19)
    (hnotRegular :
      ¬ ∃ d : ℕ,
        ∀ v : fixedVertexSet (h.smulEquiv (DihedralGroup.sr k)),
          (h.fixedInducedGraph (DihedralGroup.sr k)).degree v = d) :
    InvolutionFixedSetStar56 Γ (h.smulEquiv (DihedralGroup.sr k)) := by
  have hstrong := h.fixedInducedGraph_isStrongZeroOne (DihedralGroup.sr k)
  rcases hstrong.exists_isStarWithCenter_of_not_regular hnotRegular with
    ⟨c, hstar⟩
  exact hin.involutionFixedSetStar56_of_fixedInduced_isStarWithCenter k hstar

end D19LinearCharacterInput

end D19ActsOnMoore57

end

end Moore57
