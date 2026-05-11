import Moore57.D19OnMoore57.Fixed.FixedInducedStarEdgeFormula
import Moore57.Moore57Graph.InvolutionEdgeCountFormula

/-!
# Reflection fixed-star bridge from trace integrality and fixed-count bounds

This file removes the explicit star-edge-formula hypothesis from the
trace-and-bounds route.  The bounds `52 ≤ a₀ ≤ 56` exclude the regular
fixed-induced branch by strongly-regular parameter arithmetic, so the fixed
induced graph is a star and the raw involution edge-count formula supplies the
star-edge formula.
-/

namespace Moore57

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

namespace D19ActsOnMoore57

variable {h : D19ActsOnMoore57 V Γ}

/-- Trace integrality plus the fixed-count bounds `52 ≤ a₀ ≤ 56` force the
paper-shaped fixed-star conclusion for a reflection. -/
theorem involutionFixedSetStar56_of_reflection_trace_fixedVertexCount_bounds
    (k : ZMod 19) {z : ℤ}
    (htrace :
      Matrix.trace (E7Matrix Γ * permMatrix (h.smulEquiv (DihedralGroup.sr k))) =
        (z : ℚ))
    (hfixed_lower :
      52 ≤ (fixedVertexCount (h.smulEquiv (DihedralGroup.sr k)) : ℤ))
    (hfixed_upper :
      (fixedVertexCount (h.smulEquiv (DihedralGroup.sr k)) : ℤ) ≤ 56) :
    InvolutionFixedSetStar56 Γ (h.smulEquiv (DihedralGroup.sr k)) := by
  have hfixed_lower_nat :
      52 ≤ fixedVertexCount (h.smulEquiv (DihedralGroup.sr k)) := by
    exact_mod_cast hfixed_lower
  have hfixed_upper_nat :
      fixedVertexCount (h.smulEquiv (DihedralGroup.sr k)) ≤ 56 := by
    exact_mod_cast hfixed_upper
  have hnotRegular :
      ¬ ∃ d : ℕ,
        ∀ x : fixedVertexSet (h.smulEquiv (DihedralGroup.sr k)),
          (h.fixedInducedGraph (DihedralGroup.sr k)).degree x = d :=
    h.fixedInducedGraph_not_regular_of_fixedVertexCount_between_52_56
      (DihedralGroup.sr k) hfixed_lower_nat hfixed_upper_nat
  have hstrong := h.fixedInducedGraph_isStrongZeroOne (DihedralGroup.sr k)
  rcases hstrong.exists_isStarWithCenter_of_not_regular hnotRegular with
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
  exact h.involutionFixedSetStar56_of_reflection_trace_starEdgeCountFormula_bounds
    k htrace
    (h.reflection_starEdgeCountFormula_of_fixedInduced_isStarWithCenter
      k hstar hformula_edge)
    hfixed_lower hfixed_upper

/-- Prop-valued `K_{1,55}` output from the same trace-and-bounds bridge. -/
theorem nonempty_involutionK155_of_reflection_trace_fixedVertexCount_bounds
    (k : ZMod 19) {z : ℤ}
    (htrace :
      Matrix.trace (E7Matrix Γ * permMatrix (h.smulEquiv (DihedralGroup.sr k))) =
        (z : ℚ))
    (hfixed_lower :
      52 ≤ (fixedVertexCount (h.smulEquiv (DihedralGroup.sr k)) : ℤ))
    (hfixed_upper :
      (fixedVertexCount (h.smulEquiv (DihedralGroup.sr k)) : ℤ) ≤ 56) :
    Nonempty (InvolutionK155 Γ (h.smulEquiv (DihedralGroup.sr k))) :=
  (h.involutionFixedSetStar56_of_reflection_trace_fixedVertexCount_bounds
    k htrace hfixed_lower hfixed_upper).nonempty_involutionK155

end D19ActsOnMoore57

end

end Moore57
