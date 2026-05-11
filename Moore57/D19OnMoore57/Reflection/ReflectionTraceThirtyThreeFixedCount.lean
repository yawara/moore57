import Moore57.D19OnMoore57.Reflection.ReflectionRegularTenTraceArithmetic
import Moore57.D19OnMoore57.Reflection.ReflectionTraceCandidateLowerBoundBridge

/-!
# Reflection fixed count from E7 trace value `33`

This file isolates the non-circular reflection-count step: for a single
reflection, the E7 trace value `33` rules out the regular-`10` branch and the
nonregular strong `(0,1)` branch then forces fixed count `56` through the
star-edge formula.
-/

namespace Moore57

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

namespace D19ActsOnMoore57

variable {h : D19ActsOnMoore57 V Γ}

/-- For a reflection whose fixed-induced graph is star-shaped, E7 trace value
`33` forces the fixed count to be `56`. -/
theorem fixedVertexCount_reflection_eq_56_of_trace_eq_33_and_starEdgeCountFormula
    (k : ZMod 19)
    (htrace33 :
      Matrix.trace (E7Matrix Γ * permMatrix (h.smulEquiv (DihedralGroup.sr k))) =
        (33 : ℚ))
    (hformula :
      (adjacentMovedCount Γ (h.smulEquiv (DihedralGroup.sr k)) : ℤ) =
        3250 -
          58 * (fixedVertexCount (h.smulEquiv (DihedralGroup.sr k)) : ℤ) +
            2 * ((fixedVertexCount (h.smulEquiv (DihedralGroup.sr k)) : ℤ) - 1)) :
    fixedVertexCount (h.smulEquiv (DihedralGroup.sr k)) = 56 := by
  have htrace := htrace33
  rw [h.isMoore.higman_trace_formula] at htrace
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

/-- A single-reflection E7 trace value `33` forces the paper fixed count `56`
without assuming a packaged full D19 linear-character input. -/
theorem fixedVertexCount_reflection_eq_56_of_E7_trace_eq_33
    (k : ZMod 19)
    (htrace33 :
      Matrix.trace (E7Matrix Γ * permMatrix (h.smulEquiv (DihedralGroup.sr k))) =
        (33 : ℚ)) :
    fixedVertexCount (h.smulEquiv (DihedralGroup.sr k)) = 56 := by
  by_cases hregular :
      ∃ d : ℕ,
        ∀ x : fixedVertexSet (h.smulEquiv (DihedralGroup.sr k)),
          (h.fixedInducedGraph (DihedralGroup.sr k)).degree x = d
  · have hreg :=
      h.reflectionRegularTenAllCenterNeighborOrbitsPreserved_of_regular
        k hregular
    have htrace181 :=
      hreg.trace_E7Matrix_mul_permMatrix_eq_181
    have hbad : (181 : ℚ) = 33 := htrace181.symm.trans htrace33
    norm_num at hbad
  · have hstrong := h.fixedInducedGraph_isStrongZeroOne (DihedralGroup.sr k)
    rcases hstrong.exists_isStarWithCenter_of_not_regular hregular with
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
    exact
      h.fixedVertexCount_reflection_eq_56_of_trace_eq_33_and_starEdgeCountFormula
        k htrace33 hstar_formula

/-- Uniform trace-`33` package gives the lower-bound package used by the
reflection-count route. -/
theorem reflectionFixedCountLower47_of_E7_trace_eq_33
    (htrace33 :
      ∀ k : ZMod 19,
        Matrix.trace (E7Matrix Γ * permMatrix (h.smulEquiv (DihedralGroup.sr k))) =
          (33 : ℚ)) :
    ReflectionFixedCountLower47 h where
  lower := by
    intro k
    rw [h.fixedVertexCount_reflection_eq_56_of_E7_trace_eq_33 k (htrace33 k)]
    norm_num

end D19ActsOnMoore57

end

end Moore57
