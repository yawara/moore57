import Moore57.D19OnMoore57.Reflection.AdjacentSwapFixedCount
import Moore57.D19OnMoore57.Reflection.TraceSmallCandidateReduction

/-!
# Reflections have positive adjacent-moved count

The adjacent-swap branch is already closed by
`ReflectionAdjacentSwapFixedCount`.  This file closes its complement.  The
trace-refined raw fixed-count candidates give `a₀ ≤ 56` for a reflection, while
the involution edge-count formula makes `a₁ = 0` impossible under that bound.
Thus every reflection has positive adjacent-moved count, and the adjacent-swap
fixed-count theorem applies uniformly.
-/

namespace Moore57

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

namespace D19ActsOnMoore57

variable {h : D19ActsOnMoore57 V Γ}

/-- The trace-refined raw reflection candidate list gives the coarse upper
bound `a₀ ≤ 56`. -/
theorem fixedVertexCount_reflection_trace_refined_le_fiftySix
    (k : ZMod 19) :
    fixedVertexCount (h.smulEquiv (DihedralGroup.sr k)) ≤ 56 := by
  rcases h.fixedVertexCount_reflection_trace_refined_raw_candidates k with
      h6 | h10 | h16 | h26 | h36 | h46 | h56 <;> omega

/-- A reflection cannot have `a₁ = 0`: the trace-refined bound `a₀ ≤ 56` and
the involution edge-count formula force `a₁ ≥ 2`. -/
theorem reflection_adjacentMovedCount_pos
    (k : ZMod 19) :
    0 < adjacentMovedCount Γ (h.smulEquiv (DihedralGroup.sr k)) := by
  by_contra hnot
  have hzero :
      adjacentMovedCount Γ (h.smulEquiv (DihedralGroup.sr k)) = 0 :=
    Nat.eq_zero_of_not_pos hnot
  have hleNat :=
    h.fixedVertexCount_reflection_trace_refined_le_fiftySix k
  have hleInt :
      (fixedVertexCount (h.smulEquiv (DihedralGroup.sr k)) : ℤ) ≤ 56 := by
    exact_mod_cast hleNat
  have hedgeNonneg :
      0 ≤
        ((h.fixedInducedGraph (DihedralGroup.sr k)).edgeFinset.card : ℤ) := by
    exact_mod_cast Nat.zero_le
      (h.fixedInducedGraph (DihedralGroup.sr k)).edgeFinset.card
  have hformula :
      (adjacentMovedCount Γ (h.smulEquiv (DihedralGroup.sr k)) : ℤ) =
        3250 -
          58 * (fixedVertexCount (h.smulEquiv (DihedralGroup.sr k)) : ℤ) +
            2 * ((h.fixedInducedGraph (DihedralGroup.sr k)).edgeFinset.card : ℤ) :=
    adjacentMovedCount_eq_involution_fixed_edge_formula
      (Γ := Γ) h.isMoore
      (h.reflection_smulEquiv_involutive k)
      (h.reflection_smulEquiv_automorphism k)
  rw [hzero] at hformula
  norm_num at hformula
  nlinarith

/-- Raw action data already gives the exact Cameron/Higman reflection fixed
count `56` for every reflection. -/
theorem fixedVertexCount_reflection_eq_56_of_raw_action
    (k : ZMod 19) :
    fixedVertexCount (h.smulEquiv (DihedralGroup.sr k)) = 56 :=
  h.fixedVertexCount_reflection_eq_56_of_adjacentMovedCount_pos
    k (h.reflection_adjacentMovedCount_pos k)

/-- Package form of the raw-action reflection fixed-count theorem. -/
def reflectionFixedCountLower47_of_raw_action :
    ReflectionFixedCountLower47 h where
  lower := by
    intro k
    rw [h.fixedVertexCount_reflection_eq_56_of_raw_action k]
    norm_num

end D19ActsOnMoore57

end

end Moore57
