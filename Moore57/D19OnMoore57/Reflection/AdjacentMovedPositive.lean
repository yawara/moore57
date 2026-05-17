import Moore57.D19OnMoore57.Reflection.InvolutionFixedSetStarFromActionBoundary
import Moore57.D19OnMoore57.Reflection.TraceCandidateLowerBoundBridge
import Moore57.Moore57Graph.Aut.InvolutionFixIsK155

/-!
# Reflections have positive adjacent-moved count

`fixedVertexCount_reflection_eq_56_of_raw_action` を Tier-2 抽象 API
`Moore57.aut_involution_fixedVertexCount_eq_56` (Cameron Theorem 3.13,
sorry-free) に直接 reduce する.

これにより以前の trace-candidate 経由
(`Reflection.TraceSmallCandidateReduction` +
`Reflection.AdjacentSwapFixedCount` の Cameron Step 2 複製) は本ファイル
からは不要となり, D19 reflection chain が大幅に短縮される.

なお `reflection_adjacentMovedCount_pos` も Tier-2 で得られる
`|Fix(σ)| = 56` から involution edge-count formula 経由で導出する.
-/

namespace Moore57

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

namespace D19ActsOnMoore57

variable {h : D19ActsOnMoore57 V Γ}

/-- Raw action data already gives the exact Cameron/Higman reflection fixed
count `56` for every reflection.

旧版では trace-candidate (`fixedVertexCount_reflection_trace_refined_raw_candidates`
の 7 候補 {6, 10, 16, 26, 36, 46, 56}) を `reflection_adjacentMovedCount_pos`
の involution edge-count formula 議論で 56 に絞っていたが,
本版では Tier-2 `Moore57.aut_involution_fixedVertexCount_eq_56`
(Cameron Theorem 3.13, sorry-free, Cameron Step 1+2 を完備) に直接 reduce する.
-/
theorem fixedVertexCount_reflection_eq_56_of_raw_action
    (k : ZMod 19) :
    fixedVertexCount (h.smulEquiv (DihedralGroup.sr k)) = 56 :=
  Moore57.aut_involution_fixedVertexCount_eq_56
    h.isMoore (h.smulEquiv (DihedralGroup.sr k))
    (h.reflection_smulEquiv_automorphism k)
    (h.reflection_smulEquiv_involutive k)
    (h.reflection_smulEquiv_ne_one k)

/-- Tier-2 経由で得られる reflection の `a₁ > 0` (旧 trace 候補経由を経ない). -/
theorem reflection_adjacentMovedCount_pos
    (k : ZMod 19) :
    0 < adjacentMovedCount Γ (h.smulEquiv (DihedralGroup.sr k)) := by
  by_contra hnot
  have hzero :
      adjacentMovedCount Γ (h.smulEquiv (DihedralGroup.sr k)) = 0 :=
    Nat.eq_zero_of_not_pos hnot
  have hfix :
      fixedVertexCount (h.smulEquiv (DihedralGroup.sr k)) = 56 :=
    h.fixedVertexCount_reflection_eq_56_of_raw_action k
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
  rw [hzero, hfix] at hformula
  push_cast at hformula
  -- 0 = 3250 - 58·56 + 2·E = 2 + 2·E ⟹ 2·E = -2, but E ≥ 0 contradicts.
  omega

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
