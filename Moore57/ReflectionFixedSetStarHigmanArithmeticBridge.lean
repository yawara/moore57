import Moore57.InvolutionHigmanCountArithmetic
import Moore57.FixedInducedStrongStarBridge

/-!
# Reflection fixed-star bridge from Higman arithmetic inputs

This file connects the arithmetic reduction in
`InvolutionHigmanCountArithmetic` to the paper-shaped fixed-star conclusion.
The geometric star-edge formula and the fixed-count bounds remain explicit
inputs.
-/

namespace Moore57

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

namespace D19ActsOnMoore57

variable {h : D19ActsOnMoore57 V Γ}

/-- Raw-reflection bridge: if the reflection trace is integral, and the
geometric star-edge formula plus the `52..56` bounds are supplied, the
reflection fixed set is the paper-shaped `56`-vertex star. -/
theorem involutionFixedSetStar56_of_reflection_trace_starEdgeCountFormula_bounds
    (k : ZMod 19) {z : ℤ}
    (htrace :
      Matrix.trace (E7Matrix Γ * permMatrix (h.smulEquiv (DihedralGroup.sr k))) =
        (z : ℚ))
    (hformula :
      (adjacentMovedCount Γ (h.smulEquiv (DihedralGroup.sr k)) : ℤ) =
        3250 -
          58 * (fixedVertexCount (h.smulEquiv (DihedralGroup.sr k)) : ℤ) +
            2 * ((fixedVertexCount (h.smulEquiv (DihedralGroup.sr k)) : ℤ) - 1))
    (hfixed_lower :
      52 ≤ (fixedVertexCount (h.smulEquiv (DihedralGroup.sr k)) : ℤ))
    (hfixed_upper :
      (fixedVertexCount (h.smulEquiv (DihedralGroup.sr k)) : ℤ) ≤ 56) :
    InvolutionFixedSetStar56 Γ (h.smulEquiv (DihedralGroup.sr k)) :=
  h.involutionFixedSetStar56_of_reflection_fixedVertexCount_eq_56 k
    (h.isMoore.starEdgeCountFormula_fixedVertexCount_eq_56_of_bounds
      (h.smulEquiv (DihedralGroup.sr k))
      (h.reflection_smulEquiv_involutive k)
      htrace hformula hfixed_lower hfixed_upper)

namespace D19LinearCharacterInput

/-- Packaged-character bridge: once the geometric star-edge formula and the
`52..56` bounds are supplied, the packaged reflection Higman congruence yields
the paper-shaped fixed-star conclusion. -/
theorem involutionFixedSetStar56_of_starEdgeCountFormula_bounds
    (hin : D19LinearCharacterInput h) (k : ZMod 19)
    (hformula :
      (adjacentMovedCount Γ (h.smulEquiv (DihedralGroup.sr k)) : ℤ) =
        3250 -
          58 * (fixedVertexCount (h.smulEquiv (DihedralGroup.sr k)) : ℤ) +
            2 * ((fixedVertexCount (h.smulEquiv (DihedralGroup.sr k)) : ℤ) - 1))
    (hfixed_lower :
      52 ≤ (fixedVertexCount (h.smulEquiv (DihedralGroup.sr k)) : ℤ))
    (hfixed_upper :
      (fixedVertexCount (h.smulEquiv (DihedralGroup.sr k)) : ℤ) ≤ 56) :
    InvolutionFixedSetStar56 Γ (h.smulEquiv (DihedralGroup.sr k)) :=
  h.involutionFixedSetStar56_of_reflection_fixedVertexCount_eq_56 k
    (hin.reflection_starEdgeCountFormula_fixedVertexCount_eq_56_of_bounds
      k hformula hfixed_lower hfixed_upper)

/-- Prop-valued `K_{1,55}` witness produced by the same bounded star-edge
arithmetic bridge. -/
theorem nonempty_involutionK155_of_starEdgeCountFormula_bounds
    (hin : D19LinearCharacterInput h) (k : ZMod 19)
    (hformula :
      (adjacentMovedCount Γ (h.smulEquiv (DihedralGroup.sr k)) : ℤ) =
        3250 -
          58 * (fixedVertexCount (h.smulEquiv (DihedralGroup.sr k)) : ℤ) +
            2 * ((fixedVertexCount (h.smulEquiv (DihedralGroup.sr k)) : ℤ) - 1))
    (hfixed_lower :
      52 ≤ (fixedVertexCount (h.smulEquiv (DihedralGroup.sr k)) : ℤ))
    (hfixed_upper :
      (fixedVertexCount (h.smulEquiv (DihedralGroup.sr k)) : ℤ) ≤ 56) :
    Nonempty (InvolutionK155 Γ (h.smulEquiv (DihedralGroup.sr k))) :=
  (hin.involutionFixedSetStar56_of_starEdgeCountFormula_bounds
    k hformula hfixed_lower hfixed_upper).nonempty_involutionK155

end D19LinearCharacterInput

end D19ActsOnMoore57

end

end Moore57
