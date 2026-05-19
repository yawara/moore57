import Moore57.Moore57Graph.HigmanTrace.Congruence
import Moore57.D19OnMoore57.LinearCharacter.Input
import Moore57.D19OnMoore57.Action.D19Action
import Moore57.Foundations.GroupTheory.D19LinearCharacter

/-!
# Higman trace congruence — D₁₉ reflection instance

The Moore57-abstract Higman congruence
`adjacentMovedCount Γ σ ≡ 7 fixedVertexCount σ + 5 [MOD 15]`
now lives in `Moore57.Moore57Graph.HigmanTrace.Congruence` and is reused below.

This file keeps only the **D₁₉-specific** instance that supplies the integer
trace witness from a packaged D₁₉ linear-character input on a reflection.
-/

namespace Moore57

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

namespace D19ActsOnMoore57

variable {h : D19ActsOnMoore57 V Γ}

namespace D19LinearCharacterInput

/-- A packaged linear-character input supplies the reflection instance of
Higman's congruence: the reflection character value is the integer
`α - β`. -/
theorem reflection_higman_natModEq
    (hin : D19LinearCharacterInput h) (k : ZMod 19) :
    adjacentMovedCount Γ (h.smulEquiv (DihedralGroup.sr k)) ≡
      7 * fixedVertexCount (h.smulEquiv (DihedralGroup.sr k)) + 5 [MOD 15] := by
  apply h.isMoore.higman_trace_int_natModEq
    (σ := h.smulEquiv (DihedralGroup.sr k))
    (z := (hin.multiplicity.alpha : ℤ) - (hin.multiplicity.beta : ℤ))
  rw [hin.linear_character, d19LinearCharacter_reflection]

end D19LinearCharacterInput

end D19ActsOnMoore57

end

end Moore57
