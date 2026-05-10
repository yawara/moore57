import Moore57.E7Minus8InversePairTraceLinearCharacterConsequences
import Moore57.ReflectionLinearCharacterNonemptyBridge

/-!
# Inverse-pair trace count raw-reflection fixed-star connectors

This file exposes the raw-reflection fixed-star and `K_{1,55}` wrappers directly
from inverse-pair trace boundaries plus the count-side inputs needed to build a
nonempty `D19LinearCharacterInput`.
-/

namespace Moore57

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

namespace D19ActsOnMoore57

/-- Inverse-pair E7/minus-8 trace boundaries plus the reflection and rotation
count inputs give the raw-reflection paper-shaped `56`-fixed-set star for any
reflection. -/
theorem involutionFixedSetStar56_of_E7AndMinus8InversePairTraceBoundariesAndReflectionCounts_raw_reflection
    (h : D19ActsOnMoore57 V Γ)
    (alpha beta gamma A B C : ℕ)
    (e7Trace : E7ProjectionInversePairTraceBoundary h alpha beta gamma)
    (minus8Trace : Minus8ProjectionInversePairTraceBoundary h A B C)
    {dt : ZMod 19}
    (hreflection_a0 :
      fixedVertexCount (h.smulEquiv (DihedralGroup.sr dt)) = 56)
    (hreflection_a1 :
      adjacentMovedCount Γ (h.smulEquiv (DihedralGroup.sr dt)) = 112)
    (hrotation_a0 :
      ∀ d : ZMod 19, d ≠ 0 →
        fixedVertexCount (h.smulEquiv (DihedralGroup.r d)) = 1)
    (k : ZMod 19) :
    InvolutionFixedSetStar56 Γ (h.smulEquiv (DihedralGroup.sr k)) :=
  involutionFixedSetStar56_of_nonempty_linearCharacterInput_raw_reflection
    (D19LinearCharacterInput.nonempty_ofE7AndMinus8InversePairTraceBoundaries
      h alpha beta gamma A B C e7Trace minus8Trace
      hreflection_a0 hreflection_a1 hrotation_a0)
    k

/-- Inverse-pair E7/minus-8 trace boundaries plus the reflection and rotation
count inputs give a nonempty explicit `K_{1,55}` witness for any reflection via
the raw-reflection bridge. -/
theorem nonempty_involutionK155_of_E7AndMinus8InversePairTraceBoundariesAndReflectionCounts_raw_reflection
    (h : D19ActsOnMoore57 V Γ)
    (alpha beta gamma A B C : ℕ)
    (e7Trace : E7ProjectionInversePairTraceBoundary h alpha beta gamma)
    (minus8Trace : Minus8ProjectionInversePairTraceBoundary h A B C)
    {dt : ZMod 19}
    (hreflection_a0 :
      fixedVertexCount (h.smulEquiv (DihedralGroup.sr dt)) = 56)
    (hreflection_a1 :
      adjacentMovedCount Γ (h.smulEquiv (DihedralGroup.sr dt)) = 112)
    (hrotation_a0 :
      ∀ d : ZMod 19, d ≠ 0 →
        fixedVertexCount (h.smulEquiv (DihedralGroup.r d)) = 1)
    (k : ZMod 19) :
    Nonempty (InvolutionK155 Γ (h.smulEquiv (DihedralGroup.sr k))) :=
  nonempty_involutionK155_of_nonempty_linearCharacterInput_raw_reflection
    (D19LinearCharacterInput.nonempty_ofE7AndMinus8InversePairTraceBoundaries
      h alpha beta gamma A B C e7Trace minus8Trace
      hreflection_a0 hreflection_a1 hrotation_a0)
    k

end D19ActsOnMoore57

end

end Moore57
