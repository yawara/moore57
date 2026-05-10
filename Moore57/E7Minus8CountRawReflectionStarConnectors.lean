import Moore57.E7ProjectionLinearCharacterConsequences
import Moore57.ReflectionLinearRawReflectionK155Bridge

/-!
# E7/minus-8 count raw-reflection fixed-star connectors

This file exposes the raw-reflection fixed-star and `K_{1,55}` wrappers directly
from the concrete E7/minus-8 character-boundary inputs, together with the
fixed-count hypotheses needed to build `D19LinearCharacterInput`.
-/

namespace Moore57

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

namespace D19ActsOnMoore57

/-- Concrete E7/minus-8 character boundaries plus the standard reflection and
rotation fixed-count inputs give the raw-reflection paper-shaped `56`-fixed-set
star for any reflection. -/
theorem involutionFixedSetStar56_of_E7AndMinus8CharacterBoundariesAndReflectionCounts_raw_reflection
    (h : D19ActsOnMoore57 V Γ)
    (alpha beta gamma A B C : ℕ)
    (e7Class :
      D19CharacterClassBoundary h.e7ProjectionRepresentation alpha beta gamma)
    (minus8Values :
      D19CharacterValueBoundary h.minus8ProjectionRepresentation A B C)
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
  (D19LinearCharacterInput.ofE7AndMinus8CharacterBoundaries h
    alpha beta gamma A B C e7Class minus8Values
    hreflection_a0 hreflection_a1 hrotation_a0)
      |>.involutionFixedSetStar56_of_raw_reflection k

/-- Concrete E7/minus-8 character boundaries plus the standard reflection and
rotation fixed-count inputs give a nonempty explicit `K_{1,55}` witness for any
reflection via the raw-reflection bridge. -/
theorem nonempty_involutionK155_of_E7AndMinus8CharacterBoundariesAndReflectionCounts_raw_reflection
    (h : D19ActsOnMoore57 V Γ)
    (alpha beta gamma A B C : ℕ)
    (e7Class :
      D19CharacterClassBoundary h.e7ProjectionRepresentation alpha beta gamma)
    (minus8Values :
      D19CharacterValueBoundary h.minus8ProjectionRepresentation A B C)
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
  (D19LinearCharacterInput.ofE7AndMinus8CharacterBoundaries h
    alpha beta gamma A B C e7Class minus8Values
    hreflection_a0 hreflection_a1 hrotation_a0)
      |>.nonempty_involutionK155_of_raw_reflection k

end D19ActsOnMoore57

end

end Moore57
