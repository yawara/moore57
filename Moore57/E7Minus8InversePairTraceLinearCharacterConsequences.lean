import Moore57.E7ProjectionLinearCharacterConsequences
import Moore57.E7Minus8InversePairTraceBoundaryBridge

/-!
# Linear-character consequences of inverse-pair trace boundaries

This file packages the inverse-pair projection trace boundaries into the
linear-character input and component-boundary consequences already available
for the concrete `E7` and `(-8)` projection character boundaries.
-/

namespace Moore57

namespace D19ActsOnMoore57

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

namespace D19LinearCharacterInput

/-- Inverse-pair projection trace boundaries for the concrete `E7` and `(-8)`
representations produce a linear-character input once the standard fixed-count
facts are supplied. -/
theorem nonempty_ofE7AndMinus8InversePairTraceBoundaries
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
        fixedVertexCount (h.smulEquiv (DihedralGroup.r d)) = 1) :
    Nonempty (D19LinearCharacterInput h) :=
  nonempty_ofE7AndMinus8CharacterBoundaries h
    alpha beta gamma A B C
    e7Trace.toCharacterClassBoundary
    minus8Trace.toCharacterValueBoundary
    hreflection_a0 hreflection_a1 hrotation_a0

end D19LinearCharacterInput

/-- Component-boundary consequence of inverse-pair trace boundaries for the
concrete `E7` and `(-8)` projection representations. -/
theorem representationCharacterComponentsBoundary_of_E7AndMinus8InversePairTraceBoundaries
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
        fixedVertexCount (h.smulEquiv (DihedralGroup.r d)) = 1) :
    RepresentationCharacterComponentsBoundary h :=
  representationCharacterComponentsBoundary_of_E7AndMinus8CharacterBoundaries h
    alpha beta gamma A B C
    e7Trace.toCharacterClassBoundary
    minus8Trace.toCharacterValueBoundary
    hreflection_a0 hreflection_a1 hrotation_a0

end D19ActsOnMoore57

end Moore57
