import Moore57.D19OnMoore57.E7Projection.Minus8InversePairTraceBoundaryBridge
import Moore57.D19OnMoore57.E7Projection.Minus8RawReflectionStarConnectors
import Moore57.D19OnMoore57.Reflection.LinearRawReflectionK155Bridge

/-!
# Inverse-pair trace raw-reflection fixed-star connectors

This file composes the inverse-pair trace boundary bridge with the existing
raw-reflection fixed-star connectors.  It contains no new linear algebra or
graph theory: inverse-pair trace data is first expanded to the concrete
character-boundary API, and the existing paper-star/K155 raw-reflection
connectors supply the reflection-wise fixed-star outputs.
-/

namespace Moore57

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

namespace D19ActsOnMoore57

/-- Inverse-pair E7/minus-8 trace boundaries plus one paper-shaped fixed-star
boundary give the raw-reflection paper-shaped `56`-fixed-set star for any
reflection. -/
theorem involutionFixedSetStar56_of_E7AndMinus8InversePairTraceBoundariesAndPaperFixedStar56_raw_reflection
    (h : D19ActsOnMoore57 V Γ)
    (alpha beta gamma A B C : ℕ)
    (e7Trace : E7ProjectionInversePairTraceBoundary h alpha beta gamma)
    (minus8Trace : Minus8ProjectionInversePairTraceBoundary h A B C)
    {dt : ZMod 19}
    (hStar :
      InvolutionFixedSetStar56 Γ (h.smulEquiv (DihedralGroup.sr dt)))
    (k : ZMod 19) :
    InvolutionFixedSetStar56 Γ (h.smulEquiv (DihedralGroup.sr k)) :=
  involutionFixedSetStar56_of_E7AndMinus8CharacterBoundariesAndPaperFixedStar56_raw_reflection
    h alpha beta gamma A B C
    e7Trace.toCharacterClassBoundary
    minus8Trace.toCharacterValueBoundary
    hStar k

/-- Inverse-pair E7/minus-8 trace boundaries plus one paper-shaped fixed-star
boundary give a nonempty explicit `K_{1,55}` witness for any reflection via
the raw-reflection bridge. -/
theorem nonempty_involutionK155_of_E7AndMinus8InversePairTraceBoundariesAndPaperFixedStar56_raw_reflection
    (h : D19ActsOnMoore57 V Γ)
    (alpha beta gamma A B C : ℕ)
    (e7Trace : E7ProjectionInversePairTraceBoundary h alpha beta gamma)
    (minus8Trace : Minus8ProjectionInversePairTraceBoundary h A B C)
    {dt : ZMod 19}
    (hStar :
      InvolutionFixedSetStar56 Γ (h.smulEquiv (DihedralGroup.sr dt)))
    (k : ZMod 19) :
    Nonempty (InvolutionK155 Γ (h.smulEquiv (DihedralGroup.sr k))) :=
  nonempty_involutionK155_of_E7AndMinus8CharacterBoundariesAndPaperFixedStar56_raw_reflection
    h alpha beta gamma A B C
    e7Trace.toCharacterClassBoundary
    minus8Trace.toCharacterValueBoundary
    hStar k

/-- Inverse-pair E7/minus-8 trace boundaries plus one explicit `K_{1,55}`
witness give the raw-reflection paper-shaped `56`-fixed-set star for any
reflection. -/
theorem involutionFixedSetStar56_of_E7AndMinus8InversePairTraceBoundariesAndInvolutionK155_raw_reflection
    (h : D19ActsOnMoore57 V Γ)
    (alpha beta gamma A B C : ℕ)
    (e7Trace : E7ProjectionInversePairTraceBoundary h alpha beta gamma)
    (minus8Trace : Minus8ProjectionInversePairTraceBoundary h A B C)
    {dt : ZMod 19}
    (hK : InvolutionK155 Γ (h.smulEquiv (DihedralGroup.sr dt)))
    (k : ZMod 19) :
    InvolutionFixedSetStar56 Γ (h.smulEquiv (DihedralGroup.sr k)) :=
  involutionFixedSetStar56_of_E7AndMinus8CharacterBoundariesAndInvolutionK155_raw_reflection
    h alpha beta gamma A B C
    e7Trace.toCharacterClassBoundary
    minus8Trace.toCharacterValueBoundary
    hK k

/-- Inverse-pair E7/minus-8 trace boundaries plus one explicit `K_{1,55}`
witness give a nonempty explicit `K_{1,55}` witness for any reflection via the
raw-reflection bridge. -/
theorem nonempty_involutionK155_of_E7AndMinus8InversePairTraceBoundariesAndInvolutionK155_raw_reflection
    (h : D19ActsOnMoore57 V Γ)
    (alpha beta gamma A B C : ℕ)
    (e7Trace : E7ProjectionInversePairTraceBoundary h alpha beta gamma)
    (minus8Trace : Minus8ProjectionInversePairTraceBoundary h A B C)
    {dt : ZMod 19}
    (hK : InvolutionK155 Γ (h.smulEquiv (DihedralGroup.sr dt)))
    (k : ZMod 19) :
    Nonempty (InvolutionK155 Γ (h.smulEquiv (DihedralGroup.sr k))) :=
  nonempty_involutionK155_of_E7AndMinus8CharacterBoundariesAndInvolutionK155_raw_reflection
    h alpha beta gamma A B C
    e7Trace.toCharacterClassBoundary
    minus8Trace.toCharacterValueBoundary
    hK k

end D19ActsOnMoore57

end

end Moore57
