import Moore57.D19OnMoore57.E7Projection.E7Minus8PaperFixedStarConnectors
import Moore57.D19OnMoore57.E7Projection.E7Minus8K155NoGoConnectors
import Moore57.D19OnMoore57.Reflection.ReflectionLinearRawReflectionK155Bridge

/-!
# E7/minus-8 raw-reflection fixed-star connectors

This file keeps the raw-reflection fixed-star bridge available at the concrete
E7/minus-8 boundary surfaces.  No geometry or linear algebra is reproved here:
the concrete boundary constructors first build `D19LinearCharacterInput`, and
the existing raw-reflection bridge then supplies the fixed-star/K155 outputs.
-/

namespace Moore57

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

namespace D19ActsOnMoore57

variable {h : D19ActsOnMoore57 V Γ}

/-- Concrete E7/minus-8 character boundaries plus one paper-shaped fixed-star
boundary give the raw-reflection paper-shaped `56`-fixed-set star for any
reflection. -/
theorem involutionFixedSetStar56_of_E7AndMinus8CharacterBoundariesAndPaperFixedStar56_raw_reflection
    (h : D19ActsOnMoore57 V Γ)
    (alpha beta gamma A B C : ℕ)
    (e7Class :
      D19CharacterClassBoundary h.e7ProjectionRepresentation alpha beta gamma)
    (minus8Values :
      D19CharacterValueBoundary h.minus8ProjectionRepresentation A B C)
    {dt : ZMod 19}
    (hStar :
      InvolutionFixedSetStar56 Γ (h.smulEquiv (DihedralGroup.sr dt)))
    (k : ZMod 19) :
    InvolutionFixedSetStar56 Γ (h.smulEquiv (DihedralGroup.sr k)) :=
  (D19LinearCharacterInput.ofE7AndMinus8CharacterBoundariesAndPaperFixedStar56
    h alpha beta gamma A B C e7Class minus8Values hStar)
      |>.involutionFixedSetStar56_of_raw_reflection k

/-- Concrete E7/minus-8 character boundaries plus one paper-shaped fixed-star
boundary give a nonempty explicit `K_{1,55}` witness for any reflection via
the raw-reflection bridge. -/
theorem nonempty_involutionK155_of_E7AndMinus8CharacterBoundariesAndPaperFixedStar56_raw_reflection
    (h : D19ActsOnMoore57 V Γ)
    (alpha beta gamma A B C : ℕ)
    (e7Class :
      D19CharacterClassBoundary h.e7ProjectionRepresentation alpha beta gamma)
    (minus8Values :
      D19CharacterValueBoundary h.minus8ProjectionRepresentation A B C)
    {dt : ZMod 19}
    (hStar :
      InvolutionFixedSetStar56 Γ (h.smulEquiv (DihedralGroup.sr dt)))
    (k : ZMod 19) :
    Nonempty (InvolutionK155 Γ (h.smulEquiv (DihedralGroup.sr k))) :=
  (D19LinearCharacterInput.ofE7AndMinus8CharacterBoundariesAndPaperFixedStar56
    h alpha beta gamma A B C e7Class minus8Values hStar)
      |>.nonempty_involutionK155_of_raw_reflection k

/-- Concrete E7/minus-8 character boundaries plus one explicit `K_{1,55}`
witness give the raw-reflection paper-shaped `56`-fixed-set star for any
reflection. -/
theorem involutionFixedSetStar56_of_E7AndMinus8CharacterBoundariesAndInvolutionK155_raw_reflection
    (h : D19ActsOnMoore57 V Γ)
    (alpha beta gamma A B C : ℕ)
    (e7Class :
      D19CharacterClassBoundary h.e7ProjectionRepresentation alpha beta gamma)
    (minus8Values :
      D19CharacterValueBoundary h.minus8ProjectionRepresentation A B C)
    {dt : ZMod 19}
    (hK : InvolutionK155 Γ (h.smulEquiv (DihedralGroup.sr dt)))
    (k : ZMod 19) :
    InvolutionFixedSetStar56 Γ (h.smulEquiv (DihedralGroup.sr k)) :=
  (D19LinearCharacterInput.ofE7AndMinus8CharacterBoundariesAndInvolutionK155
    h alpha beta gamma A B C e7Class minus8Values hK)
      |>.involutionFixedSetStar56_of_raw_reflection k

/-- Concrete E7/minus-8 character boundaries plus one explicit `K_{1,55}`
witness give a nonempty explicit `K_{1,55}` witness for any reflection via the
raw-reflection bridge. -/
theorem nonempty_involutionK155_of_E7AndMinus8CharacterBoundariesAndInvolutionK155_raw_reflection
    (h : D19ActsOnMoore57 V Γ)
    (alpha beta gamma A B C : ℕ)
    (e7Class :
      D19CharacterClassBoundary h.e7ProjectionRepresentation alpha beta gamma)
    (minus8Values :
      D19CharacterValueBoundary h.minus8ProjectionRepresentation A B C)
    {dt : ZMod 19}
    (hK : InvolutionK155 Γ (h.smulEquiv (DihedralGroup.sr dt)))
    (k : ZMod 19) :
    Nonempty (InvolutionK155 Γ (h.smulEquiv (DihedralGroup.sr k))) :=
  (D19LinearCharacterInput.ofE7AndMinus8CharacterBoundariesAndInvolutionK155
    h alpha beta gamma A B C e7Class minus8Values hK)
      |>.nonempty_involutionK155_of_raw_reflection k

end D19ActsOnMoore57

end

end Moore57
