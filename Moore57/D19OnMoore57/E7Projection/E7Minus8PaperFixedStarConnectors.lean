import Moore57.D19OnMoore57.E7Projection.E7Minus8CharacterInputBridge
import Moore57.D19OnMoore57.Involution.InvolutionFixedStarPaperBoundary
import Moore57.D19OnMoore57.Rotation.RotationFixedCountOneFrontier

/-!
# E7/minus-8 character boundaries with paper fixed-star input

This file exposes the concrete E7 and `(-8)` character-boundary constructor
with the reflection-side hypotheses supplied by the paper-shaped fixed-star
witness.
-/

namespace Moore57

noncomputable section

namespace D19ActsOnMoore57

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

namespace D19LinearCharacterInput

/-- Build `D19LinearCharacterInput` from concrete E7 and `(-8)`
character-boundary data, with the reflection counts extracted from the
paper-shaped `56`-vertex fixed-star witness. -/
noncomputable def ofE7AndMinus8CharacterBoundariesAndPaperFixedStar56
    (h : D19ActsOnMoore57 V Γ)
    (alpha beta gamma A B C : ℕ)
    (e7Class :
      D19CharacterClassBoundary h.e7ProjectionRepresentation alpha beta gamma)
    (minus8Values :
      D19CharacterValueBoundary h.minus8ProjectionRepresentation A B C)
    {dt : ZMod 19}
    (hStar :
      InvolutionFixedSetStar56 Γ (h.smulEquiv (DihedralGroup.sr dt))) :
    D19LinearCharacterInput h :=
  ofE7AndMinus8CharacterBoundaries h alpha beta gamma A B C
    e7Class minus8Values
    (h.fixedVertexCount_reflection_eq_56_of_reflectionFixedSetStar56 hStar)
    (h.adjacentMovedCount_reflection_eq_112_of_reflectionFixedSetStar56
      hStar)
    (D19ActsOnMoore57.rotationFixedCountOne_smulEquiv h)

end D19LinearCharacterInput

/-- Component-boundary form of
`D19LinearCharacterInput.ofE7AndMinus8CharacterBoundariesAndPaperFixedStar56`.
-/
theorem representationCharacterComponentsBoundary_of_E7AndMinus8CharacterBoundariesAndPaperFixedStar56
    (h : D19ActsOnMoore57 V Γ)
    (alpha beta gamma A B C : ℕ)
    (e7Class :
      D19CharacterClassBoundary h.e7ProjectionRepresentation alpha beta gamma)
    (minus8Values :
      D19CharacterValueBoundary h.minus8ProjectionRepresentation A B C)
    {dt : ZMod 19}
    (hStar :
      InvolutionFixedSetStar56 Γ (h.smulEquiv (DihedralGroup.sr dt))) :
    RepresentationCharacterComponentsBoundary h :=
  (D19LinearCharacterInput.ofE7AndMinus8CharacterBoundariesAndPaperFixedStar56 h
      alpha beta gamma A B C e7Class minus8Values hStar)
      |>.representationCharacterComponentsBoundary

end D19ActsOnMoore57

end

end Moore57
