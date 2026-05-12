import Moore57.D19OnMoore57.LinearCharacter.DimensionConnectors
import Moore57.D19OnMoore57.Involution.FixedStarPaperBoundary

/-!
# Paper fixed-star connectors for D19 linear-character inputs

This file exposes thin wrappers from the paper-shaped fixed-star reflection
hypothesis to the existing linear-character/count constructors.
-/

namespace Moore57

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

namespace D19ActsOnMoore57

variable {h : D19ActsOnMoore57 V Γ}

namespace D19LinearCharacterInput

/-- Paper-fixed-star form of `ofLinearCharacterAndCounts`. -/
noncomputable def ofLinearCharacterAndPaperFixedStar56
    (alpha beta gamma : ℕ)
    (minus8_trivial_nonneg : alpha ≤ 113)
    (minus8_sign_nonneg : beta ≤ 58)
    (hlin : ∀ g : DihedralGroup 19,
      Matrix.trace (E7Matrix Γ * permMatrix (h.smulEquiv g)) =
        (d19LinearCharacter alpha beta gamma g : ℚ))
    {d : ZMod 19}
    (hStar :
      InvolutionFixedSetStar56 Γ (h.smulEquiv (DihedralGroup.sr d))) :
    D19LinearCharacterInput h :=
  ofLinearCharacterAndCounts (h := h)
    alpha beta gamma minus8_trivial_nonneg minus8_sign_nonneg hlin
    (h.fixedVertexCount_reflection_eq_56_of_reflectionFixedSetStar56 hStar)
    (h.adjacentMovedCount_reflection_eq_112_of_reflectionFixedSetStar56
      hStar)

end D19LinearCharacterInput

namespace D19RepresentationCharacterInput

/-- Paper-fixed-star form of `ofLinearCharacterAndCounts`. -/
noncomputable def ofLinearCharacterAndPaperFixedStar56
    (alpha beta gamma : ℕ)
    (minus8_trivial_nonneg : alpha ≤ 113)
    (minus8_sign_nonneg : beta ≤ 58)
    (hlin : ∀ g : DihedralGroup 19,
      Matrix.trace (E7Matrix Γ * permMatrix (h.smulEquiv g)) =
        (d19LinearCharacter alpha beta gamma g : ℚ))
    {d : ZMod 19}
    (hStar :
      InvolutionFixedSetStar56 Γ (h.smulEquiv (DihedralGroup.sr d))) :
    D19RepresentationCharacterInput h :=
  ofLinearCharacterAndCounts (h := h)
    alpha beta gamma minus8_trivial_nonneg minus8_sign_nonneg hlin
    (h.fixedVertexCount_reflection_eq_56_of_reflectionFixedSetStar56 hStar)
    (h.adjacentMovedCount_reflection_eq_112_of_reflectionFixedSetStar56
      hStar)

end D19RepresentationCharacterInput

end D19ActsOnMoore57

namespace D19FinalCharacterInputs

variable {h : D19ActsOnMoore57 V Γ}

/-- Paper-fixed-star form of `ofLinearCharacterAndCounts`. -/
noncomputable def ofLinearCharacterAndPaperFixedStar56
    (alpha beta gamma : ℕ)
    (minus8_trivial_nonneg : alpha ≤ 113)
    (minus8_sign_nonneg : beta ≤ 58)
    (hlin : ∀ g : DihedralGroup 19,
      Matrix.trace (E7Matrix Γ * permMatrix (h.smulEquiv g)) =
        (d19LinearCharacter alpha beta gamma g : ℚ))
    {d : ZMod 19}
    (hStar :
      InvolutionFixedSetStar56 Γ (h.smulEquiv (DihedralGroup.sr d)))
    (fixedUpperBound : D19ActsOnMoore57.RotationFixedUpperBoundInput h) :
    D19FinalCharacterInputs h :=
  ofLinearCharacterAndCounts (h := h)
    alpha beta gamma minus8_trivial_nonneg minus8_sign_nonneg hlin
    (h.fixedVertexCount_reflection_eq_56_of_reflectionFixedSetStar56 hStar)
    (h.adjacentMovedCount_reflection_eq_112_of_reflectionFixedSetStar56
      hStar)
    fixedUpperBound

end D19FinalCharacterInputs

end

end Moore57
