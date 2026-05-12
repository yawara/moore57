import Moore57.D19OnMoore57.Fixed.InducedStrongStarBridge
import Moore57.D19OnMoore57.LinearCharacter.Dimension

/-!
# Reflection fixed-star from trace count data

This file exposes the paper route from Higman-style trace data to the
paper-shaped reflection fixed star.  The fixed-induced geometry is already
handled by `FixedInducedStrongStarBridge`; only the standard reflection fixed
count `a₀ = 56` has to be supplied or derived from trace data.
-/

namespace Moore57

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

namespace D19ActsOnMoore57

variable {h : D19ActsOnMoore57 V Γ}

/-- A raw full linear-character equality, the reflection character arithmetic,
and the standard adjacent-moved count give the paper-shaped fixed-star
statement for that reflection. -/
theorem involutionFixedSetStar56_of_linear_character_reflection_eq_and_adjacentMovedCount_eq_112
    (alpha beta gamma : ℕ)
    (hlin : ∀ g : DihedralGroup 19,
      Matrix.trace (E7Matrix Γ * permMatrix (h.smulEquiv g)) =
        (d19LinearCharacter alpha beta gamma g : ℚ))
    (hreflection : (alpha : ℤ) - (beta : ℤ) = 33)
    {k : ZMod 19}
    (ha1 : adjacentMovedCount Γ (h.smulEquiv (DihedralGroup.sr k)) = 112) :
    InvolutionFixedSetStar56 Γ (h.smulEquiv (DihedralGroup.sr k)) :=
  h.involutionFixedSetStar56_of_reflection_fixedVertexCount_eq_56 k
    (h.fixedVertexCount_reflection_eq_56_of_linear_character
      alpha beta gamma hlin hreflection ha1)

namespace D19LinearCharacterInput

/-- A packaged D19 linear-character input recovers the paper-shaped fixed-star
statement for a reflection from the standard adjacent-moved count. -/
theorem involutionFixedSetStar56_of_adjacentMovedCount_eq_112
    (hin : D19LinearCharacterInput h)
    {k : ZMod 19}
    (ha1 : adjacentMovedCount Γ (h.smulEquiv (DihedralGroup.sr k)) = 112) :
    InvolutionFixedSetStar56 Γ (h.smulEquiv (DihedralGroup.sr k)) :=
  h.involutionFixedSetStar56_of_reflection_fixedVertexCount_eq_56 k
    (hin.fixedVertexCount_reflection_eq_56_of_adjacentMovedCount_eq_112 ha1)

/-- Family form of
`involutionFixedSetStar56_of_adjacentMovedCount_eq_112`. -/
theorem reflection_involutionFixedSetStar56_of_adjacentMovedCount_eq_112
    (hin : D19LinearCharacterInput h)
    (ha1 : ∀ k : ZMod 19,
      adjacentMovedCount Γ (h.smulEquiv (DihedralGroup.sr k)) = 112) :
    ∀ k : ZMod 19,
      InvolutionFixedSetStar56 Γ (h.smulEquiv (DihedralGroup.sr k)) := by
  intro k
  exact hin.involutionFixedSetStar56_of_adjacentMovedCount_eq_112 (ha1 k)

/-- The same packaged trace input also yields the explicit `K_{1,55}` witness
as a Prop-valued downstream input. -/
theorem nonempty_involutionK155_of_adjacentMovedCount_eq_112
    (hin : D19LinearCharacterInput h)
    {k : ZMod 19}
    (ha1 : adjacentMovedCount Γ (h.smulEquiv (DihedralGroup.sr k)) = 112) :
    Nonempty (InvolutionK155 Γ (h.smulEquiv (DihedralGroup.sr k))) :=
  (hin.involutionFixedSetStar56_of_adjacentMovedCount_eq_112
    ha1).nonempty_involutionK155

end D19LinearCharacterInput

end D19ActsOnMoore57

end

end Moore57
