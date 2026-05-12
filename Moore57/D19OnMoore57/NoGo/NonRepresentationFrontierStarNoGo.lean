import Moore57.D19OnMoore57.NoGo.NonRepresentationFrontierEigenspaceNoGo
import Moore57.D19OnMoore57.Involution.FixedStarA1

/-!
# Fixed-star form of the default-base non-representation frontier no-go

This file removes the explicit reflection count hypotheses from the eigenspace
frontier no-go when an `InvolutionFixedStar55` witness is available.  The
counts are supplied by the existing fixed-star lemmas.
-/

namespace Moore57

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- Eigenspace-character no-go with the standard reflection counts supplied by
an `InvolutionFixedStar55` witness. -/
theorem no_remainingNonRepresentationFrontierAfterDefaultBase_of_eigenspaceCharactersAndFixedStar55
    (h : D19ActsOnMoore57 V Γ)
    (alpha beta gamma A B C : ℕ)
    (h7 : ∀ g : DihedralGroup 19,
      Matrix.trace (E7Matrix Γ * permMatrix (h.smulEquiv g)) =
        (d19LinearCharacter alpha beta gamma g : ℚ))
    (hMinus8 : ∀ g : DihedralGroup 19,
      Matrix.trace (permMatrix (h.smulEquiv g)) - 1 -
          Matrix.trace (E7Matrix Γ * permMatrix (h.smulEquiv g)) =
        (d19LinearCharacter A B C g : ℚ))
    {dt : ZMod 19}
    (hStar :
      InvolutionFixedStar55 Γ (h.smulEquiv (DihedralGroup.sr dt)))
    (hrotation_a0 :
      ∀ d : ZMod 19, d ≠ 0 →
        fixedVertexCount (h.smulEquiv (DihedralGroup.r d)) = 1) :
    ¬ Nonempty (RemainingNonRepresentationFrontierAfterDefaultBase h) :=
  no_remainingNonRepresentationFrontierAfterDefaultBase_of_eigenspaceCharactersAndCounts
    h alpha beta gamma A B C h7 hMinus8
    (h.fixedVertexCount_reflection_eq_56_of_involutionFixedStar55 hStar)
    hrotation_a0
    (h.adjacentMovedCount_reflection_eq_112 hStar)

/-- Raw-action-frontier alias of the fixed-star eigenspace no-go. -/
theorem no_remainingNonRepresentationRawActionFrontierAfterDefaultBase_of_eigenspaceCharactersAndFixedStar55
    (h : D19ActsOnMoore57 V Γ)
    (alpha beta gamma A B C : ℕ)
    (h7 : ∀ g : DihedralGroup 19,
      Matrix.trace (E7Matrix Γ * permMatrix (h.smulEquiv g)) =
        (d19LinearCharacter alpha beta gamma g : ℚ))
    (hMinus8 : ∀ g : DihedralGroup 19,
      Matrix.trace (permMatrix (h.smulEquiv g)) - 1 -
          Matrix.trace (E7Matrix Γ * permMatrix (h.smulEquiv g)) =
        (d19LinearCharacter A B C g : ℚ))
    {dt : ZMod 19}
    (hStar :
      InvolutionFixedStar55 Γ (h.smulEquiv (DihedralGroup.sr dt)))
    (hrotation_a0 :
      ∀ d : ZMod 19, d ≠ 0 →
        fixedVertexCount (h.smulEquiv (DihedralGroup.r d)) = 1) :
    ¬ RemainingNonRepresentationRawActionFrontierAfterDefaultBase h :=
  no_remainingNonRepresentationFrontierAfterDefaultBase_of_eigenspaceCharactersAndFixedStar55
    h alpha beta gamma A B C h7 hMinus8 hStar hrotation_a0

end

end Moore57
