import Moore57.D19OnMoore57.NoGo.FixedCenterLeafReplacementAutoNoGo

/-!
# K155 no-go aliases for fixed-center-leaf replacement frontiers

This file exposes high-level aliases where a single reflection-level
`InvolutionK155` witness supplies the fixed-star reflection-count input needed
by the fixed-center-leaf replacement no-go theorems.  The proofs only delegate
to the existing auto-rotation fixed-star no-go surface.
-/

namespace Moore57

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- Eigenspace/K155 no-go for the induced fixed-star degree wrapper, with
rotation counts supplied by the ambient D19 action theorem. -/
theorem no_remainingNonRepresentationFrontierAfterDefaultBaseFixedInducedStarDegrees_of_eigenspaceCharactersAndK155_autoRotation
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
    (hK : InvolutionK155 Γ (h.smulEquiv (DihedralGroup.sr dt))) :
    ¬ Nonempty
        (RemainingNonRepresentationFrontierAfterDefaultBaseFixedInducedStarDegrees
          h) :=
  no_remainingNonRepresentationFrontierAfterDefaultBaseFixedInducedStarDegrees_of_eigenspaceCharactersAndFixedStar55_autoRotation
    h alpha beta gamma A B C h7 hMinus8
    (InvolutionK155.toInvolutionFixedStar55 h.isMoore hK)

/-- Eigenspace/K155 no-go for the fixed-neighbor star-count wrapper, with
rotation counts supplied by the ambient D19 action theorem. -/
theorem no_remainingNonRepresentationFrontierAfterDefaultBaseFixedNeighborStarCounts_of_eigenspaceCharactersAndK155_autoRotation
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
    (hK : InvolutionK155 Γ (h.smulEquiv (DihedralGroup.sr dt))) :
    ¬ Nonempty
        (RemainingNonRepresentationFrontierAfterDefaultBaseFixedNeighborStarCounts
          h) :=
  no_remainingNonRepresentationFrontierAfterDefaultBaseFixedNeighborStarCounts_of_eigenspaceCharactersAndFixedStar55_autoRotation
    h alpha beta gamma A B C h7 hMinus8
    (InvolutionK155.toInvolutionFixedStar55 h.isMoore hK)

/-- Eigenspace/K155 no-go for the explicit per-reflection `K_{1,55}` wrapper,
with rotation counts supplied by the ambient D19 action theorem. -/
theorem no_remainingNonRepresentationFrontierAfterDefaultBaseInvolutionK155_of_eigenspaceCharactersAndK155_autoRotation
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
    (hK : InvolutionK155 Γ (h.smulEquiv (DihedralGroup.sr dt))) :
    ¬ Nonempty
        (RemainingNonRepresentationFrontierAfterDefaultBaseInvolutionK155 h) :=
  no_remainingNonRepresentationFrontierAfterDefaultBaseInvolutionK155_of_eigenspaceCharactersAndFixedStar55_autoRotation
    h alpha beta gamma A B C h7 hMinus8
    (InvolutionK155.toInvolutionFixedStar55 h.isMoore hK)

/-- Concise alias for the explicit `K_{1,55}` wrapper no-go using the
wrapper's own per-reflection `K_{1,55}` witnesses. -/
theorem no_remainingNonRepresentationFrontierAfterDefaultBaseInvolutionK155_of_eigenspaceCharactersAndOwnK155_autoRotation
    (h : D19ActsOnMoore57 V Γ)
    (alpha beta gamma A B C : ℕ)
    (h7 : ∀ g : DihedralGroup 19,
      Matrix.trace (E7Matrix Γ * permMatrix (h.smulEquiv g)) =
        (d19LinearCharacter alpha beta gamma g : ℚ))
    (hMinus8 : ∀ g : DihedralGroup 19,
      Matrix.trace (permMatrix (h.smulEquiv g)) - 1 -
          Matrix.trace (E7Matrix Γ * permMatrix (h.smulEquiv g)) =
        (d19LinearCharacter A B C g : ℚ))
    {dt : ZMod 19} :
    ¬ Nonempty
        (RemainingNonRepresentationFrontierAfterDefaultBaseInvolutionK155 h) :=
  no_remainingNonRepresentationFrontierAfterDefaultBaseInvolutionK155_of_eigenspaceCharactersAndOwnStar_autoRotation
    h alpha beta gamma A B C h7 hMinus8 (dt := dt)

end

end Moore57
