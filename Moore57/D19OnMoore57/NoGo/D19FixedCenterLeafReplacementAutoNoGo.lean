import Moore57.D19OnMoore57.NoGo.D19FixedCenterLeafReplacementNoGo
import Moore57.D19OnMoore57.Rotation.RotationFixedCountOneFrontier

/-!
# Auto-rotation no-go variants for fixed-center-leaf replacement frontiers

This file removes the explicit nontrivial-rotation fixed-count hypothesis from
the fixed-center-leaf replacement no-go surface.  The rotation count is supplied
by the already-proved `D19ActsOnMoore57.rotationFixedCountOne_smulEquiv`.
-/

namespace Moore57

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- Eigenspace/reflection-count no-go for the induced fixed-star degree wrapper,
with rotation counts supplied by the ambient D19 action theorem. -/
theorem no_remainingNonRepresentationFrontierAfterDefaultBaseFixedInducedStarDegrees_of_eigenspaceCharactersAndCounts_autoRotation
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
    (hreflection_a0 :
      fixedVertexCount (h.smulEquiv (DihedralGroup.sr dt)) = 56)
    (hreflection_a1 :
      adjacentMovedCount Γ (h.smulEquiv (DihedralGroup.sr dt)) = 112) :
    ¬ Nonempty
        (RemainingNonRepresentationFrontierAfterDefaultBaseFixedInducedStarDegrees
          h) :=
  no_remainingNonRepresentationFrontierAfterDefaultBaseFixedInducedStarDegrees_of_eigenspaceCharactersAndCounts
    h alpha beta gamma A B C h7 hMinus8 hreflection_a0
    (D19ActsOnMoore57.rotationFixedCountOne_smulEquiv h) hreflection_a1

/-- Eigenspace/reflection-count no-go for the fixed-neighbor star-count wrapper,
with rotation counts supplied by the ambient D19 action theorem. -/
theorem no_remainingNonRepresentationFrontierAfterDefaultBaseFixedNeighborStarCounts_of_eigenspaceCharactersAndCounts_autoRotation
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
    (hreflection_a0 :
      fixedVertexCount (h.smulEquiv (DihedralGroup.sr dt)) = 56)
    (hreflection_a1 :
      adjacentMovedCount Γ (h.smulEquiv (DihedralGroup.sr dt)) = 112) :
    ¬ Nonempty
        (RemainingNonRepresentationFrontierAfterDefaultBaseFixedNeighborStarCounts
          h) :=
  no_remainingNonRepresentationFrontierAfterDefaultBaseFixedNeighborStarCounts_of_eigenspaceCharactersAndCounts
    h alpha beta gamma A B C h7 hMinus8 hreflection_a0
    (D19ActsOnMoore57.rotationFixedCountOne_smulEquiv h) hreflection_a1

/-- Eigenspace/reflection-count no-go for the explicit per-reflection `K_{1,55}`
wrapper, with rotation counts supplied by the ambient D19 action theorem. -/
theorem no_remainingNonRepresentationFrontierAfterDefaultBaseInvolutionK155_of_eigenspaceCharactersAndCounts_autoRotation
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
    (hreflection_a0 :
      fixedVertexCount (h.smulEquiv (DihedralGroup.sr dt)) = 56)
    (hreflection_a1 :
      adjacentMovedCount Γ (h.smulEquiv (DihedralGroup.sr dt)) = 112) :
    ¬ Nonempty
        (RemainingNonRepresentationFrontierAfterDefaultBaseInvolutionK155 h) :=
  no_remainingNonRepresentationFrontierAfterDefaultBaseInvolutionK155_of_eigenspaceCharactersAndCounts
    h alpha beta gamma A B C h7 hMinus8 hreflection_a0
    (D19ActsOnMoore57.rotationFixedCountOne_smulEquiv h) hreflection_a1

/-- Eigenspace/fixed-star no-go for the induced fixed-star degree wrapper, with
rotation counts supplied by the ambient D19 action theorem. -/
theorem no_remainingNonRepresentationFrontierAfterDefaultBaseFixedInducedStarDegrees_of_eigenspaceCharactersAndFixedStar55_autoRotation
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
      InvolutionFixedStar55 Γ (h.smulEquiv (DihedralGroup.sr dt))) :
    ¬ Nonempty
        (RemainingNonRepresentationFrontierAfterDefaultBaseFixedInducedStarDegrees
          h) :=
  no_remainingNonRepresentationFrontierAfterDefaultBaseFixedInducedStarDegrees_of_eigenspaceCharactersAndFixedStar55
    h alpha beta gamma A B C h7 hMinus8 hStar
    (D19ActsOnMoore57.rotationFixedCountOne_smulEquiv h)

/-- Eigenspace/fixed-star no-go for the fixed-neighbor star-count wrapper, with
rotation counts supplied by the ambient D19 action theorem. -/
theorem no_remainingNonRepresentationFrontierAfterDefaultBaseFixedNeighborStarCounts_of_eigenspaceCharactersAndFixedStar55_autoRotation
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
      InvolutionFixedStar55 Γ (h.smulEquiv (DihedralGroup.sr dt))) :
    ¬ Nonempty
        (RemainingNonRepresentationFrontierAfterDefaultBaseFixedNeighborStarCounts
          h) :=
  no_remainingNonRepresentationFrontierAfterDefaultBaseFixedNeighborStarCounts_of_eigenspaceCharactersAndFixedStar55
    h alpha beta gamma A B C h7 hMinus8 hStar
    (D19ActsOnMoore57.rotationFixedCountOne_smulEquiv h)

/-- Eigenspace/fixed-star no-go for the explicit per-reflection `K_{1,55}`
wrapper, with rotation counts supplied by the ambient D19 action theorem. -/
theorem no_remainingNonRepresentationFrontierAfterDefaultBaseInvolutionK155_of_eigenspaceCharactersAndFixedStar55_autoRotation
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
      InvolutionFixedStar55 Γ (h.smulEquiv (DihedralGroup.sr dt))) :
    ¬ Nonempty
        (RemainingNonRepresentationFrontierAfterDefaultBaseInvolutionK155 h) :=
  no_remainingNonRepresentationFrontierAfterDefaultBaseInvolutionK155_of_eigenspaceCharactersAndFixedStar55
    h alpha beta gamma A B C h7 hMinus8 hStar
    (D19ActsOnMoore57.rotationFixedCountOne_smulEquiv h)

/-- Eigenspace no-go for the explicit `K_{1,55}` wrapper using the wrapper's
own star witness, with rotation counts supplied by the ambient D19 action
theorem. -/
theorem no_remainingNonRepresentationFrontierAfterDefaultBaseInvolutionK155_of_eigenspaceCharactersAndOwnStar_autoRotation
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
  no_remainingNonRepresentationFrontierAfterDefaultBaseInvolutionK155_of_eigenspaceCharactersAndRotationCounts
    h alpha beta gamma A B C h7 hMinus8
    (dt := dt)
    (D19ActsOnMoore57.rotationFixedCountOne_smulEquiv h)

end

end Moore57
