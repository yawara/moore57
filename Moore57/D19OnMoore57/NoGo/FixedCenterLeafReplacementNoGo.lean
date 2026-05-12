import Moore57.D19OnMoore57.NoGo.FixedCenterLeafReplacementFrontier
import Moore57.D19OnMoore57.NoGo.NonRepresentationFrontierLinearNoGo
import Moore57.D19OnMoore57.NoGo.NonRepresentationFrontierEigenspaceNoGo
import Moore57.D19OnMoore57.NoGo.NonRepresentationFrontierStarNoGo

/-!
# No-go variants for fixed-center-leaf replacement frontiers

This file adds representation-input no-go forms for the wrappers in
`D19FixedCenterLeafReplacementFrontier`.  Each theorem only collapses the
wrapper to `RemainingNonRepresentationFrontierAfterDefaultBase` and delegates
to an existing frontier no-go theorem.
-/

namespace Moore57

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- Linear-character/count no-go for the induced fixed-star degree wrapper. -/
theorem no_remainingNonRepresentationFrontierAfterDefaultBaseFixedInducedStarDegrees_of_linearCharacterAndCounts
    (h : D19ActsOnMoore57 V Γ)
    (alpha beta gamma : ℕ)
    (minus8_trivial_nonneg : alpha ≤ 113)
    (minus8_sign_nonneg : beta ≤ 58)
    (hlin : ∀ g : DihedralGroup 19,
      Matrix.trace (E7Matrix Γ * permMatrix (h.smulEquiv g)) =
        (d19LinearCharacter alpha beta gamma g : ℚ))
    {d : ZMod 19}
    (ha0 : fixedVertexCount (h.smulEquiv (DihedralGroup.sr d)) = 56)
    (ha1 : adjacentMovedCount Γ (h.smulEquiv (DihedralGroup.sr d)) = 112) :
    ¬ Nonempty
        (RemainingNonRepresentationFrontierAfterDefaultBaseFixedInducedStarDegrees
          h) := by
  rintro ⟨connector⟩
  exact
    no_remainingNonRepresentationFrontierAfterDefaultBase_of_linearCharacterAndCounts
      h alpha beta gamma minus8_trivial_nonneg minus8_sign_nonneg hlin ha0
      ha1
      ⟨connector.toRemainingNonRepresentationFrontierAfterDefaultBase⟩

/-- Linear-character/count no-go for the fixed-neighbor star-count wrapper. -/
theorem no_remainingNonRepresentationFrontierAfterDefaultBaseFixedNeighborStarCounts_of_linearCharacterAndCounts
    (h : D19ActsOnMoore57 V Γ)
    (alpha beta gamma : ℕ)
    (minus8_trivial_nonneg : alpha ≤ 113)
    (minus8_sign_nonneg : beta ≤ 58)
    (hlin : ∀ g : DihedralGroup 19,
      Matrix.trace (E7Matrix Γ * permMatrix (h.smulEquiv g)) =
        (d19LinearCharacter alpha beta gamma g : ℚ))
    {d : ZMod 19}
    (ha0 : fixedVertexCount (h.smulEquiv (DihedralGroup.sr d)) = 56)
    (ha1 : adjacentMovedCount Γ (h.smulEquiv (DihedralGroup.sr d)) = 112) :
    ¬ Nonempty
        (RemainingNonRepresentationFrontierAfterDefaultBaseFixedNeighborStarCounts
          h) := by
  rintro ⟨connector⟩
  exact
    no_remainingNonRepresentationFrontierAfterDefaultBase_of_linearCharacterAndCounts
      h alpha beta gamma minus8_trivial_nonneg minus8_sign_nonneg hlin ha0
      ha1
      ⟨connector.toRemainingNonRepresentationFrontierAfterDefaultBase⟩

/-- Linear-character/count no-go for the explicit per-reflection `K_{1,55}`
wrapper. -/
theorem no_remainingNonRepresentationFrontierAfterDefaultBaseInvolutionK155_of_linearCharacterAndCounts
    (h : D19ActsOnMoore57 V Γ)
    (alpha beta gamma : ℕ)
    (minus8_trivial_nonneg : alpha ≤ 113)
    (minus8_sign_nonneg : beta ≤ 58)
    (hlin : ∀ g : DihedralGroup 19,
      Matrix.trace (E7Matrix Γ * permMatrix (h.smulEquiv g)) =
        (d19LinearCharacter alpha beta gamma g : ℚ))
    {d : ZMod 19}
    (ha0 : fixedVertexCount (h.smulEquiv (DihedralGroup.sr d)) = 56)
    (ha1 : adjacentMovedCount Γ (h.smulEquiv (DihedralGroup.sr d)) = 112) :
    ¬ Nonempty
        (RemainingNonRepresentationFrontierAfterDefaultBaseInvolutionK155 h) := by
  rintro ⟨connector⟩
  exact
    no_remainingNonRepresentationFrontierAfterDefaultBase_of_linearCharacterAndCounts
      h alpha beta gamma minus8_trivial_nonneg minus8_sign_nonneg hlin ha0
      ha1
      ⟨connector.toRemainingNonRepresentationFrontierAfterDefaultBase⟩

/-- Eigenspace-character/count no-go for the induced fixed-star degree wrapper. -/
theorem no_remainingNonRepresentationFrontierAfterDefaultBaseFixedInducedStarDegrees_of_eigenspaceCharactersAndCounts
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
    (hrotation_a0 :
      ∀ d : ZMod 19, d ≠ 0 →
        fixedVertexCount (h.smulEquiv (DihedralGroup.r d)) = 1)
    (hreflection_a1 :
      adjacentMovedCount Γ (h.smulEquiv (DihedralGroup.sr dt)) = 112) :
    ¬ Nonempty
        (RemainingNonRepresentationFrontierAfterDefaultBaseFixedInducedStarDegrees
          h) := by
  rintro ⟨connector⟩
  exact
    no_remainingNonRepresentationFrontierAfterDefaultBase_of_eigenspaceCharactersAndCounts
      h alpha beta gamma A B C h7 hMinus8 hreflection_a0 hrotation_a0
      hreflection_a1
      ⟨connector.toRemainingNonRepresentationFrontierAfterDefaultBase⟩

/-- Eigenspace-character/count no-go for the fixed-neighbor star-count wrapper. -/
theorem no_remainingNonRepresentationFrontierAfterDefaultBaseFixedNeighborStarCounts_of_eigenspaceCharactersAndCounts
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
    (hrotation_a0 :
      ∀ d : ZMod 19, d ≠ 0 →
        fixedVertexCount (h.smulEquiv (DihedralGroup.r d)) = 1)
    (hreflection_a1 :
      adjacentMovedCount Γ (h.smulEquiv (DihedralGroup.sr dt)) = 112) :
    ¬ Nonempty
        (RemainingNonRepresentationFrontierAfterDefaultBaseFixedNeighborStarCounts
          h) := by
  rintro ⟨connector⟩
  exact
    no_remainingNonRepresentationFrontierAfterDefaultBase_of_eigenspaceCharactersAndCounts
      h alpha beta gamma A B C h7 hMinus8 hreflection_a0 hrotation_a0
      hreflection_a1
      ⟨connector.toRemainingNonRepresentationFrontierAfterDefaultBase⟩

/-- Eigenspace-character/count no-go for the explicit per-reflection `K_{1,55}`
wrapper. -/
theorem no_remainingNonRepresentationFrontierAfterDefaultBaseInvolutionK155_of_eigenspaceCharactersAndCounts
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
    (hrotation_a0 :
      ∀ d : ZMod 19, d ≠ 0 →
        fixedVertexCount (h.smulEquiv (DihedralGroup.r d)) = 1)
    (hreflection_a1 :
      adjacentMovedCount Γ (h.smulEquiv (DihedralGroup.sr dt)) = 112) :
    ¬ Nonempty
        (RemainingNonRepresentationFrontierAfterDefaultBaseInvolutionK155 h) := by
  rintro ⟨connector⟩
  exact
    no_remainingNonRepresentationFrontierAfterDefaultBase_of_eigenspaceCharactersAndCounts
      h alpha beta gamma A B C h7 hMinus8 hreflection_a0 hrotation_a0
      hreflection_a1
      ⟨connector.toRemainingNonRepresentationFrontierAfterDefaultBase⟩

/-- Fixed-star/eigenspace no-go for the induced fixed-star degree wrapper. -/
theorem no_remainingNonRepresentationFrontierAfterDefaultBaseFixedInducedStarDegrees_of_eigenspaceCharactersAndFixedStar55
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
    ¬ Nonempty
        (RemainingNonRepresentationFrontierAfterDefaultBaseFixedInducedStarDegrees
          h) := by
  rintro ⟨connector⟩
  exact
    no_remainingNonRepresentationFrontierAfterDefaultBase_of_eigenspaceCharactersAndFixedStar55
      h alpha beta gamma A B C h7 hMinus8 hStar hrotation_a0
      ⟨connector.toRemainingNonRepresentationFrontierAfterDefaultBase⟩

/-- Fixed-star/eigenspace no-go for the fixed-neighbor star-count wrapper. -/
theorem no_remainingNonRepresentationFrontierAfterDefaultBaseFixedNeighborStarCounts_of_eigenspaceCharactersAndFixedStar55
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
    ¬ Nonempty
        (RemainingNonRepresentationFrontierAfterDefaultBaseFixedNeighborStarCounts
          h) := by
  rintro ⟨connector⟩
  exact
    no_remainingNonRepresentationFrontierAfterDefaultBase_of_eigenspaceCharactersAndFixedStar55
      h alpha beta gamma A B C h7 hMinus8 hStar hrotation_a0
      ⟨connector.toRemainingNonRepresentationFrontierAfterDefaultBase⟩

/-- Fixed-star/eigenspace no-go for the explicit per-reflection `K_{1,55}`
wrapper. -/
theorem no_remainingNonRepresentationFrontierAfterDefaultBaseInvolutionK155_of_eigenspaceCharactersAndFixedStar55
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
    ¬ Nonempty
        (RemainingNonRepresentationFrontierAfterDefaultBaseInvolutionK155 h) := by
  rintro ⟨connector⟩
  exact
    no_remainingNonRepresentationFrontierAfterDefaultBase_of_eigenspaceCharactersAndFixedStar55
      h alpha beta gamma A B C h7 hMinus8 hStar hrotation_a0
      ⟨connector.toRemainingNonRepresentationFrontierAfterDefaultBase⟩

/-- Eigenspace no-go for the explicit `K_{1,55}` wrapper, using the wrapper's
own star witness to provide the reflection fixed-star counts. -/
theorem no_remainingNonRepresentationFrontierAfterDefaultBaseInvolutionK155_of_eigenspaceCharactersAndRotationCounts
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
    (hrotation_a0 :
      ∀ d : ZMod 19, d ≠ 0 →
        fixedVertexCount (h.smulEquiv (DihedralGroup.r d)) = 1) :
    ¬ Nonempty
        (RemainingNonRepresentationFrontierAfterDefaultBaseInvolutionK155 h) := by
  rintro ⟨connector⟩
  exact
    no_remainingNonRepresentationFrontierAfterDefaultBase_of_eigenspaceCharactersAndFixedStar55
      h alpha beta gamma A B C h7 hMinus8
      (InvolutionK155.toInvolutionFixedStar55 h.isMoore
        (connector.involutionK155 dt))
      hrotation_a0
      ⟨connector.toRemainingNonRepresentationFrontierAfterDefaultBase⟩

end

end Moore57
