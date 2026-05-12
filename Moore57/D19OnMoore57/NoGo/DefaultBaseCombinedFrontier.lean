import Moore57.D19OnMoore57.BranchOrbit.ABCDefaultBaseCombinedFrontier
import Moore57.D19OnMoore57.NoGo.NonRepresentationFrontier
import Moore57.D19OnMoore57.Rotation.FixedCountOneFrontier

/-!
# No-go surfaces for combined default-base frontier wrappers

The combined wrappers in `BranchOrbitABCDefaultBaseCombinedFrontier` are
diagnostic packages.  This file exposes their public no-go theorems by
collapsing each wrapper to `RemainingNonRepresentationFrontierAfterDefaultBase`
and then delegating to the existing component, linear-character, eigenspace,
or fixed-star no-go theorem.
-/

namespace Moore57

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

private theorem no_combinedDefaultBaseFrontier_of_components
    (h : D19ActsOnMoore57 V Γ)
    {Frontier : Type*}
    (collapse : Frontier → RemainingNonRepresentationFrontierAfterDefaultBase h) :
    ¬ ∃ _representationComponents : RemainingRepresentationComponents h,
        Nonempty Frontier := by
  rintro ⟨representationComponents, ⟨frontier⟩⟩
  exact no_remainingNonRepresentationFrontierAfterDefaultBase_of_components h
    ⟨representationComponents, ⟨collapse frontier⟩⟩

private theorem no_combinedDefaultBaseFrontier_of_linearCharacterAndCounts
    (h : D19ActsOnMoore57 V Γ)
    {Frontier : Type*}
    (collapse : Frontier → RemainingNonRepresentationFrontierAfterDefaultBase h)
    (alpha beta gamma : ℕ)
    (minus8_trivial_nonneg : alpha ≤ 113)
    (minus8_sign_nonneg : beta ≤ 58)
    (hlin : ∀ g : DihedralGroup 19,
      Matrix.trace (E7Matrix Γ * permMatrix (h.smulEquiv g)) =
        (d19LinearCharacter alpha beta gamma g : ℚ))
    {d : ZMod 19}
    (ha0 : fixedVertexCount (h.smulEquiv (DihedralGroup.sr d)) = 56)
    (ha1 : adjacentMovedCount Γ (h.smulEquiv (DihedralGroup.sr d)) = 112) :
    ¬ Nonempty Frontier := by
  rintro ⟨frontier⟩
  exact
    no_remainingNonRepresentationFrontierAfterDefaultBase_of_linearCharacterAndCounts
      h alpha beta gamma minus8_trivial_nonneg minus8_sign_nonneg hlin ha0 ha1
      ⟨collapse frontier⟩

private theorem no_combinedDefaultBaseFrontier_of_eigenspaceCharactersAndCounts
    (h : D19ActsOnMoore57 V Γ)
    {Frontier : Type*}
    (collapse : Frontier → RemainingNonRepresentationFrontierAfterDefaultBase h)
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
    ¬ Nonempty Frontier := by
  rintro ⟨frontier⟩
  exact
    no_remainingNonRepresentationFrontierAfterDefaultBase_of_eigenspaceCharactersAndCounts
      h alpha beta gamma A B C h7 hMinus8 hreflection_a0 hrotation_a0
      hreflection_a1
      ⟨collapse frontier⟩

private theorem no_combinedDefaultBaseFrontier_of_eigenspaceCharactersAndFixedStar55
    (h : D19ActsOnMoore57 V Γ)
    {Frontier : Type*}
    (collapse : Frontier → RemainingNonRepresentationFrontierAfterDefaultBase h)
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
    ¬ Nonempty Frontier := by
  rintro ⟨frontier⟩
  exact
    no_remainingNonRepresentationFrontierAfterDefaultBase_of_eigenspaceCharactersAndFixedStar55
      h alpha beta gamma A B C h7 hMinus8 hStar hrotation_a0
      ⟨collapse frontier⟩

/-- Component-level no-go for the lean-aware endpoint-obstruction wrapper. -/
theorem no_remainingNonRepresentationFrontierAfterDefaultBaseLeanAwareEndpointObstruction_of_components
    (h : D19ActsOnMoore57 V Γ) :
    ¬ ∃ _representationComponents : RemainingRepresentationComponents h,
        Nonempty
          (RemainingNonRepresentationFrontierAfterDefaultBaseLeanAwareEndpointObstruction h) :=
  no_combinedDefaultBaseFrontier_of_components
    (h := h)
    (Frontier :=
      RemainingNonRepresentationFrontierAfterDefaultBaseLeanAwareEndpointObstruction h)
    RemainingNonRepresentationFrontierAfterDefaultBaseLeanAwareEndpointObstruction.toRemainingNonRepresentationFrontierAfterDefaultBase

/-- Component-level no-go for the A-fixing singleton endpoint-obstruction wrapper. -/
theorem no_remainingNonRepresentationFrontierAfterDefaultBaseAFixingSingletonEndpointObstruction_of_components
    (h : D19ActsOnMoore57 V Γ) :
    ¬ ∃ _representationComponents : RemainingRepresentationComponents h,
        Nonempty
          (RemainingNonRepresentationFrontierAfterDefaultBaseAFixingSingletonEndpointObstruction h) :=
  no_combinedDefaultBaseFrontier_of_components
    (h := h)
    (Frontier :=
      RemainingNonRepresentationFrontierAfterDefaultBaseAFixingSingletonEndpointObstruction h)
    RemainingNonRepresentationFrontierAfterDefaultBaseAFixingSingletonEndpointObstruction.toRemainingNonRepresentationFrontierAfterDefaultBase

/-- Component-level no-go for the A-fixing doubling endpoint-obstruction wrapper. -/
theorem no_remainingNonRepresentationFrontierAfterDefaultBaseAFixingDoublingEndpointObstruction_of_components
    (h : D19ActsOnMoore57 V Γ) :
    ¬ ∃ _representationComponents : RemainingRepresentationComponents h,
        Nonempty
          (RemainingNonRepresentationFrontierAfterDefaultBaseAFixingDoublingEndpointObstruction h) :=
  no_combinedDefaultBaseFrontier_of_components
    (h := h)
    (Frontier :=
      RemainingNonRepresentationFrontierAfterDefaultBaseAFixingDoublingEndpointObstruction h)
    RemainingNonRepresentationFrontierAfterDefaultBaseAFixingDoublingEndpointObstruction.toRemainingNonRepresentationFrontierAfterDefaultBase

/-- Component-level no-go for the fixed-star-local singleton endpoint wrapper. -/
theorem no_remainingNonRepresentationFrontierAfterDefaultBaseFixedStarLocalSingletonEndpointObstruction_of_components
    (h : D19ActsOnMoore57 V Γ) :
    ¬ ∃ _representationComponents : RemainingRepresentationComponents h,
        Nonempty
          (RemainingNonRepresentationFrontierAfterDefaultBaseFixedStarLocalSingletonEndpointObstruction h) :=
  no_combinedDefaultBaseFrontier_of_components
    (h := h)
    (Frontier :=
      RemainingNonRepresentationFrontierAfterDefaultBaseFixedStarLocalSingletonEndpointObstruction h)
    RemainingNonRepresentationFrontierAfterDefaultBaseFixedStarLocalSingletonEndpointObstruction.toRemainingNonRepresentationFrontierAfterDefaultBase

/-- Component-level no-go for the action-level singleton endpoint-obstruction wrapper. -/
theorem no_remainingNonRepresentationFrontierAfterDefaultBaseActionLevelSingletonEndpointObstruction_of_components
    (h : D19ActsOnMoore57 V Γ) :
    ¬ ∃ _representationComponents : RemainingRepresentationComponents h,
        Nonempty
          (RemainingNonRepresentationFrontierAfterDefaultBaseActionLevelSingletonEndpointObstruction h) :=
  no_combinedDefaultBaseFrontier_of_components
    (h := h)
    (Frontier :=
      RemainingNonRepresentationFrontierAfterDefaultBaseActionLevelSingletonEndpointObstruction h)
    RemainingNonRepresentationFrontierAfterDefaultBaseActionLevelSingletonEndpointObstruction.toRemainingNonRepresentationFrontierAfterDefaultBase

/-- Component-level no-go for the action-level doubling endpoint-obstruction wrapper. -/
theorem no_remainingNonRepresentationFrontierAfterDefaultBaseActionLevelDoublingEndpointObstruction_of_components
    (h : D19ActsOnMoore57 V Γ) :
    ¬ ∃ _representationComponents : RemainingRepresentationComponents h,
        Nonempty
          (RemainingNonRepresentationFrontierAfterDefaultBaseActionLevelDoublingEndpointObstruction h) :=
  no_combinedDefaultBaseFrontier_of_components
    (h := h)
    (Frontier :=
      RemainingNonRepresentationFrontierAfterDefaultBaseActionLevelDoublingEndpointObstruction h)
    RemainingNonRepresentationFrontierAfterDefaultBaseActionLevelDoublingEndpointObstruction.toRemainingNonRepresentationFrontierAfterDefaultBase

/-- Linear-character/count no-go for the lean-aware endpoint-obstruction wrapper. -/
theorem no_remainingNonRepresentationFrontierAfterDefaultBaseLeanAwareEndpointObstruction_of_linearCharacterAndCounts
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
        (RemainingNonRepresentationFrontierAfterDefaultBaseLeanAwareEndpointObstruction h) :=
  no_combinedDefaultBaseFrontier_of_linearCharacterAndCounts
    (h := h)
    (Frontier :=
      RemainingNonRepresentationFrontierAfterDefaultBaseLeanAwareEndpointObstruction h)
    RemainingNonRepresentationFrontierAfterDefaultBaseLeanAwareEndpointObstruction.toRemainingNonRepresentationFrontierAfterDefaultBase
    alpha beta gamma minus8_trivial_nonneg minus8_sign_nonneg hlin ha0 ha1

/-- Linear-character/count no-go for the A-fixing singleton endpoint-obstruction wrapper. -/
theorem no_remainingNonRepresentationFrontierAfterDefaultBaseAFixingSingletonEndpointObstruction_of_linearCharacterAndCounts
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
        (RemainingNonRepresentationFrontierAfterDefaultBaseAFixingSingletonEndpointObstruction h) :=
  no_combinedDefaultBaseFrontier_of_linearCharacterAndCounts
    (h := h)
    (Frontier :=
      RemainingNonRepresentationFrontierAfterDefaultBaseAFixingSingletonEndpointObstruction h)
    RemainingNonRepresentationFrontierAfterDefaultBaseAFixingSingletonEndpointObstruction.toRemainingNonRepresentationFrontierAfterDefaultBase
    alpha beta gamma minus8_trivial_nonneg minus8_sign_nonneg hlin ha0 ha1

/-- Linear-character/count no-go for the A-fixing doubling endpoint-obstruction wrapper. -/
theorem no_remainingNonRepresentationFrontierAfterDefaultBaseAFixingDoublingEndpointObstruction_of_linearCharacterAndCounts
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
        (RemainingNonRepresentationFrontierAfterDefaultBaseAFixingDoublingEndpointObstruction h) :=
  no_combinedDefaultBaseFrontier_of_linearCharacterAndCounts
    (h := h)
    (Frontier :=
      RemainingNonRepresentationFrontierAfterDefaultBaseAFixingDoublingEndpointObstruction h)
    RemainingNonRepresentationFrontierAfterDefaultBaseAFixingDoublingEndpointObstruction.toRemainingNonRepresentationFrontierAfterDefaultBase
    alpha beta gamma minus8_trivial_nonneg minus8_sign_nonneg hlin ha0 ha1

/-- Linear-character/count no-go for the fixed-star-local singleton endpoint wrapper. -/
theorem no_remainingNonRepresentationFrontierAfterDefaultBaseFixedStarLocalSingletonEndpointObstruction_of_linearCharacterAndCounts
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
        (RemainingNonRepresentationFrontierAfterDefaultBaseFixedStarLocalSingletonEndpointObstruction h) :=
  no_combinedDefaultBaseFrontier_of_linearCharacterAndCounts
    (h := h)
    (Frontier :=
      RemainingNonRepresentationFrontierAfterDefaultBaseFixedStarLocalSingletonEndpointObstruction h)
    RemainingNonRepresentationFrontierAfterDefaultBaseFixedStarLocalSingletonEndpointObstruction.toRemainingNonRepresentationFrontierAfterDefaultBase
    alpha beta gamma minus8_trivial_nonneg minus8_sign_nonneg hlin ha0 ha1

/-- Linear-character/count no-go for the action-level singleton endpoint-obstruction wrapper. -/
theorem no_remainingNonRepresentationFrontierAfterDefaultBaseActionLevelSingletonEndpointObstruction_of_linearCharacterAndCounts
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
        (RemainingNonRepresentationFrontierAfterDefaultBaseActionLevelSingletonEndpointObstruction h) :=
  no_combinedDefaultBaseFrontier_of_linearCharacterAndCounts
    (h := h)
    (Frontier :=
      RemainingNonRepresentationFrontierAfterDefaultBaseActionLevelSingletonEndpointObstruction h)
    RemainingNonRepresentationFrontierAfterDefaultBaseActionLevelSingletonEndpointObstruction.toRemainingNonRepresentationFrontierAfterDefaultBase
    alpha beta gamma minus8_trivial_nonneg minus8_sign_nonneg hlin ha0 ha1

/-- Linear-character/count no-go for the action-level doubling endpoint-obstruction wrapper. -/
theorem no_remainingNonRepresentationFrontierAfterDefaultBaseActionLevelDoublingEndpointObstruction_of_linearCharacterAndCounts
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
        (RemainingNonRepresentationFrontierAfterDefaultBaseActionLevelDoublingEndpointObstruction h) :=
  no_combinedDefaultBaseFrontier_of_linearCharacterAndCounts
    (h := h)
    (Frontier :=
      RemainingNonRepresentationFrontierAfterDefaultBaseActionLevelDoublingEndpointObstruction h)
    RemainingNonRepresentationFrontierAfterDefaultBaseActionLevelDoublingEndpointObstruction.toRemainingNonRepresentationFrontierAfterDefaultBase
    alpha beta gamma minus8_trivial_nonneg minus8_sign_nonneg hlin ha0 ha1

/-- Eigenspace-character/count no-go for the lean-aware endpoint-obstruction wrapper. -/
theorem no_remainingNonRepresentationFrontierAfterDefaultBaseLeanAwareEndpointObstruction_of_eigenspaceCharactersAndCounts
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
        (RemainingNonRepresentationFrontierAfterDefaultBaseLeanAwareEndpointObstruction h) :=
  no_combinedDefaultBaseFrontier_of_eigenspaceCharactersAndCounts
    (h := h)
    (Frontier :=
      RemainingNonRepresentationFrontierAfterDefaultBaseLeanAwareEndpointObstruction h)
    RemainingNonRepresentationFrontierAfterDefaultBaseLeanAwareEndpointObstruction.toRemainingNonRepresentationFrontierAfterDefaultBase
    alpha beta gamma A B C h7 hMinus8 hreflection_a0 hrotation_a0 hreflection_a1

/-- Eigenspace-character/count no-go for the A-fixing singleton endpoint-obstruction wrapper. -/
theorem no_remainingNonRepresentationFrontierAfterDefaultBaseAFixingSingletonEndpointObstruction_of_eigenspaceCharactersAndCounts
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
        (RemainingNonRepresentationFrontierAfterDefaultBaseAFixingSingletonEndpointObstruction h) :=
  no_combinedDefaultBaseFrontier_of_eigenspaceCharactersAndCounts
    (h := h)
    (Frontier :=
      RemainingNonRepresentationFrontierAfterDefaultBaseAFixingSingletonEndpointObstruction h)
    RemainingNonRepresentationFrontierAfterDefaultBaseAFixingSingletonEndpointObstruction.toRemainingNonRepresentationFrontierAfterDefaultBase
    alpha beta gamma A B C h7 hMinus8 hreflection_a0 hrotation_a0 hreflection_a1

/-- Eigenspace-character/count no-go for the A-fixing doubling endpoint-obstruction wrapper. -/
theorem no_remainingNonRepresentationFrontierAfterDefaultBaseAFixingDoublingEndpointObstruction_of_eigenspaceCharactersAndCounts
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
        (RemainingNonRepresentationFrontierAfterDefaultBaseAFixingDoublingEndpointObstruction h) :=
  no_combinedDefaultBaseFrontier_of_eigenspaceCharactersAndCounts
    (h := h)
    (Frontier :=
      RemainingNonRepresentationFrontierAfterDefaultBaseAFixingDoublingEndpointObstruction h)
    RemainingNonRepresentationFrontierAfterDefaultBaseAFixingDoublingEndpointObstruction.toRemainingNonRepresentationFrontierAfterDefaultBase
    alpha beta gamma A B C h7 hMinus8 hreflection_a0 hrotation_a0 hreflection_a1

/-- Eigenspace-character/count no-go for the fixed-star-local singleton endpoint wrapper. -/
theorem no_remainingNonRepresentationFrontierAfterDefaultBaseFixedStarLocalSingletonEndpointObstruction_of_eigenspaceCharactersAndCounts
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
        (RemainingNonRepresentationFrontierAfterDefaultBaseFixedStarLocalSingletonEndpointObstruction h) :=
  no_combinedDefaultBaseFrontier_of_eigenspaceCharactersAndCounts
    (h := h)
    (Frontier :=
      RemainingNonRepresentationFrontierAfterDefaultBaseFixedStarLocalSingletonEndpointObstruction h)
    RemainingNonRepresentationFrontierAfterDefaultBaseFixedStarLocalSingletonEndpointObstruction.toRemainingNonRepresentationFrontierAfterDefaultBase
    alpha beta gamma A B C h7 hMinus8 hreflection_a0 hrotation_a0 hreflection_a1

/-- Eigenspace-character/count no-go for the action-level singleton endpoint-obstruction wrapper. -/
theorem no_remainingNonRepresentationFrontierAfterDefaultBaseActionLevelSingletonEndpointObstruction_of_eigenspaceCharactersAndCounts
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
        (RemainingNonRepresentationFrontierAfterDefaultBaseActionLevelSingletonEndpointObstruction h) :=
  no_combinedDefaultBaseFrontier_of_eigenspaceCharactersAndCounts
    (h := h)
    (Frontier :=
      RemainingNonRepresentationFrontierAfterDefaultBaseActionLevelSingletonEndpointObstruction h)
    RemainingNonRepresentationFrontierAfterDefaultBaseActionLevelSingletonEndpointObstruction.toRemainingNonRepresentationFrontierAfterDefaultBase
    alpha beta gamma A B C h7 hMinus8 hreflection_a0 hrotation_a0 hreflection_a1

/-- Eigenspace-character/count no-go for the action-level doubling endpoint-obstruction wrapper. -/
theorem no_remainingNonRepresentationFrontierAfterDefaultBaseActionLevelDoublingEndpointObstruction_of_eigenspaceCharactersAndCounts
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
        (RemainingNonRepresentationFrontierAfterDefaultBaseActionLevelDoublingEndpointObstruction h) :=
  no_combinedDefaultBaseFrontier_of_eigenspaceCharactersAndCounts
    (h := h)
    (Frontier :=
      RemainingNonRepresentationFrontierAfterDefaultBaseActionLevelDoublingEndpointObstruction h)
    RemainingNonRepresentationFrontierAfterDefaultBaseActionLevelDoublingEndpointObstruction.toRemainingNonRepresentationFrontierAfterDefaultBase
    alpha beta gamma A B C h7 hMinus8 hreflection_a0 hrotation_a0 hreflection_a1

/-- Fixed-star/eigenspace no-go for the lean-aware endpoint-obstruction wrapper. -/
theorem no_remainingNonRepresentationFrontierAfterDefaultBaseLeanAwareEndpointObstruction_of_eigenspaceCharactersAndFixedStar55
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
        (RemainingNonRepresentationFrontierAfterDefaultBaseLeanAwareEndpointObstruction h) :=
  no_combinedDefaultBaseFrontier_of_eigenspaceCharactersAndFixedStar55
    (h := h)
    (Frontier :=
      RemainingNonRepresentationFrontierAfterDefaultBaseLeanAwareEndpointObstruction h)
    RemainingNonRepresentationFrontierAfterDefaultBaseLeanAwareEndpointObstruction.toRemainingNonRepresentationFrontierAfterDefaultBase
    alpha beta gamma A B C h7 hMinus8 hStar hrotation_a0

/-- Fixed-star/eigenspace no-go for the A-fixing singleton endpoint-obstruction wrapper. -/
theorem no_remainingNonRepresentationFrontierAfterDefaultBaseAFixingSingletonEndpointObstruction_of_eigenspaceCharactersAndFixedStar55
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
        (RemainingNonRepresentationFrontierAfterDefaultBaseAFixingSingletonEndpointObstruction h) :=
  no_combinedDefaultBaseFrontier_of_eigenspaceCharactersAndFixedStar55
    (h := h)
    (Frontier :=
      RemainingNonRepresentationFrontierAfterDefaultBaseAFixingSingletonEndpointObstruction h)
    RemainingNonRepresentationFrontierAfterDefaultBaseAFixingSingletonEndpointObstruction.toRemainingNonRepresentationFrontierAfterDefaultBase
    alpha beta gamma A B C h7 hMinus8 hStar hrotation_a0

/-- Fixed-star/eigenspace no-go for the A-fixing doubling endpoint-obstruction wrapper. -/
theorem no_remainingNonRepresentationFrontierAfterDefaultBaseAFixingDoublingEndpointObstruction_of_eigenspaceCharactersAndFixedStar55
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
        (RemainingNonRepresentationFrontierAfterDefaultBaseAFixingDoublingEndpointObstruction h) :=
  no_combinedDefaultBaseFrontier_of_eigenspaceCharactersAndFixedStar55
    (h := h)
    (Frontier :=
      RemainingNonRepresentationFrontierAfterDefaultBaseAFixingDoublingEndpointObstruction h)
    RemainingNonRepresentationFrontierAfterDefaultBaseAFixingDoublingEndpointObstruction.toRemainingNonRepresentationFrontierAfterDefaultBase
    alpha beta gamma A B C h7 hMinus8 hStar hrotation_a0

/-- Fixed-star/eigenspace no-go for the fixed-star-local singleton endpoint wrapper. -/
theorem no_remainingNonRepresentationFrontierAfterDefaultBaseFixedStarLocalSingletonEndpointObstruction_of_eigenspaceCharactersAndFixedStar55
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
        (RemainingNonRepresentationFrontierAfterDefaultBaseFixedStarLocalSingletonEndpointObstruction h) :=
  no_combinedDefaultBaseFrontier_of_eigenspaceCharactersAndFixedStar55
    (h := h)
    (Frontier :=
      RemainingNonRepresentationFrontierAfterDefaultBaseFixedStarLocalSingletonEndpointObstruction h)
    RemainingNonRepresentationFrontierAfterDefaultBaseFixedStarLocalSingletonEndpointObstruction.toRemainingNonRepresentationFrontierAfterDefaultBase
    alpha beta gamma A B C h7 hMinus8 hStar hrotation_a0

/-- Fixed-star/eigenspace no-go for the action-level singleton endpoint-obstruction wrapper. -/
theorem no_remainingNonRepresentationFrontierAfterDefaultBaseActionLevelSingletonEndpointObstruction_of_eigenspaceCharactersAndFixedStar55
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
        (RemainingNonRepresentationFrontierAfterDefaultBaseActionLevelSingletonEndpointObstruction h) :=
  no_combinedDefaultBaseFrontier_of_eigenspaceCharactersAndFixedStar55
    (h := h)
    (Frontier :=
      RemainingNonRepresentationFrontierAfterDefaultBaseActionLevelSingletonEndpointObstruction h)
    RemainingNonRepresentationFrontierAfterDefaultBaseActionLevelSingletonEndpointObstruction.toRemainingNonRepresentationFrontierAfterDefaultBase
    alpha beta gamma A B C h7 hMinus8 hStar hrotation_a0

/-- Fixed-star/eigenspace no-go for the action-level doubling endpoint-obstruction wrapper. -/
theorem no_remainingNonRepresentationFrontierAfterDefaultBaseActionLevelDoublingEndpointObstruction_of_eigenspaceCharactersAndFixedStar55
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
        (RemainingNonRepresentationFrontierAfterDefaultBaseActionLevelDoublingEndpointObstruction h) :=
  no_combinedDefaultBaseFrontier_of_eigenspaceCharactersAndFixedStar55
    (h := h)
    (Frontier :=
      RemainingNonRepresentationFrontierAfterDefaultBaseActionLevelDoublingEndpointObstruction h)
    RemainingNonRepresentationFrontierAfterDefaultBaseActionLevelDoublingEndpointObstruction.toRemainingNonRepresentationFrontierAfterDefaultBase
    alpha beta gamma A B C h7 hMinus8 hStar hrotation_a0

end

end Moore57

/-!
# Auto-rotation no-go surfaces for combined default-base wrappers

The combined-wrapper no-go theorems in
`D19DefaultBaseCombinedFrontierNoGo` consume the standard nontrivial-rotation
fixed-count hypothesis explicitly.  This file removes that argument by using
`D19ActsOnMoore57.rotationFixedCountOne_smulEquiv`.
-/

namespace Moore57

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- Eigenspace-character/reflection-count no-go for the lean-aware
endpoint-obstruction wrapper, with rotation counts supplied automatically. -/
theorem no_remainingNonRepresentationFrontierAfterDefaultBaseLeanAwareEndpointObstruction_of_eigenspaceCharactersAndReflectionCounts
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
        (RemainingNonRepresentationFrontierAfterDefaultBaseLeanAwareEndpointObstruction h) :=
  no_remainingNonRepresentationFrontierAfterDefaultBaseLeanAwareEndpointObstruction_of_eigenspaceCharactersAndCounts
    h alpha beta gamma A B C h7 hMinus8 hreflection_a0
    (D19ActsOnMoore57.rotationFixedCountOne_smulEquiv h) hreflection_a1

/-- Eigenspace-character/reflection-count no-go for the A-fixing singleton
endpoint-obstruction wrapper, with rotation counts supplied automatically. -/
theorem no_remainingNonRepresentationFrontierAfterDefaultBaseAFixingSingletonEndpointObstruction_of_eigenspaceCharactersAndReflectionCounts
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
        (RemainingNonRepresentationFrontierAfterDefaultBaseAFixingSingletonEndpointObstruction h) :=
  no_remainingNonRepresentationFrontierAfterDefaultBaseAFixingSingletonEndpointObstruction_of_eigenspaceCharactersAndCounts
    h alpha beta gamma A B C h7 hMinus8 hreflection_a0
    (D19ActsOnMoore57.rotationFixedCountOne_smulEquiv h) hreflection_a1

/-- Eigenspace-character/reflection-count no-go for the A-fixing doubling
endpoint-obstruction wrapper, with rotation counts supplied automatically. -/
theorem no_remainingNonRepresentationFrontierAfterDefaultBaseAFixingDoublingEndpointObstruction_of_eigenspaceCharactersAndReflectionCounts
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
        (RemainingNonRepresentationFrontierAfterDefaultBaseAFixingDoublingEndpointObstruction h) :=
  no_remainingNonRepresentationFrontierAfterDefaultBaseAFixingDoublingEndpointObstruction_of_eigenspaceCharactersAndCounts
    h alpha beta gamma A B C h7 hMinus8 hreflection_a0
    (D19ActsOnMoore57.rotationFixedCountOne_smulEquiv h) hreflection_a1

/-- Eigenspace-character/reflection-count no-go for the fixed-star-local
singleton endpoint wrapper, with rotation counts supplied automatically. -/
theorem no_remainingNonRepresentationFrontierAfterDefaultBaseFixedStarLocalSingletonEndpointObstruction_of_eigenspaceCharactersAndReflectionCounts
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
        (RemainingNonRepresentationFrontierAfterDefaultBaseFixedStarLocalSingletonEndpointObstruction h) :=
  no_remainingNonRepresentationFrontierAfterDefaultBaseFixedStarLocalSingletonEndpointObstruction_of_eigenspaceCharactersAndCounts
    h alpha beta gamma A B C h7 hMinus8 hreflection_a0
    (D19ActsOnMoore57.rotationFixedCountOne_smulEquiv h) hreflection_a1

/-- Eigenspace-character/reflection-count no-go for the action-level singleton
endpoint-obstruction wrapper, with rotation counts supplied automatically. -/
theorem no_remainingNonRepresentationFrontierAfterDefaultBaseActionLevelSingletonEndpointObstruction_of_eigenspaceCharactersAndReflectionCounts
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
        (RemainingNonRepresentationFrontierAfterDefaultBaseActionLevelSingletonEndpointObstruction h) :=
  no_remainingNonRepresentationFrontierAfterDefaultBaseActionLevelSingletonEndpointObstruction_of_eigenspaceCharactersAndCounts
    h alpha beta gamma A B C h7 hMinus8 hreflection_a0
    (D19ActsOnMoore57.rotationFixedCountOne_smulEquiv h) hreflection_a1

/-- Eigenspace-character/reflection-count no-go for the action-level doubling
endpoint-obstruction wrapper, with rotation counts supplied automatically. -/
theorem no_remainingNonRepresentationFrontierAfterDefaultBaseActionLevelDoublingEndpointObstruction_of_eigenspaceCharactersAndReflectionCounts
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
        (RemainingNonRepresentationFrontierAfterDefaultBaseActionLevelDoublingEndpointObstruction h) :=
  no_remainingNonRepresentationFrontierAfterDefaultBaseActionLevelDoublingEndpointObstruction_of_eigenspaceCharactersAndCounts
    h alpha beta gamma A B C h7 hMinus8 hreflection_a0
    (D19ActsOnMoore57.rotationFixedCountOne_smulEquiv h) hreflection_a1

/-- Fixed-star/eigenspace no-go for the lean-aware endpoint-obstruction wrapper,
with rotation counts supplied automatically. -/
theorem no_remainingNonRepresentationFrontierAfterDefaultBaseLeanAwareEndpointObstruction_of_eigenspaceCharactersAndFixedStar55_autoRotation
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
        (RemainingNonRepresentationFrontierAfterDefaultBaseLeanAwareEndpointObstruction h) :=
  no_remainingNonRepresentationFrontierAfterDefaultBaseLeanAwareEndpointObstruction_of_eigenspaceCharactersAndFixedStar55
    h alpha beta gamma A B C h7 hMinus8 hStar
    (D19ActsOnMoore57.rotationFixedCountOne_smulEquiv h)

/-- Fixed-star/eigenspace no-go for the A-fixing singleton endpoint-obstruction
wrapper, with rotation counts supplied automatically. -/
theorem no_remainingNonRepresentationFrontierAfterDefaultBaseAFixingSingletonEndpointObstruction_of_eigenspaceCharactersAndFixedStar55_autoRotation
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
        (RemainingNonRepresentationFrontierAfterDefaultBaseAFixingSingletonEndpointObstruction h) :=
  no_remainingNonRepresentationFrontierAfterDefaultBaseAFixingSingletonEndpointObstruction_of_eigenspaceCharactersAndFixedStar55
    h alpha beta gamma A B C h7 hMinus8 hStar
    (D19ActsOnMoore57.rotationFixedCountOne_smulEquiv h)

/-- Fixed-star/eigenspace no-go for the A-fixing doubling endpoint-obstruction
wrapper, with rotation counts supplied automatically. -/
theorem no_remainingNonRepresentationFrontierAfterDefaultBaseAFixingDoublingEndpointObstruction_of_eigenspaceCharactersAndFixedStar55_autoRotation
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
        (RemainingNonRepresentationFrontierAfterDefaultBaseAFixingDoublingEndpointObstruction h) :=
  no_remainingNonRepresentationFrontierAfterDefaultBaseAFixingDoublingEndpointObstruction_of_eigenspaceCharactersAndFixedStar55
    h alpha beta gamma A B C h7 hMinus8 hStar
    (D19ActsOnMoore57.rotationFixedCountOne_smulEquiv h)

/-- Fixed-star/eigenspace no-go for the fixed-star-local singleton endpoint
wrapper, with rotation counts supplied automatically. -/
theorem no_remainingNonRepresentationFrontierAfterDefaultBaseFixedStarLocalSingletonEndpointObstruction_of_eigenspaceCharactersAndFixedStar55_autoRotation
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
        (RemainingNonRepresentationFrontierAfterDefaultBaseFixedStarLocalSingletonEndpointObstruction h) :=
  no_remainingNonRepresentationFrontierAfterDefaultBaseFixedStarLocalSingletonEndpointObstruction_of_eigenspaceCharactersAndFixedStar55
    h alpha beta gamma A B C h7 hMinus8 hStar
    (D19ActsOnMoore57.rotationFixedCountOne_smulEquiv h)

/-- Fixed-star/eigenspace no-go for the action-level singleton endpoint-obstruction
wrapper, with rotation counts supplied automatically. -/
theorem no_remainingNonRepresentationFrontierAfterDefaultBaseActionLevelSingletonEndpointObstruction_of_eigenspaceCharactersAndFixedStar55_autoRotation
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
        (RemainingNonRepresentationFrontierAfterDefaultBaseActionLevelSingletonEndpointObstruction h) :=
  no_remainingNonRepresentationFrontierAfterDefaultBaseActionLevelSingletonEndpointObstruction_of_eigenspaceCharactersAndFixedStar55
    h alpha beta gamma A B C h7 hMinus8 hStar
    (D19ActsOnMoore57.rotationFixedCountOne_smulEquiv h)

/-- Fixed-star/eigenspace no-go for the action-level doubling endpoint-obstruction
wrapper, with rotation counts supplied automatically. -/
theorem no_remainingNonRepresentationFrontierAfterDefaultBaseActionLevelDoublingEndpointObstruction_of_eigenspaceCharactersAndFixedStar55_autoRotation
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
        (RemainingNonRepresentationFrontierAfterDefaultBaseActionLevelDoublingEndpointObstruction h) :=
  no_remainingNonRepresentationFrontierAfterDefaultBaseActionLevelDoublingEndpointObstruction_of_eigenspaceCharactersAndFixedStar55
    h alpha beta gamma A B C h7 hMinus8 hStar
    (D19ActsOnMoore57.rotationFixedCountOne_smulEquiv h)

end

end Moore57

