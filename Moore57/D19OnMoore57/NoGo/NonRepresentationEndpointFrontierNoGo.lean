import Moore57.D19OnMoore57.BranchOrbit.ABCNoAllEndpointAdjFrontier
import Moore57.D19OnMoore57.NoGo.NonRepresentationFrontierLinearNoGo
import Moore57.D19OnMoore57.NoGo.NonRepresentationFrontierEigenspaceNoGo

/-!
# Endpoint-wrapper no-go surfaces for the default-base frontier

This file exposes no-go theorems for the endpoint-obstruction diagnostic
wrappers introduced in `BranchOrbitABCNoAllEndpointAdjFrontier`.

No endpoint combinatorics is reproved here.  Each wrapper is collapsed to
`RemainingNonRepresentationFrontierAfterDefaultBase`, then the existing
component, linear-character, or eigenspace-character no-go theorem is applied.
-/

namespace Moore57

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- Component-level no-go for the endpoint non-adjacency witness wrapper. -/
theorem no_remainingNonRepresentationFrontierAfterDefaultBaseEndpointNonadjWitness_of_components
    (h : D19ActsOnMoore57 V Γ) :
    ¬ ∃ _representationComponents : RemainingRepresentationComponents h,
        Nonempty
          (RemainingNonRepresentationFrontierAfterDefaultBaseEndpointNonadjWitness h) := by
  rintro ⟨representationComponents, ⟨connector⟩⟩
  exact no_remainingNonRepresentationFrontierAfterDefaultBase_of_components h
    ⟨representationComponents,
      ⟨connector.toRemainingNonRepresentationFrontierAfterDefaultBase⟩⟩

/-- Component-level no-go for the pointwise endpoint non-adjacency wrapper. -/
theorem no_remainingNonRepresentationFrontierAfterDefaultBaseEndpointPointwiseNonadj_of_components
    (h : D19ActsOnMoore57 V Γ) :
    ¬ ∃ _representationComponents : RemainingRepresentationComponents h,
        Nonempty
          (RemainingNonRepresentationFrontierAfterDefaultBaseEndpointPointwiseNonadj h) := by
  rintro ⟨representationComponents, ⟨connector⟩⟩
  exact no_remainingNonRepresentationFrontierAfterDefaultBase_of_components h
    ⟨representationComponents,
      ⟨connector.toRemainingNonRepresentationFrontierAfterDefaultBase⟩⟩

/-- Component-level no-go for the endpoint-forces-fixed wrapper. -/
theorem no_remainingNonRepresentationFrontierAfterDefaultBaseEndpointAdjForcesAFixingFixed_of_components
    (h : D19ActsOnMoore57 V Γ) :
    ¬ ∃ _representationComponents : RemainingRepresentationComponents h,
        Nonempty
          (RemainingNonRepresentationFrontierAfterDefaultBaseEndpointAdjForcesAFixingFixed h) := by
  rintro ⟨representationComponents, ⟨connector⟩⟩
  exact no_remainingNonRepresentationFrontierAfterDefaultBase_of_components h
    ⟨representationComponents,
      ⟨connector.toRemainingNonRepresentationFrontierAfterDefaultBase⟩⟩

/-- Component-level no-go for the vertex-fixed endpoint-forces-fixed wrapper. -/
theorem no_remainingNonRepresentationFrontierAfterDefaultBaseEndpointAdjForcesAFixingVertexFixed_of_components
    (h : D19ActsOnMoore57 V Γ) :
    ¬ ∃ _representationComponents : RemainingRepresentationComponents h,
        Nonempty
          (RemainingNonRepresentationFrontierAfterDefaultBaseEndpointAdjForcesAFixingVertexFixed h) := by
  rintro ⟨representationComponents, ⟨connector⟩⟩
  exact no_remainingNonRepresentationFrontierAfterDefaultBase_of_components h
    ⟨representationComponents,
      ⟨connector.toRemainingNonRepresentationFrontierAfterDefaultBase⟩⟩

/-- Component-level no-go for the pair endpoint non-adjacency wrapper. -/
theorem no_remainingNonRepresentationFrontierAfterDefaultBasePairEndpointNonadj_of_components
    (h : D19ActsOnMoore57 V Γ) :
    ¬ ∃ _representationComponents : RemainingRepresentationComponents h,
        Nonempty
          (RemainingNonRepresentationFrontierAfterDefaultBasePairEndpointNonadj h) := by
  rintro ⟨representationComponents, ⟨connector⟩⟩
  exact no_remainingNonRepresentationFrontierAfterDefaultBase_of_components h
    ⟨representationComponents,
      ⟨connector.toRemainingNonRepresentationFrontierAfterDefaultBase⟩⟩

/-- Component-level no-go for the pair common-neighbor endpoint wrapper. -/
theorem no_remainingNonRepresentationFrontierAfterDefaultBasePairEndpointTwoCommonNeighbors_of_components
    (h : D19ActsOnMoore57 V Γ) :
    ¬ ∃ _representationComponents : RemainingRepresentationComponents h,
        Nonempty
          (RemainingNonRepresentationFrontierAfterDefaultBasePairEndpointTwoCommonNeighbors h) := by
  rintro ⟨representationComponents, ⟨connector⟩⟩
  exact no_remainingNonRepresentationFrontierAfterDefaultBase_of_components h
    ⟨representationComponents,
      ⟨connector.toRemainingNonRepresentationFrontierAfterDefaultBase⟩⟩

/-- Linear-character/count no-go for the endpoint non-adjacency witness wrapper. -/
theorem no_remainingNonRepresentationFrontierAfterDefaultBaseEndpointNonadjWitness_of_linearCharacterAndCounts
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
        (RemainingNonRepresentationFrontierAfterDefaultBaseEndpointNonadjWitness h) := by
  rintro ⟨connector⟩
  exact
    no_remainingNonRepresentationFrontierAfterDefaultBase_of_linearCharacterAndCounts
      h alpha beta gamma minus8_trivial_nonneg minus8_sign_nonneg hlin ha0 ha1
      ⟨connector.toRemainingNonRepresentationFrontierAfterDefaultBase⟩

/-- Linear-character/count no-go for the pointwise endpoint non-adjacency wrapper. -/
theorem no_remainingNonRepresentationFrontierAfterDefaultBaseEndpointPointwiseNonadj_of_linearCharacterAndCounts
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
        (RemainingNonRepresentationFrontierAfterDefaultBaseEndpointPointwiseNonadj h) := by
  rintro ⟨connector⟩
  exact
    no_remainingNonRepresentationFrontierAfterDefaultBase_of_linearCharacterAndCounts
      h alpha beta gamma minus8_trivial_nonneg minus8_sign_nonneg hlin ha0 ha1
      ⟨connector.toRemainingNonRepresentationFrontierAfterDefaultBase⟩

/-- Linear-character/count no-go for the endpoint-forces-fixed wrapper. -/
theorem no_remainingNonRepresentationFrontierAfterDefaultBaseEndpointAdjForcesAFixingFixed_of_linearCharacterAndCounts
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
        (RemainingNonRepresentationFrontierAfterDefaultBaseEndpointAdjForcesAFixingFixed h) := by
  rintro ⟨connector⟩
  exact
    no_remainingNonRepresentationFrontierAfterDefaultBase_of_linearCharacterAndCounts
      h alpha beta gamma minus8_trivial_nonneg minus8_sign_nonneg hlin ha0 ha1
      ⟨connector.toRemainingNonRepresentationFrontierAfterDefaultBase⟩

/-- Linear-character/count no-go for the vertex-fixed endpoint-forces-fixed wrapper. -/
theorem no_remainingNonRepresentationFrontierAfterDefaultBaseEndpointAdjForcesAFixingVertexFixed_of_linearCharacterAndCounts
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
        (RemainingNonRepresentationFrontierAfterDefaultBaseEndpointAdjForcesAFixingVertexFixed h) := by
  rintro ⟨connector⟩
  exact
    no_remainingNonRepresentationFrontierAfterDefaultBase_of_linearCharacterAndCounts
      h alpha beta gamma minus8_trivial_nonneg minus8_sign_nonneg hlin ha0 ha1
      ⟨connector.toRemainingNonRepresentationFrontierAfterDefaultBase⟩

/-- Linear-character/count no-go for the pair endpoint non-adjacency wrapper. -/
theorem no_remainingNonRepresentationFrontierAfterDefaultBasePairEndpointNonadj_of_linearCharacterAndCounts
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
        (RemainingNonRepresentationFrontierAfterDefaultBasePairEndpointNonadj h) := by
  rintro ⟨connector⟩
  exact
    no_remainingNonRepresentationFrontierAfterDefaultBase_of_linearCharacterAndCounts
      h alpha beta gamma minus8_trivial_nonneg minus8_sign_nonneg hlin ha0 ha1
      ⟨connector.toRemainingNonRepresentationFrontierAfterDefaultBase⟩

/-- Linear-character/count no-go for the pair common-neighbor endpoint wrapper. -/
theorem no_remainingNonRepresentationFrontierAfterDefaultBasePairEndpointTwoCommonNeighbors_of_linearCharacterAndCounts
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
        (RemainingNonRepresentationFrontierAfterDefaultBasePairEndpointTwoCommonNeighbors h) := by
  rintro ⟨connector⟩
  exact
    no_remainingNonRepresentationFrontierAfterDefaultBase_of_linearCharacterAndCounts
      h alpha beta gamma minus8_trivial_nonneg minus8_sign_nonneg hlin ha0 ha1
      ⟨connector.toRemainingNonRepresentationFrontierAfterDefaultBase⟩

/-- Eigenspace-character/count no-go for the endpoint non-adjacency witness wrapper. -/
theorem no_remainingNonRepresentationFrontierAfterDefaultBaseEndpointNonadjWitness_of_eigenspaceCharactersAndCounts
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
        (RemainingNonRepresentationFrontierAfterDefaultBaseEndpointNonadjWitness h) := by
  rintro ⟨connector⟩
  exact
    no_remainingNonRepresentationFrontierAfterDefaultBase_of_eigenspaceCharactersAndCounts
      h alpha beta gamma A B C h7 hMinus8 hreflection_a0 hrotation_a0
      hreflection_a1
      ⟨connector.toRemainingNonRepresentationFrontierAfterDefaultBase⟩

/-- Eigenspace-character/count no-go for the pointwise endpoint non-adjacency wrapper. -/
theorem no_remainingNonRepresentationFrontierAfterDefaultBaseEndpointPointwiseNonadj_of_eigenspaceCharactersAndCounts
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
        (RemainingNonRepresentationFrontierAfterDefaultBaseEndpointPointwiseNonadj h) := by
  rintro ⟨connector⟩
  exact
    no_remainingNonRepresentationFrontierAfterDefaultBase_of_eigenspaceCharactersAndCounts
      h alpha beta gamma A B C h7 hMinus8 hreflection_a0 hrotation_a0
      hreflection_a1
      ⟨connector.toRemainingNonRepresentationFrontierAfterDefaultBase⟩

/-- Eigenspace-character/count no-go for the endpoint-forces-fixed wrapper. -/
theorem no_remainingNonRepresentationFrontierAfterDefaultBaseEndpointAdjForcesAFixingFixed_of_eigenspaceCharactersAndCounts
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
        (RemainingNonRepresentationFrontierAfterDefaultBaseEndpointAdjForcesAFixingFixed h) := by
  rintro ⟨connector⟩
  exact
    no_remainingNonRepresentationFrontierAfterDefaultBase_of_eigenspaceCharactersAndCounts
      h alpha beta gamma A B C h7 hMinus8 hreflection_a0 hrotation_a0
      hreflection_a1
      ⟨connector.toRemainingNonRepresentationFrontierAfterDefaultBase⟩

/-- Eigenspace-character/count no-go for the vertex-fixed endpoint-forces-fixed wrapper. -/
theorem no_remainingNonRepresentationFrontierAfterDefaultBaseEndpointAdjForcesAFixingVertexFixed_of_eigenspaceCharactersAndCounts
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
        (RemainingNonRepresentationFrontierAfterDefaultBaseEndpointAdjForcesAFixingVertexFixed h) := by
  rintro ⟨connector⟩
  exact
    no_remainingNonRepresentationFrontierAfterDefaultBase_of_eigenspaceCharactersAndCounts
      h alpha beta gamma A B C h7 hMinus8 hreflection_a0 hrotation_a0
      hreflection_a1
      ⟨connector.toRemainingNonRepresentationFrontierAfterDefaultBase⟩

/-- Eigenspace-character/count no-go for the pair endpoint non-adjacency wrapper. -/
theorem no_remainingNonRepresentationFrontierAfterDefaultBasePairEndpointNonadj_of_eigenspaceCharactersAndCounts
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
        (RemainingNonRepresentationFrontierAfterDefaultBasePairEndpointNonadj h) := by
  rintro ⟨connector⟩
  exact
    no_remainingNonRepresentationFrontierAfterDefaultBase_of_eigenspaceCharactersAndCounts
      h alpha beta gamma A B C h7 hMinus8 hreflection_a0 hrotation_a0
      hreflection_a1
      ⟨connector.toRemainingNonRepresentationFrontierAfterDefaultBase⟩

/-- Eigenspace-character/count no-go for the pair common-neighbor endpoint wrapper. -/
theorem no_remainingNonRepresentationFrontierAfterDefaultBasePairEndpointTwoCommonNeighbors_of_eigenspaceCharactersAndCounts
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
        (RemainingNonRepresentationFrontierAfterDefaultBasePairEndpointTwoCommonNeighbors h) := by
  rintro ⟨connector⟩
  exact
    no_remainingNonRepresentationFrontierAfterDefaultBase_of_eigenspaceCharactersAndCounts
      h alpha beta gamma A B C h7 hMinus8 hreflection_a0 hrotation_a0
      hreflection_a1
      ⟨connector.toRemainingNonRepresentationFrontierAfterDefaultBase⟩

end

end Moore57
