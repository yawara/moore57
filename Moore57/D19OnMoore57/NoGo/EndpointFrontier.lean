import Moore57.D19OnMoore57.BranchOrbit.NoFrontier
import Moore57.D19OnMoore57.Involution.FixedStarA1
import Moore57.D19OnMoore57.NoGo.DefaultBaseCombinedFrontier
import Moore57.D19OnMoore57.NoGo.NonRepresentationFrontier
import Moore57.D19OnMoore57.Rotation.FixedCountOneFrontier

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

/-!
# Auto-rotation no-go surfaces for endpoint wrappers

This file removes the explicit rotation fixed-count argument from the
endpoint-wrapper eigenspace no-go theorems.  The rotation count is supplied by
the ambient `D19ActsOnMoore57.rotationFixedCountOne_smulEquiv` theorem.
-/

namespace Moore57

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- Endpoint non-adjacency wrapper no-go, with the rotation counts supplied by
the ambient action theorem. -/
theorem no_remainingNonRepresentationFrontierAfterDefaultBaseEndpointNonadjWitness_of_eigenspaceCharactersAndReflectionCounts
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
        (RemainingNonRepresentationFrontierAfterDefaultBaseEndpointNonadjWitness h) :=
  no_remainingNonRepresentationFrontierAfterDefaultBaseEndpointNonadjWitness_of_eigenspaceCharactersAndCounts
    h alpha beta gamma A B C h7 hMinus8 hreflection_a0
    (D19ActsOnMoore57.rotationFixedCountOne_smulEquiv h)
    hreflection_a1

/-- Pointwise endpoint non-adjacency wrapper no-go with automatic rotation
counts. -/
theorem no_remainingNonRepresentationFrontierAfterDefaultBaseEndpointPointwiseNonadj_of_eigenspaceCharactersAndReflectionCounts
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
        (RemainingNonRepresentationFrontierAfterDefaultBaseEndpointPointwiseNonadj h) :=
  no_remainingNonRepresentationFrontierAfterDefaultBaseEndpointPointwiseNonadj_of_eigenspaceCharactersAndCounts
    h alpha beta gamma A B C h7 hMinus8 hreflection_a0
    (D19ActsOnMoore57.rotationFixedCountOne_smulEquiv h)
    hreflection_a1

/-- Endpoint-forces-fixed wrapper no-go with automatic rotation counts. -/
theorem no_remainingNonRepresentationFrontierAfterDefaultBaseEndpointAdjForcesAFixingFixed_of_eigenspaceCharactersAndReflectionCounts
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
        (RemainingNonRepresentationFrontierAfterDefaultBaseEndpointAdjForcesAFixingFixed h) :=
  no_remainingNonRepresentationFrontierAfterDefaultBaseEndpointAdjForcesAFixingFixed_of_eigenspaceCharactersAndCounts
    h alpha beta gamma A B C h7 hMinus8 hreflection_a0
    (D19ActsOnMoore57.rotationFixedCountOne_smulEquiv h)
    hreflection_a1

/-- Vertex-fixed endpoint-forces-fixed wrapper no-go with automatic rotation
counts. -/
theorem no_remainingNonRepresentationFrontierAfterDefaultBaseEndpointAdjForcesAFixingVertexFixed_of_eigenspaceCharactersAndReflectionCounts
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
        (RemainingNonRepresentationFrontierAfterDefaultBaseEndpointAdjForcesAFixingVertexFixed h) :=
  no_remainingNonRepresentationFrontierAfterDefaultBaseEndpointAdjForcesAFixingVertexFixed_of_eigenspaceCharactersAndCounts
    h alpha beta gamma A B C h7 hMinus8 hreflection_a0
    (D19ActsOnMoore57.rotationFixedCountOne_smulEquiv h)
    hreflection_a1

/-- Pair endpoint non-adjacency wrapper no-go with automatic rotation counts. -/
theorem no_remainingNonRepresentationFrontierAfterDefaultBasePairEndpointNonadj_of_eigenspaceCharactersAndReflectionCounts
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
        (RemainingNonRepresentationFrontierAfterDefaultBasePairEndpointNonadj h) :=
  no_remainingNonRepresentationFrontierAfterDefaultBasePairEndpointNonadj_of_eigenspaceCharactersAndCounts
    h alpha beta gamma A B C h7 hMinus8 hreflection_a0
    (D19ActsOnMoore57.rotationFixedCountOne_smulEquiv h)
    hreflection_a1

/-- Pair common-neighbor endpoint wrapper no-go with automatic rotation counts. -/
theorem no_remainingNonRepresentationFrontierAfterDefaultBasePairEndpointTwoCommonNeighbors_of_eigenspaceCharactersAndReflectionCounts
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
        (RemainingNonRepresentationFrontierAfterDefaultBasePairEndpointTwoCommonNeighbors h) :=
  no_remainingNonRepresentationFrontierAfterDefaultBasePairEndpointTwoCommonNeighbors_of_eigenspaceCharactersAndCounts
    h alpha beta gamma A B C h7 hMinus8 hreflection_a0
    (D19ActsOnMoore57.rotationFixedCountOne_smulEquiv h)
    hreflection_a1

/-- Endpoint non-adjacency wrapper no-go from a fixed-star reflection witness,
with automatic rotation counts. -/
theorem no_remainingNonRepresentationFrontierAfterDefaultBaseEndpointNonadjWitness_of_eigenspaceCharactersAndFixedStar55_autoRotation
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
        (RemainingNonRepresentationFrontierAfterDefaultBaseEndpointNonadjWitness h) :=
  no_remainingNonRepresentationFrontierAfterDefaultBaseEndpointNonadjWitness_of_eigenspaceCharactersAndReflectionCounts
    h alpha beta gamma A B C h7 hMinus8
    (h.fixedVertexCount_reflection_eq_56_of_involutionFixedStar55 hStar)
    (h.adjacentMovedCount_reflection_eq_112 hStar)

/-- Pointwise endpoint non-adjacency wrapper no-go from a fixed-star reflection
witness, with automatic rotation counts. -/
theorem no_remainingNonRepresentationFrontierAfterDefaultBaseEndpointPointwiseNonadj_of_eigenspaceCharactersAndFixedStar55_autoRotation
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
        (RemainingNonRepresentationFrontierAfterDefaultBaseEndpointPointwiseNonadj h) :=
  no_remainingNonRepresentationFrontierAfterDefaultBaseEndpointPointwiseNonadj_of_eigenspaceCharactersAndReflectionCounts
    h alpha beta gamma A B C h7 hMinus8
    (h.fixedVertexCount_reflection_eq_56_of_involutionFixedStar55 hStar)
    (h.adjacentMovedCount_reflection_eq_112 hStar)

/-- Endpoint-forces-fixed wrapper no-go from a fixed-star reflection witness,
with automatic rotation counts. -/
theorem no_remainingNonRepresentationFrontierAfterDefaultBaseEndpointAdjForcesAFixingFixed_of_eigenspaceCharactersAndFixedStar55_autoRotation
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
        (RemainingNonRepresentationFrontierAfterDefaultBaseEndpointAdjForcesAFixingFixed h) :=
  no_remainingNonRepresentationFrontierAfterDefaultBaseEndpointAdjForcesAFixingFixed_of_eigenspaceCharactersAndReflectionCounts
    h alpha beta gamma A B C h7 hMinus8
    (h.fixedVertexCount_reflection_eq_56_of_involutionFixedStar55 hStar)
    (h.adjacentMovedCount_reflection_eq_112 hStar)

/-- Vertex-fixed endpoint-forces-fixed wrapper no-go from a fixed-star
reflection witness, with automatic rotation counts. -/
theorem no_remainingNonRepresentationFrontierAfterDefaultBaseEndpointAdjForcesAFixingVertexFixed_of_eigenspaceCharactersAndFixedStar55_autoRotation
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
        (RemainingNonRepresentationFrontierAfterDefaultBaseEndpointAdjForcesAFixingVertexFixed h) :=
  no_remainingNonRepresentationFrontierAfterDefaultBaseEndpointAdjForcesAFixingVertexFixed_of_eigenspaceCharactersAndReflectionCounts
    h alpha beta gamma A B C h7 hMinus8
    (h.fixedVertexCount_reflection_eq_56_of_involutionFixedStar55 hStar)
    (h.adjacentMovedCount_reflection_eq_112 hStar)

/-- Pair endpoint non-adjacency wrapper no-go from a fixed-star reflection
witness, with automatic rotation counts. -/
theorem no_remainingNonRepresentationFrontierAfterDefaultBasePairEndpointNonadj_of_eigenspaceCharactersAndFixedStar55_autoRotation
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
        (RemainingNonRepresentationFrontierAfterDefaultBasePairEndpointNonadj h) :=
  no_remainingNonRepresentationFrontierAfterDefaultBasePairEndpointNonadj_of_eigenspaceCharactersAndReflectionCounts
    h alpha beta gamma A B C h7 hMinus8
    (h.fixedVertexCount_reflection_eq_56_of_involutionFixedStar55 hStar)
    (h.adjacentMovedCount_reflection_eq_112 hStar)

/-- Pair common-neighbor endpoint wrapper no-go from a fixed-star reflection
witness, with automatic rotation counts. -/
theorem no_remainingNonRepresentationFrontierAfterDefaultBasePairEndpointTwoCommonNeighbors_of_eigenspaceCharactersAndFixedStar55_autoRotation
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
        (RemainingNonRepresentationFrontierAfterDefaultBasePairEndpointTwoCommonNeighbors h) :=
  no_remainingNonRepresentationFrontierAfterDefaultBasePairEndpointTwoCommonNeighbors_of_eigenspaceCharactersAndReflectionCounts
    h alpha beta gamma A B C h7 hMinus8
    (h.fixedVertexCount_reflection_eq_56_of_involutionFixedStar55 hStar)
    (h.adjacentMovedCount_reflection_eq_112 hStar)

end

end Moore57

/-!
# K155 no-go surfaces for endpoint and combined frontiers

This file exposes `K_{1,55}` versions of the endpoint and combined-wrapper
auto-rotation no-go theorems.  Each proof only converts the explicit
`InvolutionK155` witness to `InvolutionFixedStar55` and delegates to the
existing fixed-star theorem.
-/

namespace Moore57

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- Endpoint non-adjacency wrapper no-go from an explicit `K_{1,55}` reflection
witness, with automatic rotation counts. -/
theorem no_remainingNonRepresentationFrontierAfterDefaultBaseEndpointNonadjWitness_of_eigenspaceCharactersAndK155_autoRotation
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
        (RemainingNonRepresentationFrontierAfterDefaultBaseEndpointNonadjWitness h) :=
  no_remainingNonRepresentationFrontierAfterDefaultBaseEndpointNonadjWitness_of_eigenspaceCharactersAndFixedStar55_autoRotation
    h alpha beta gamma A B C h7 hMinus8
    (InvolutionK155.toInvolutionFixedStar55 h.isMoore hK)

/-- Pointwise endpoint non-adjacency wrapper no-go from an explicit `K_{1,55}`
reflection witness, with automatic rotation counts. -/
theorem no_remainingNonRepresentationFrontierAfterDefaultBaseEndpointPointwiseNonadj_of_eigenspaceCharactersAndK155_autoRotation
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
        (RemainingNonRepresentationFrontierAfterDefaultBaseEndpointPointwiseNonadj h) :=
  no_remainingNonRepresentationFrontierAfterDefaultBaseEndpointPointwiseNonadj_of_eigenspaceCharactersAndFixedStar55_autoRotation
    h alpha beta gamma A B C h7 hMinus8
    (InvolutionK155.toInvolutionFixedStar55 h.isMoore hK)

/-- Endpoint-forces-fixed wrapper no-go from an explicit `K_{1,55}` reflection
witness, with automatic rotation counts. -/
theorem no_remainingNonRepresentationFrontierAfterDefaultBaseEndpointAdjForcesAFixingFixed_of_eigenspaceCharactersAndK155_autoRotation
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
        (RemainingNonRepresentationFrontierAfterDefaultBaseEndpointAdjForcesAFixingFixed h) :=
  no_remainingNonRepresentationFrontierAfterDefaultBaseEndpointAdjForcesAFixingFixed_of_eigenspaceCharactersAndFixedStar55_autoRotation
    h alpha beta gamma A B C h7 hMinus8
    (InvolutionK155.toInvolutionFixedStar55 h.isMoore hK)

/-- Vertex-fixed endpoint-forces-fixed wrapper no-go from an explicit
`K_{1,55}` reflection witness, with automatic rotation counts. -/
theorem no_remainingNonRepresentationFrontierAfterDefaultBaseEndpointAdjForcesAFixingVertexFixed_of_eigenspaceCharactersAndK155_autoRotation
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
        (RemainingNonRepresentationFrontierAfterDefaultBaseEndpointAdjForcesAFixingVertexFixed h) :=
  no_remainingNonRepresentationFrontierAfterDefaultBaseEndpointAdjForcesAFixingVertexFixed_of_eigenspaceCharactersAndFixedStar55_autoRotation
    h alpha beta gamma A B C h7 hMinus8
    (InvolutionK155.toInvolutionFixedStar55 h.isMoore hK)

/-- Pair endpoint non-adjacency wrapper no-go from an explicit `K_{1,55}`
reflection witness, with automatic rotation counts. -/
theorem no_remainingNonRepresentationFrontierAfterDefaultBasePairEndpointNonadj_of_eigenspaceCharactersAndK155_autoRotation
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
        (RemainingNonRepresentationFrontierAfterDefaultBasePairEndpointNonadj h) :=
  no_remainingNonRepresentationFrontierAfterDefaultBasePairEndpointNonadj_of_eigenspaceCharactersAndFixedStar55_autoRotation
    h alpha beta gamma A B C h7 hMinus8
    (InvolutionK155.toInvolutionFixedStar55 h.isMoore hK)

/-- Pair common-neighbor endpoint wrapper no-go from an explicit `K_{1,55}`
reflection witness, with automatic rotation counts. -/
theorem no_remainingNonRepresentationFrontierAfterDefaultBasePairEndpointTwoCommonNeighbors_of_eigenspaceCharactersAndK155_autoRotation
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
        (RemainingNonRepresentationFrontierAfterDefaultBasePairEndpointTwoCommonNeighbors h) :=
  no_remainingNonRepresentationFrontierAfterDefaultBasePairEndpointTwoCommonNeighbors_of_eigenspaceCharactersAndFixedStar55_autoRotation
    h alpha beta gamma A B C h7 hMinus8
    (InvolutionK155.toInvolutionFixedStar55 h.isMoore hK)

/-- Combined lean-aware endpoint-obstruction wrapper no-go from an explicit
`K_{1,55}` reflection witness, with automatic rotation counts. -/
theorem no_remainingNonRepresentationFrontierAfterDefaultBaseLeanAwareEndpointObstruction_of_eigenspaceCharactersAndK155_autoRotation
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
        (RemainingNonRepresentationFrontierAfterDefaultBaseLeanAwareEndpointObstruction h) :=
  no_remainingNonRepresentationFrontierAfterDefaultBaseLeanAwareEndpointObstruction_of_eigenspaceCharactersAndFixedStar55_autoRotation
    h alpha beta gamma A B C h7 hMinus8
    (InvolutionK155.toInvolutionFixedStar55 h.isMoore hK)

/-- Combined A-fixing singleton endpoint-obstruction wrapper no-go from an
explicit `K_{1,55}` reflection witness, with automatic rotation counts. -/
theorem no_remainingNonRepresentationFrontierAfterDefaultBaseAFixingSingletonEndpointObstruction_of_eigenspaceCharactersAndK155_autoRotation
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
        (RemainingNonRepresentationFrontierAfterDefaultBaseAFixingSingletonEndpointObstruction h) :=
  no_remainingNonRepresentationFrontierAfterDefaultBaseAFixingSingletonEndpointObstruction_of_eigenspaceCharactersAndFixedStar55_autoRotation
    h alpha beta gamma A B C h7 hMinus8
    (InvolutionK155.toInvolutionFixedStar55 h.isMoore hK)

/-- Combined A-fixing doubling endpoint-obstruction wrapper no-go from an
explicit `K_{1,55}` reflection witness, with automatic rotation counts. -/
theorem no_remainingNonRepresentationFrontierAfterDefaultBaseAFixingDoublingEndpointObstruction_of_eigenspaceCharactersAndK155_autoRotation
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
        (RemainingNonRepresentationFrontierAfterDefaultBaseAFixingDoublingEndpointObstruction h) :=
  no_remainingNonRepresentationFrontierAfterDefaultBaseAFixingDoublingEndpointObstruction_of_eigenspaceCharactersAndFixedStar55_autoRotation
    h alpha beta gamma A B C h7 hMinus8
    (InvolutionK155.toInvolutionFixedStar55 h.isMoore hK)

/-- Combined fixed-star-local singleton endpoint-obstruction wrapper no-go
from an explicit `K_{1,55}` reflection witness, with automatic rotation
counts. -/
theorem no_remainingNonRepresentationFrontierAfterDefaultBaseFixedStarLocalSingletonEndpointObstruction_of_eigenspaceCharactersAndK155_autoRotation
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
        (RemainingNonRepresentationFrontierAfterDefaultBaseFixedStarLocalSingletonEndpointObstruction h) :=
  no_remainingNonRepresentationFrontierAfterDefaultBaseFixedStarLocalSingletonEndpointObstruction_of_eigenspaceCharactersAndFixedStar55_autoRotation
    h alpha beta gamma A B C h7 hMinus8
    (InvolutionK155.toInvolutionFixedStar55 h.isMoore hK)

/-- Combined action-level singleton endpoint-obstruction wrapper no-go from an
explicit `K_{1,55}` reflection witness, with automatic rotation counts. -/
theorem no_remainingNonRepresentationFrontierAfterDefaultBaseActionLevelSingletonEndpointObstruction_of_eigenspaceCharactersAndK155_autoRotation
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
        (RemainingNonRepresentationFrontierAfterDefaultBaseActionLevelSingletonEndpointObstruction h) :=
  no_remainingNonRepresentationFrontierAfterDefaultBaseActionLevelSingletonEndpointObstruction_of_eigenspaceCharactersAndFixedStar55_autoRotation
    h alpha beta gamma A B C h7 hMinus8
    (InvolutionK155.toInvolutionFixedStar55 h.isMoore hK)

/-- Combined action-level doubling endpoint-obstruction wrapper no-go from an
explicit `K_{1,55}` reflection witness, with automatic rotation counts. -/
theorem no_remainingNonRepresentationFrontierAfterDefaultBaseActionLevelDoublingEndpointObstruction_of_eigenspaceCharactersAndK155_autoRotation
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
        (RemainingNonRepresentationFrontierAfterDefaultBaseActionLevelDoublingEndpointObstruction h) :=
  no_remainingNonRepresentationFrontierAfterDefaultBaseActionLevelDoublingEndpointObstruction_of_eigenspaceCharactersAndFixedStar55_autoRotation
    h alpha beta gamma A B C h7 hMinus8
    (InvolutionK155.toInvolutionFixedStar55 h.isMoore hK)

end

end Moore57

/-!
# Concise K155 aliases for endpoint frontiers

This file gives short raw-action-style names to the endpoint-only `K_{1,55}`
no-go surfaces.  The proofs only delegate to the existing endpoint K155
theorems.
-/

namespace Moore57

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

abbrev RemainingEndpointNonadjWitnessFrontierAfterDefaultBase
    (h : D19ActsOnMoore57 V Γ) : Prop :=
  Nonempty
    (RemainingNonRepresentationFrontierAfterDefaultBaseEndpointNonadjWitness h)

abbrev RemainingEndpointPointwiseNonadjFrontierAfterDefaultBase
    (h : D19ActsOnMoore57 V Γ) : Prop :=
  Nonempty
    (RemainingNonRepresentationFrontierAfterDefaultBaseEndpointPointwiseNonadj h)

abbrev RemainingEndpointAdjForcesAFixingFixedFrontierAfterDefaultBase
    (h : D19ActsOnMoore57 V Γ) : Prop :=
  Nonempty
    (RemainingNonRepresentationFrontierAfterDefaultBaseEndpointAdjForcesAFixingFixed
      h)

abbrev RemainingEndpointAdjForcesAFixingVertexFixedFrontierAfterDefaultBase
    (h : D19ActsOnMoore57 V Γ) : Prop :=
  Nonempty
    (RemainingNonRepresentationFrontierAfterDefaultBaseEndpointAdjForcesAFixingVertexFixed
      h)

abbrev RemainingPairEndpointNonadjFrontierAfterDefaultBase
    (h : D19ActsOnMoore57 V Γ) : Prop :=
  Nonempty
    (RemainingNonRepresentationFrontierAfterDefaultBasePairEndpointNonadj h)

abbrev RemainingPairEndpointTwoCommonNeighborsFrontierAfterDefaultBase
    (h : D19ActsOnMoore57 V Γ) : Prop :=
  Nonempty
    (RemainingNonRepresentationFrontierAfterDefaultBasePairEndpointTwoCommonNeighbors
      h)

/-- Concise endpoint-witness K155 no-go alias. -/
theorem no_remainingEndpointNonadjWitnessFrontierAfterDefaultBase_of_eigenspaceCharactersAndK155_autoRotation
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
    ¬ RemainingEndpointNonadjWitnessFrontierAfterDefaultBase h :=
  no_remainingNonRepresentationFrontierAfterDefaultBaseEndpointNonadjWitness_of_eigenspaceCharactersAndK155_autoRotation
    h alpha beta gamma A B C h7 hMinus8 hK

/-- Concise pointwise endpoint K155 no-go alias. -/
theorem no_remainingEndpointPointwiseNonadjFrontierAfterDefaultBase_of_eigenspaceCharactersAndK155_autoRotation
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
    ¬ RemainingEndpointPointwiseNonadjFrontierAfterDefaultBase h :=
  no_remainingNonRepresentationFrontierAfterDefaultBaseEndpointPointwiseNonadj_of_eigenspaceCharactersAndK155_autoRotation
    h alpha beta gamma A B C h7 hMinus8 hK

/-- Concise endpoint-forces-fixed K155 no-go alias. -/
theorem no_remainingEndpointAdjForcesAFixingFixedFrontierAfterDefaultBase_of_eigenspaceCharactersAndK155_autoRotation
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
    ¬ RemainingEndpointAdjForcesAFixingFixedFrontierAfterDefaultBase h :=
  no_remainingNonRepresentationFrontierAfterDefaultBaseEndpointAdjForcesAFixingFixed_of_eigenspaceCharactersAndK155_autoRotation
    h alpha beta gamma A B C h7 hMinus8 hK

/-- Concise vertex-fixed endpoint-forces-fixed K155 no-go alias. -/
theorem no_remainingEndpointAdjForcesAFixingVertexFixedFrontierAfterDefaultBase_of_eigenspaceCharactersAndK155_autoRotation
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
    ¬ RemainingEndpointAdjForcesAFixingVertexFixedFrontierAfterDefaultBase h :=
  no_remainingNonRepresentationFrontierAfterDefaultBaseEndpointAdjForcesAFixingVertexFixed_of_eigenspaceCharactersAndK155_autoRotation
    h alpha beta gamma A B C h7 hMinus8 hK

/-- Concise pair-endpoint non-adjacency K155 no-go alias. -/
theorem no_remainingPairEndpointNonadjFrontierAfterDefaultBase_of_eigenspaceCharactersAndK155_autoRotation
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
    ¬ RemainingPairEndpointNonadjFrontierAfterDefaultBase h :=
  no_remainingNonRepresentationFrontierAfterDefaultBasePairEndpointNonadj_of_eigenspaceCharactersAndK155_autoRotation
    h alpha beta gamma A B C h7 hMinus8 hK

/-- Concise pair common-neighbor endpoint K155 no-go alias. -/
theorem no_remainingPairEndpointTwoCommonNeighborsFrontierAfterDefaultBase_of_eigenspaceCharactersAndK155_autoRotation
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
    ¬ RemainingPairEndpointTwoCommonNeighborsFrontierAfterDefaultBase h :=
  no_remainingNonRepresentationFrontierAfterDefaultBasePairEndpointTwoCommonNeighbors_of_eigenspaceCharactersAndK155_autoRotation
    h alpha beta gamma A B C h7 hMinus8 hK

end

end Moore57

