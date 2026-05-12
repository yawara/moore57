import Moore57.D19OnMoore57.NoGo.NonRepresentationEndpointFrontierNoGo
import Moore57.D19OnMoore57.Rotation.FixedCountOneFrontier
import Moore57.D19OnMoore57.Involution.FixedStarA1

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
