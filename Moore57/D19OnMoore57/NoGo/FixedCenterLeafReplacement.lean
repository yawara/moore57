import Moore57.D19OnMoore57.NoGo.NonRepresentationFrontier
import Moore57.D19OnMoore57.Reflection.FixedCenterLeafActionFrontier
import Moore57.D19OnMoore57.Rotation.FixedCountOneFrontier

/-!
# Fixed-center-leaf replacement frontier

This file isolates the `fixedCenterLeaf` field of the compressed
post-default-base non-representation frontier.  The wrappers below replace
that field by upstream fixed-star packages and then project back to
`RemainingNonRepresentationFrontierAfterDefaultBase`.

No new combinatorial argument is introduced here; this is projection/wiring
only.
-/

namespace Moore57

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- Compressed post-default-base frontier with `fixedCenterLeaf` replaced by
the induced fixed-star degree package. -/
structure RemainingNonRepresentationFrontierAfterDefaultBaseFixedInducedStarDegrees
    (h : D19ActsOnMoore57 V Γ) where
  fixedInducedStarDegrees : ReflectionFixedInducedStarDegrees h
  k : ZMod 19
  referenceMatching :
    BranchOrbitABCReflectionLabeling.NonRepresentationDefaultBaseReferenceMatching
      (h := h) fixedInducedStarDegrees.toReflectionFixedCenterLeafBoundary k
  support_card_boundary :
    BranchOrbitABCReflectionLabeling.NonRepresentationDefaultBaseSupportCardBoundary
      (h := h) fixedInducedStarDegrees.toReflectionFixedCenterLeafBoundary k
  no_card_one :
    BranchOrbitABCReflectionLabeling.NonRepresentationDefaultBaseNoCardOne
      (h := h) fixedInducedStarDegrees.toReflectionFixedCenterLeafBoundary k
  noAllEndpointAdj :
    BranchOrbitABCReflectionLabeling.NonRepresentationDefaultBaseNoAllEndpointAdj
      (h := h) fixedInducedStarDegrees.toReflectionFixedCenterLeafBoundary k

namespace RemainingNonRepresentationFrontierAfterDefaultBaseFixedInducedStarDegrees

variable {h : D19ActsOnMoore57 V Γ}

/-- Collapse the induced-degree wrapper to the compressed post-default-base
frontier. -/
def toRemainingNonRepresentationFrontierAfterDefaultBase
    (connector :
      RemainingNonRepresentationFrontierAfterDefaultBaseFixedInducedStarDegrees
        h) :
    RemainingNonRepresentationFrontierAfterDefaultBase h where
  fixedCenterLeaf :=
    connector.fixedInducedStarDegrees.toReflectionFixedCenterLeafBoundary
  k := connector.k
  referenceMatching := connector.referenceMatching
  support_card_boundary := connector.support_card_boundary
  no_card_one := connector.no_card_one
  noAllEndpointAdj := connector.noAllEndpointAdj

end RemainingNonRepresentationFrontierAfterDefaultBaseFixedInducedStarDegrees

/-- Compressed post-default-base frontier with `fixedCenterLeaf` replaced by
the action-level reflection fixed-neighbor star-count package. -/
structure RemainingNonRepresentationFrontierAfterDefaultBaseFixedNeighborStarCounts
    (h : D19ActsOnMoore57 V Γ) where
  fixedNeighborStarCounts : ReflectionFixedNeighborStarCounts h
  k : ZMod 19
  referenceMatching :
    BranchOrbitABCReflectionLabeling.NonRepresentationDefaultBaseReferenceMatching
      (h := h) fixedNeighborStarCounts.toReflectionFixedCenterLeafBoundary k
  support_card_boundary :
    BranchOrbitABCReflectionLabeling.NonRepresentationDefaultBaseSupportCardBoundary
      (h := h) fixedNeighborStarCounts.toReflectionFixedCenterLeafBoundary k
  no_card_one :
    BranchOrbitABCReflectionLabeling.NonRepresentationDefaultBaseNoCardOne
      (h := h) fixedNeighborStarCounts.toReflectionFixedCenterLeafBoundary k
  noAllEndpointAdj :
    BranchOrbitABCReflectionLabeling.NonRepresentationDefaultBaseNoAllEndpointAdj
      (h := h) fixedNeighborStarCounts.toReflectionFixedCenterLeafBoundary k

namespace RemainingNonRepresentationFrontierAfterDefaultBaseFixedNeighborStarCounts

variable {h : D19ActsOnMoore57 V Γ}

/-- Collapse the fixed-neighbor star-count wrapper to the compressed
post-default-base frontier. -/
def toRemainingNonRepresentationFrontierAfterDefaultBase
    (connector :
      RemainingNonRepresentationFrontierAfterDefaultBaseFixedNeighborStarCounts
        h) :
    RemainingNonRepresentationFrontierAfterDefaultBase h where
  fixedCenterLeaf :=
    connector.fixedNeighborStarCounts.toReflectionFixedCenterLeafBoundary
  k := connector.k
  referenceMatching := connector.referenceMatching
  support_card_boundary := connector.support_card_boundary
  no_card_one := connector.no_card_one
  noAllEndpointAdj := connector.noAllEndpointAdj

end RemainingNonRepresentationFrontierAfterDefaultBaseFixedNeighborStarCounts

/-- Compressed post-default-base frontier with `fixedCenterLeaf` replaced by
explicit `K_{1,55}` packages for all reflections, plus the required condition
that `rotationFixedCenter` is not the center of those stars. -/
structure RemainingNonRepresentationFrontierAfterDefaultBaseInvolutionK155
    (h : D19ActsOnMoore57 V Γ) where
  involutionK155 :
    ∀ k : ZMod 19, InvolutionK155 Γ (h.smulEquiv (DihedralGroup.sr k))
  rotationFixedCenter_ne_center :
    ∀ k : ZMod 19, h.rotationFixedCenter ≠ (involutionK155 k).center
  k : ZMod 19
  referenceMatching :
    BranchOrbitABCReflectionLabeling.NonRepresentationDefaultBaseReferenceMatching
      (h := h)
      (h.reflectionFixedCenterLeafBoundary_of_involutionK155
        involutionK155 rotationFixedCenter_ne_center)
      k
  support_card_boundary :
    BranchOrbitABCReflectionLabeling.NonRepresentationDefaultBaseSupportCardBoundary
      (h := h)
      (h.reflectionFixedCenterLeafBoundary_of_involutionK155
        involutionK155 rotationFixedCenter_ne_center)
      k
  no_card_one :
    BranchOrbitABCReflectionLabeling.NonRepresentationDefaultBaseNoCardOne
      (h := h)
      (h.reflectionFixedCenterLeafBoundary_of_involutionK155
        involutionK155 rotationFixedCenter_ne_center)
      k
  noAllEndpointAdj :
    BranchOrbitABCReflectionLabeling.NonRepresentationDefaultBaseNoAllEndpointAdj
      (h := h)
      (h.reflectionFixedCenterLeafBoundary_of_involutionK155
        involutionK155 rotationFixedCenter_ne_center)
      k

namespace RemainingNonRepresentationFrontierAfterDefaultBaseInvolutionK155

variable {h : D19ActsOnMoore57 V Γ}

/-- Collapse the explicit `K_{1,55}` wrapper to the compressed
post-default-base frontier. -/
def toRemainingNonRepresentationFrontierAfterDefaultBase
    (connector :
      RemainingNonRepresentationFrontierAfterDefaultBaseInvolutionK155 h) :
    RemainingNonRepresentationFrontierAfterDefaultBase h where
  fixedCenterLeaf :=
    h.reflectionFixedCenterLeafBoundary_of_involutionK155
      connector.involutionK155
      connector.rotationFixedCenter_ne_center
  k := connector.k
  referenceMatching := connector.referenceMatching
  support_card_boundary := connector.support_card_boundary
  no_card_one := connector.no_card_one
  noAllEndpointAdj := connector.noAllEndpointAdj

end RemainingNonRepresentationFrontierAfterDefaultBaseInvolutionK155

/-- Component-level no-go for the induced fixed-star degree wrapper. -/
theorem no_remainingNonRepresentationFrontierAfterDefaultBaseFixedInducedStarDegrees_of_components
    (h : D19ActsOnMoore57 V Γ) :
    ¬ ∃ _representationComponents : RemainingRepresentationComponents h,
        Nonempty
          (RemainingNonRepresentationFrontierAfterDefaultBaseFixedInducedStarDegrees
            h) := by
  rintro ⟨representationComponents, ⟨connector⟩⟩
  exact no_remainingNonRepresentationFrontierAfterDefaultBase_of_components h
    ⟨representationComponents,
      ⟨connector.toRemainingNonRepresentationFrontierAfterDefaultBase⟩⟩

/-- Component-level no-go for the fixed-neighbor star-count wrapper. -/
theorem no_remainingNonRepresentationFrontierAfterDefaultBaseFixedNeighborStarCounts_of_components
    (h : D19ActsOnMoore57 V Γ) :
    ¬ ∃ _representationComponents : RemainingRepresentationComponents h,
        Nonempty
          (RemainingNonRepresentationFrontierAfterDefaultBaseFixedNeighborStarCounts
            h) := by
  rintro ⟨representationComponents, ⟨connector⟩⟩
  exact no_remainingNonRepresentationFrontierAfterDefaultBase_of_components h
    ⟨representationComponents,
      ⟨connector.toRemainingNonRepresentationFrontierAfterDefaultBase⟩⟩

/-- Component-level no-go for the explicit per-reflection `K_{1,55}` wrapper. -/
theorem no_remainingNonRepresentationFrontierAfterDefaultBaseInvolutionK155_of_components
    (h : D19ActsOnMoore57 V Γ) :
    ¬ ∃ _representationComponents : RemainingRepresentationComponents h,
        Nonempty
          (RemainingNonRepresentationFrontierAfterDefaultBaseInvolutionK155
            h) := by
  rintro ⟨representationComponents, ⟨connector⟩⟩
  exact no_remainingNonRepresentationFrontierAfterDefaultBase_of_components h
    ⟨representationComponents,
      ⟨connector.toRemainingNonRepresentationFrontierAfterDefaultBase⟩⟩

end

end Moore57

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

