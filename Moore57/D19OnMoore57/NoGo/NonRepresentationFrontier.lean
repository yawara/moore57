import Moore57.D19OnMoore57.BranchOrbit.ABCDefaultBaseReferenceFrontier
import Moore57.D19OnMoore57.BranchOrbit.ABCMidpointDisjointnessFrontier
import Moore57.D19OnMoore57.Involution.FixedStarA1
import Moore57.D19OnMoore57.LinearCharacter.Dimension
import Moore57.D19OnMoore57.LinearCharacter.Minus8
import Moore57.D19OnMoore57.Rotation.FixedCountOneFrontier

/-!
# Non-representation frontier after the default-base reductions

This diagnostic file records the current raw-action-side frontier after the
default center-neighbor base, fixed-center-leaf, reference-matching, and
midpoint-disjointness connector files have been wired together.

After the representation components are supplied, the remaining explicit
non-representation fields are:

* `fixedCenterLeaf`;
* `k`;
* `referenceMatching`;
* `support_card_boundary`;
* `no_card_one`;
* `noAllEndpointAdj`.

The file adds no new mathematical input.  It only gives stable names to this
frontier package and forgetful maps back to the existing public no-go surfaces.
-/

namespace Moore57

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

namespace BranchOrbitABCReflectionLabeling

variable {h : D19ActsOnMoore57 V Γ}

/-- Stable alias for the default-base labeling used by the final
non-representation frontier. -/
noncomputable abbrev nonRepresentationDefaultBaseLabeling
    (fixedCenterLeaf : ReflectionFixedCenterLeafBoundary h)
    (k : ZMod 19) :
    BranchOrbitABCReflectionLabeling h :=
  fixedCenterLeafDefaultBaseLabeling (h := h) fixedCenterLeaf k

/-- Stable alias for the default-base reference-matching field. -/
abbrev NonRepresentationDefaultBaseReferenceMatching
    (fixedCenterLeaf : ReflectionFixedCenterLeafBoundary h)
    (k : ZMod 19) : Prop :=
  ReferenceMatchingPipelineBoundary
    (nonRepresentationDefaultBaseLabeling (h := h) fixedCenterLeaf k)

/-- Stable alias for the default-base A-fixing support-cardinality field. -/
abbrev NonRepresentationDefaultBaseSupportCardBoundary
    (fixedCenterLeaf : ReflectionFixedCenterLeafBoundary h)
    (k : ZMod 19) : Prop :=
  AFixingReflectionFixedNeighborCardBoundary
    (nonRepresentationDefaultBaseLabeling (h := h) fixedCenterLeaf k)

/-- Stable alias for the default-base midpoint-exception card-one exclusion. -/
abbrev NonRepresentationDefaultBaseNoCardOne
    (fixedCenterLeaf : ReflectionFixedCenterLeafBoundary h)
    (k : ZMod 19) : Prop :=
  ∀ d : ZMod 19, ∀ hd : d ≠ 0,
    ((nonRepresentationDefaultBaseLabeling
        (h := h) fixedCenterLeaf k).midpointExceptionAFixingSupportIntersection
      (midpointOf d) (midpointOf_ne_zero hd)).card ≠ 1

/-- Stable alias for the default-base endpoint-adjacency obstruction. -/
abbrev NonRepresentationDefaultBaseNoAllEndpointAdj
    (fixedCenterLeaf : ReflectionFixedCenterLeafBoundary h)
    (k : ZMod 19) : Prop :=
  MidpointExceptionAFixingSupportNoAllEndpointAdjBoundary
    (nonRepresentationDefaultBaseLabeling (h := h) fixedCenterLeaf k)

/-- Stable alias for the midpoint-disjointness diagnostic package at the
default-base fixed-center-leaf labeling. -/
abbrev NonRepresentationDefaultBaseMidpointDisjointnessBoundary
    (fixedCenterLeaf : ReflectionFixedCenterLeafBoundary h)
    (k : ZMod 19) : Prop :=
  ReferenceFiberMatchingEquationMidpointDisjointnessBoundary
    (nonRepresentationDefaultBaseLabeling (h := h) fixedCenterLeaf k)

end BranchOrbitABCReflectionLabeling

/-- Final non-representation connector after default-base reductions.  The
fields are intentionally kept explicit so this file remains a stable diagnostic
inventory of what has not yet been constructed from a raw action alone. -/
structure RemainingNonRepresentationFrontierAfterDefaultBase
    (h : D19ActsOnMoore57 V Γ) where
  fixedCenterLeaf : ReflectionFixedCenterLeafBoundary h
  k : ZMod 19
  referenceMatching :
    BranchOrbitABCReflectionLabeling.NonRepresentationDefaultBaseReferenceMatching
      (h := h) fixedCenterLeaf k
  support_card_boundary :
    BranchOrbitABCReflectionLabeling.NonRepresentationDefaultBaseSupportCardBoundary
      (h := h) fixedCenterLeaf k
  no_card_one :
    BranchOrbitABCReflectionLabeling.NonRepresentationDefaultBaseNoCardOne
      (h := h) fixedCenterLeaf k
  noAllEndpointAdj :
    BranchOrbitABCReflectionLabeling.NonRepresentationDefaultBaseNoAllEndpointAdj
      (h := h) fixedCenterLeaf k

namespace RemainingNonRepresentationFrontierAfterDefaultBase

variable {h : D19ActsOnMoore57 V Γ}

/-- Rebundle the explicit frontier fields as the midpoint-disjointness
diagnostic boundary. -/
def toMidpointDisjointnessBoundary
    (connector : RemainingNonRepresentationFrontierAfterDefaultBase h) :
    BranchOrbitABCReflectionLabeling.NonRepresentationDefaultBaseMidpointDisjointnessBoundary
      (h := h) connector.fixedCenterLeaf connector.k where
  referenceMatching := connector.referenceMatching
  support_card_boundary := connector.support_card_boundary
  no_card_one := connector.no_card_one
  noAllEndpointAdj := connector.noAllEndpointAdj

/-- Forget the explicit midpoint-disjointness diagnostics back to the
default-base reference frontier package. -/
def toDefaultBaseFixedCenterLeafReferenceConnector
    (connector : RemainingNonRepresentationFrontierAfterDefaultBase h) :
    RemainingDefaultBaseFixedCenterLeafReferenceConnector h where
  fixedCenterLeaf := connector.fixedCenterLeaf
  k := connector.k
  referenceMatching := connector.referenceMatching
  midpointExceptionDisjoint :=
    connector.toMidpointDisjointnessBoundary
      |>.toMidpointExceptionDisjointAFixingSupportBoundary

/-- The explicit default-base frontier supplies the two-solution
reference-fiber matching equation for the induced fixed-center-leaf pair. -/
theorem referenceMatchingEquationCardTwo
    (connector : RemainingNonRepresentationFrontierAfterDefaultBase h) :
    BranchOrbitABCReflectionLabeling.ReferenceFiberMatchingEquationCardTwoOfPair
      (h := h)
      (BranchOrbitABCReflectionLabeling.fixedCenterLeafDefaultBasePair
        (h := h) connector.fixedCenterLeaf connector.k) :=
  connector.toDefaultBaseFixedCenterLeafReferenceConnector
    |>.referenceMatchingEquationCardTwo

/-- Forget the explicit default-base fields back to the fixed-center-leaf
matching-equation connector. -/
def toRemainingFixedCenterLeafMatchingEquationConnector
    (connector : RemainingNonRepresentationFrontierAfterDefaultBase h) :
    RemainingFixedCenterLeafMatchingEquationConnector h :=
  connector.toDefaultBaseFixedCenterLeafReferenceConnector
    |>.toRemainingFixedCenterLeafMatchingEquationConnector

/-- Forget the explicit default-base fields back to the public
labeled-reflection matching-equation connector. -/
def toRemainingLabeledReflectionMatchingEquationConnector
    (connector : RemainingNonRepresentationFrontierAfterDefaultBase h) :
    RemainingLabeledReflectionMatchingEquationConnector h :=
  connector.toDefaultBaseFixedCenterLeafReferenceConnector
    |>.toRemainingLabeledReflectionMatchingEquationConnector

end RemainingNonRepresentationFrontierAfterDefaultBase

/-- Once the representation components are supplied, the current explicit
non-representation default-base frontier is refuted by the existing public
matching-equation no-go theorem. -/
theorem no_remainingNonRepresentationFrontierAfterDefaultBase_of_components
    (h : D19ActsOnMoore57 V Γ) :
    ¬ ∃ _representationComponents : RemainingRepresentationComponents h,
        Nonempty (RemainingNonRepresentationFrontierAfterDefaultBase h) := by
  rintro ⟨representationComponents, ⟨connector⟩⟩
  exact no_remainingDefaultBaseFixedCenterLeafReferenceConnector_of_components h
    ⟨representationComponents,
      ⟨connector.toDefaultBaseFixedCenterLeafReferenceConnector⟩⟩

/-- Mathlib-character version of the same diagnostic no-go.  Under the
representation-theoretic hypotheses, the only remaining raw-action fields are
the explicit fields of
`RemainingNonRepresentationFrontierAfterDefaultBase`. -/
theorem no_remainingNonRepresentationFrontierAfterDefaultBase_of_mathlibCharacter
    (h : D19ActsOnMoore57 V Γ)
    {W : Type*} [AddCommGroup W] [Module ℚ W] [FiniteDimensional ℚ W]
    (ρ : Representation ℚ (DihedralGroup 19) W)
    (alpha beta gamma : ℕ)
    (finrank_eq : Module.finrank ℚ W = 1729)
    (trace_eq_character :
      ∀ g : DihedralGroup 19,
        Matrix.trace (E7Matrix Γ * permMatrix (h.smulEquiv g)) =
          ρ.character g)
    (character_eq_d19Linear :
      ∀ g : DihedralGroup 19,
        ρ.character g =
          (d19LinearCharacter alpha beta gamma g : ℚ))
    (reflection : (alpha : ℤ) - (beta : ℤ) = 33)
    (minus8_trivial_nonneg : alpha ≤ 113)
    (minus8_sign_nonneg : beta ≤ 58) :
    ¬ Nonempty (RemainingNonRepresentationFrontierAfterDefaultBase h) := by
  rintro ⟨connector⟩
  exact
    no_remainingLabeledReflectionMatchingEquationConnector_of_mathlibCharacter
      h ρ alpha beta gamma finrank_eq trace_eq_character
      character_eq_d19Linear reflection minus8_trivial_nonneg
      minus8_sign_nonneg
      connector.toRemainingLabeledReflectionMatchingEquationConnector

/-- Combined diagnostic proposition for the post-default-base
non-representation frontier. -/
abbrev RemainingNonRepresentationRawActionFrontierAfterDefaultBase
    (h : D19ActsOnMoore57 V Γ) : Prop :=
  Nonempty (RemainingNonRepresentationFrontierAfterDefaultBase h)

/-- Component-level no-go alias for the combined diagnostic proposition. -/
theorem no_remainingNonRepresentationRawActionFrontierAfterDefaultBase_of_components
    (h : D19ActsOnMoore57 V Γ) :
    ¬ ∃ _representationComponents : RemainingRepresentationComponents h,
        RemainingNonRepresentationRawActionFrontierAfterDefaultBase h :=
  no_remainingNonRepresentationFrontierAfterDefaultBase_of_components h

end

end Moore57

/-!
# Linear-character no-go for the default-base non-representation frontier

This file exposes the post-default-base frontier no-go directly from the
existing linear-character/count connectors.  It does not add representation
theory; it only delegates to
`representationCharacterComponentsBoundary_of_*AndCounts` and the component
level frontier contradiction.
-/

namespace Moore57

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- Linear-character/count form of the post-default-base frontier no-go. -/
theorem no_remainingNonRepresentationFrontierAfterDefaultBase_of_linearCharacterAndCounts
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
    ¬ Nonempty (RemainingNonRepresentationFrontierAfterDefaultBase h) := by
  intro frontier
  exact no_remainingNonRepresentationFrontierAfterDefaultBase_of_components h
    ⟨D19ActsOnMoore57.representationCharacterComponentsBoundary_of_linearCharacterAndCounts
        h alpha beta gamma minus8_trivial_nonneg minus8_sign_nonneg
        hlin ha0 ha1,
      frontier⟩

/-- Mathlib-representation/count form of the post-default-base frontier no-go.

The representation side is consumed through the existing connector file, so
this theorem avoids the older explicit finrank and reflection-arithmetic
arguments at this frontier layer. -/
theorem no_remainingNonRepresentationFrontierAfterDefaultBase_of_representationCharacterAndCounts
    (h : D19ActsOnMoore57 V Γ)
    {W : Type*} [AddCommGroup W] [Module ℚ W] [FiniteDimensional ℚ W]
    (ρ : Representation ℚ (DihedralGroup 19) W)
    (alpha beta gamma : ℕ)
    (minus8_trivial_nonneg : alpha ≤ 113)
    (minus8_sign_nonneg : beta ≤ 58)
    (trace_eq_character :
      ∀ g : DihedralGroup 19,
        Matrix.trace (E7Matrix Γ * permMatrix (h.smulEquiv g)) =
          ρ.character g)
    (character_eq_d19Linear :
      ∀ g : DihedralGroup 19,
        ρ.character g =
          (d19LinearCharacter alpha beta gamma g : ℚ))
    {d : ZMod 19}
    (ha0 : fixedVertexCount (h.smulEquiv (DihedralGroup.sr d)) = 56)
    (ha1 : adjacentMovedCount Γ (h.smulEquiv (DihedralGroup.sr d)) = 112) :
    ¬ Nonempty (RemainingNonRepresentationFrontierAfterDefaultBase h) := by
  intro frontier
  exact no_remainingNonRepresentationFrontierAfterDefaultBase_of_components h
    ⟨D19ActsOnMoore57.representationCharacterComponentsBoundary_of_representationCharacterAndCounts
        h ρ alpha beta gamma minus8_trivial_nonneg minus8_sign_nonneg
        trace_eq_character character_eq_d19Linear ha0 ha1,
      frontier⟩

/-- Linear-character/count form for the raw-action diagnostic proposition. -/
theorem no_remainingNonRepresentationRawActionFrontierAfterDefaultBase_of_linearCharacterAndCounts
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
    ¬ RemainingNonRepresentationRawActionFrontierAfterDefaultBase h :=
  no_remainingNonRepresentationFrontierAfterDefaultBase_of_linearCharacterAndCounts
    h alpha beta gamma minus8_trivial_nonneg minus8_sign_nonneg hlin ha0 ha1

/-- Mathlib-representation/count form for the raw-action diagnostic
proposition. -/
theorem no_remainingNonRepresentationRawActionFrontierAfterDefaultBase_of_representationCharacterAndCounts
    (h : D19ActsOnMoore57 V Γ)
    {W : Type*} [AddCommGroup W] [Module ℚ W] [FiniteDimensional ℚ W]
    (ρ : Representation ℚ (DihedralGroup 19) W)
    (alpha beta gamma : ℕ)
    (minus8_trivial_nonneg : alpha ≤ 113)
    (minus8_sign_nonneg : beta ≤ 58)
    (trace_eq_character :
      ∀ g : DihedralGroup 19,
        Matrix.trace (E7Matrix Γ * permMatrix (h.smulEquiv g)) =
          ρ.character g)
    (character_eq_d19Linear :
      ∀ g : DihedralGroup 19,
        ρ.character g =
          (d19LinearCharacter alpha beta gamma g : ℚ))
    {d : ZMod 19}
    (ha0 : fixedVertexCount (h.smulEquiv (DihedralGroup.sr d)) = 56)
    (ha1 : adjacentMovedCount Γ (h.smulEquiv (DihedralGroup.sr d)) = 112) :
    ¬ RemainingNonRepresentationRawActionFrontierAfterDefaultBase h :=
  no_remainingNonRepresentationFrontierAfterDefaultBase_of_representationCharacterAndCounts
    h ρ alpha beta gamma minus8_trivial_nonneg minus8_sign_nonneg
    trace_eq_character character_eq_d19Linear ha0 ha1

end

end Moore57

/-!
# Eigenspace-character connector for the post-default-base frontier

This file keeps the representation-theoretic work behind the existing
`D19LinearCharacterMinus8Connectors` boundary.  The post-default-base
non-representation frontier can therefore consume the eigenspace character
identities and fixed-count data directly.
-/

namespace Moore57

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- Eigenspace character identities and the standard fixed-count data supply
the representation components needed to refute the post-default-base
non-representation frontier. -/
theorem no_remainingNonRepresentationFrontierAfterDefaultBase_of_eigenspaceCharactersAndCounts
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
    ¬ Nonempty (RemainingNonRepresentationFrontierAfterDefaultBase h) := by
  intro frontier
  exact no_remainingNonRepresentationFrontierAfterDefaultBase_of_components h
    ⟨D19ActsOnMoore57.representationCharacterComponentsBoundary_of_eigenspaceCharactersAndCounts
        h alpha beta gamma A B C h7 hMinus8 hreflection_a0
        hrotation_a0 hreflection_a1,
      frontier⟩

/-- Raw-action-frontier alias of
`no_remainingNonRepresentationFrontierAfterDefaultBase_of_eigenspaceCharactersAndCounts`.
-/
theorem no_remainingNonRepresentationRawActionFrontierAfterDefaultBase_of_eigenspaceCharactersAndCounts
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
    ¬ RemainingNonRepresentationRawActionFrontierAfterDefaultBase h :=
  no_remainingNonRepresentationFrontierAfterDefaultBase_of_eigenspaceCharactersAndCounts
    h alpha beta gamma A B C h7 hMinus8 hreflection_a0 hrotation_a0
    hreflection_a1

end

end Moore57

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

/-!
# Auto-rotation no-go for the default-base non-representation frontier

This file removes the explicit rotation fixed-count hypothesis from the
post-default-base frontier no-go surfaces.  The rotation count is supplied by
the proved `D19ActsOnMoore57.rotationFixedCountOne_smulEquiv` theorem.
-/

namespace Moore57

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- Eigenspace-character no-go with explicit reflection counts and automatic
rotation count-one input from the ambient `D19ActsOnMoore57` theorem. -/
theorem no_remainingNonRepresentationFrontierAfterDefaultBase_of_eigenspaceCharactersAndReflectionCounts_autoRotation
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
    ¬ Nonempty (RemainingNonRepresentationFrontierAfterDefaultBase h) :=
  no_remainingNonRepresentationFrontierAfterDefaultBase_of_eigenspaceCharactersAndCounts
    h alpha beta gamma A B C h7 hMinus8 hreflection_a0
    (D19ActsOnMoore57.rotationFixedCountOne_smulEquiv h) hreflection_a1

/-- Raw-action-frontier alias of the auto-rotation eigenspace/reflection-count
no-go. -/
theorem no_remainingNonRepresentationRawActionFrontierAfterDefaultBase_of_eigenspaceCharactersAndReflectionCounts_autoRotation
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
    ¬ RemainingNonRepresentationRawActionFrontierAfterDefaultBase h :=
  no_remainingNonRepresentationFrontierAfterDefaultBase_of_eigenspaceCharactersAndReflectionCounts_autoRotation
    h alpha beta gamma A B C h7 hMinus8 hreflection_a0 hreflection_a1

/-- Eigenspace-character no-go with reflection counts supplied by an
`InvolutionFixedStar55` witness and rotation counts supplied automatically. -/
theorem no_remainingNonRepresentationFrontierAfterDefaultBase_of_eigenspaceCharactersAndFixedStar55_autoRotation
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
    ¬ Nonempty (RemainingNonRepresentationFrontierAfterDefaultBase h) :=
  no_remainingNonRepresentationFrontierAfterDefaultBase_of_eigenspaceCharactersAndFixedStar55
    h alpha beta gamma A B C h7 hMinus8 hStar
    (D19ActsOnMoore57.rotationFixedCountOne_smulEquiv h)

/-- Raw-action-frontier alias of the auto-rotation fixed-star eigenspace
no-go. -/
theorem no_remainingNonRepresentationRawActionFrontierAfterDefaultBase_of_eigenspaceCharactersAndFixedStar55_autoRotation
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
    ¬ RemainingNonRepresentationRawActionFrontierAfterDefaultBase h :=
  no_remainingNonRepresentationFrontierAfterDefaultBase_of_eigenspaceCharactersAndFixedStar55_autoRotation
    h alpha beta gamma A B C h7 hMinus8 hStar

end

end Moore57

/-!
# K155 no-go for the default-base non-representation frontier

This file removes the explicit reflection-count hypotheses from the
post-default-base frontier no-go when an explicit `K_{1,55}` reflection witness
is available.  The witness is converted to `InvolutionFixedStar55`, and the
rotation count is supplied by the existing auto-rotation theorem.
-/

namespace Moore57

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- Eigenspace-character no-go with reflection counts supplied by an explicit
`K_{1,55}` reflection witness and rotation counts supplied automatically. -/
theorem no_remainingNonRepresentationFrontierAfterDefaultBase_of_eigenspaceCharactersAndK155_autoRotation
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
    ¬ Nonempty (RemainingNonRepresentationFrontierAfterDefaultBase h) :=
  no_remainingNonRepresentationFrontierAfterDefaultBase_of_eigenspaceCharactersAndFixedStar55_autoRotation
    h alpha beta gamma A B C h7 hMinus8
    (InvolutionK155.toInvolutionFixedStar55 h.isMoore hK)

/-- Raw-action-frontier alias of the auto-rotation K155 eigenspace no-go. -/
theorem no_remainingNonRepresentationRawActionFrontierAfterDefaultBase_of_eigenspaceCharactersAndK155_autoRotation
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
    ¬ RemainingNonRepresentationRawActionFrontierAfterDefaultBase h :=
  no_remainingNonRepresentationFrontierAfterDefaultBase_of_eigenspaceCharactersAndK155_autoRotation
    h alpha beta gamma A B C h7 hMinus8 hK

end

end Moore57

