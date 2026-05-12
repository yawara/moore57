import Moore57.D19OnMoore57.BranchOrbit.ABCDefaultBaseReferenceFrontier
import Moore57.D19OnMoore57.BranchOrbit.ABCMidpointDisjointnessFrontier

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
