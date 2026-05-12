import Moore57.D19OnMoore57.BranchOrbit.BranchOrbitABCRemainingGapAfterAllOffsets
import Moore57.D19OnMoore57.BranchOrbit.BranchOrbitABCAllOffsetsClosedFrontier

/-!
# Remaining raw-action frontier for public D19 no-go surfaces

This diagnostic file audits the public `no_D19...` theorem surfaces after the
all-offset card-two work.

The all-offset closure removed the old need for a representation component in
these report-level contradictions:

* `BranchOrbitABCActionLevelDoublingEquationSupportBoundary`
* `BranchOrbitABCCurrentFinalGapBoundary`
* `BranchOrbitABCEndpointPairedFinalBoundary`

The remaining assumptions are connector packages: records or predicates that
must still be constructed from a raw `D19ActsOnMoore57` action, or supplied by
the mathlib-facing representation bridge before the package no-go theorem can
fire.  This file adds no new mathematical input; it only groups existing
public no-go names into stable frontier aliases.
-/

namespace Moore57

open Finset

noncomputable section

universe u uP

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

local instance instD19RemainingRawActionFrontierPFintype
    {h : D19ActsOnMoore57 V Γ}
    (labeling : BranchOrbitABCReflectionLabeling h) :
    Fintype labeling.data.toAFiberCoordinates.P :=
  labeling.data.toAFiberCoordinates.P_fintype

local instance instD19RemainingRawActionFrontierBranchDataPFintype
    {h : D19ActsOnMoore57 V Γ}
    (labeling : BranchOrbitABCReflectionLabeling h) :
    Fintype labeling.data.toBranchOrbitABCData.toAFiberCoordinates.P :=
  labeling.data.toBranchOrbitABCData.toAFiberCoordinates.P_fintype

local instance instD19RemainingRawActionFrontierDecidableEq
    (α : Type*) : DecidableEq α :=
  Classical.decEq α

/-! ## Raw-action/concrete-data surface -/

/-- The original counting theorem still stops at nonexistence of the concrete
orbit data package; constructing this package from a raw action is a remaining
connector. -/
abbrev RemainingConcreteOrbitDataConnector
    (_h : D19ActsOnMoore57 V Γ) : Prop :=
  Nonempty (D19ConcreteHypotheses Γ)

/-- Public alias for the current raw-action-to-concrete-data no-go surface. -/
theorem no_remainingConcreteOrbitDataConnector
    (h : D19ActsOnMoore57 V Γ) :
    ¬ RemainingConcreteOrbitDataConnector h :=
  no_D19_acts_on_Moore57 h

/-! ## Final-boundary package surfaces -/

/-- Public final-boundary records that are neither raw actions nor mathlib
representation objects.  A raw action would still need to construct one of
these connector packages before the corresponding public no-go theorem applies.
-/
abbrev RemainingPublicFinalBoundaryConnector
    (h : D19ActsOnMoore57 V Γ) : Prop :=
  Nonempty (D19FinalExposedHybridBoundaryInputs.{u, uP} h) ∨
  Nonempty (D19FinalInputCriterionBoundaryInputs.{u, uP} h) ∨
  Nonempty (D19FinalCharacterCriterionBoundaryInputs.{u, uP} h) ∨
  Nonempty (D19FinalCharacterAFiberBoundaryInputs.{u, uP} h) ∨
  Nonempty (D19FinalCharacterAFiberNoFixedBoundaryInputs.{u, uP} h) ∨
  Nonempty (D19FinalTraceHybridNoFixedBoundaryInputs.{u, uP} h)

/-- All currently public final-boundary connector records are refuted by the
existing final criterion aliases. -/
theorem no_remainingPublicFinalBoundaryConnector
    (h : D19ActsOnMoore57 V Γ) :
    ¬ RemainingPublicFinalBoundaryConnector.{u, uP} h := by
  intro hfrontier
  rcases hfrontier with
    hExposed | hInput | hCharacter | hAFiber | hAFiberNoFixed | hTraceNoFixed
  · exact no_D19_final_exposed_hybrid_boundary h hExposed
  · exact no_D19_final_input_criterion_boundary h hInput
  · exact no_D19_final_character_criterion_boundary h hCharacter
  · exact no_D19_final_character_aFiber_boundary h hAFiber
  · exact no_D19_final_character_aFiber_no_fixed_boundary h hAFiberNoFixed
  · exact no_D19_final_trace_hybrid_no_fixed_boundary h hTraceNoFixed

/-! ## All-offset report-level surfaces -/

/-- Endpoint-paired final report surface.  This is now closed directly by the
all-offset common-neighbor obstruction, without representation data. -/
abbrev RemainingEndpointPairedConnector
    (h : D19ActsOnMoore57 V Γ) : Prop :=
  Nonempty (BranchOrbitABCEndpointPairedFinalBoundary h)

/-- Public alias for the endpoint-paired all-offset no-go surface. -/
theorem no_remainingEndpointPairedConnector
    (h : D19ActsOnMoore57 V Γ) :
    ¬ RemainingEndpointPairedConnector h :=
  not_endpointPairedFinalBoundary_allOffsetsCommonNeighbor h

/-- Endpoint-obstruction final report surface.  The endpoint-obstruction data
is also unused by the all-offset support-subset contradiction. -/
abbrev RemainingEndpointObstructionConnector
    (h : D19ActsOnMoore57 V Γ) : Prop :=
  Nonempty (BranchOrbitABCEndpointObstructionFinalBoundary h)

/-- Public alias for the endpoint-obstruction all-offset no-go surface. -/
theorem no_remainingEndpointObstructionConnector
    (h : D19ActsOnMoore57 V Γ) :
    ¬ RemainingEndpointObstructionConnector h :=
  not_endpointObstructionFinalBoundary_allOffsetsCommonNeighbor h

/-- Report-level/final connector packages that are already closed by the
all-offset card-two obstruction, without representation data. -/
abbrev RemainingAllOffsetClosedConnector
    (h : D19ActsOnMoore57 V Γ) : Prop :=
  RemainingActionLevelAllOffsetsSupportPackage h ∨
  RemainingCurrentFinalGapReportPackage h ∨
  RemainingEndpointPairedConnector h ∨
  RemainingEndpointObstructionConnector h

/-- The all-offset report-level/final connector packages cannot exist. -/
theorem no_remainingAllOffsetClosedConnector
    (h : D19ActsOnMoore57 V Γ) :
    ¬ RemainingAllOffsetClosedConnector h := by
  intro hfrontier
  rcases hfrontier with hSupport | hReport | hEndpoint | hObstruction
  · exact no_remaining_actionLevelAllOffsetsSupportPackage h hSupport
  · exact no_remaining_currentFinalGapReportPackage h hReport
  · exact no_remainingEndpointPairedConnector h hEndpoint
  · exact no_remainingEndpointObstructionConnector h hObstruction

/-! ## Branch/reflection geometry surfaces -/

/-- Branch/reflection connector packages still visible in public no-go
surfaces.  The first three records contain representation components
internally; the fixed-star surfaces expose that component boundary explicitly.
Endpoint-paired and endpoint-obstruction final reports are classified above as
all-offset closed surfaces. -/
abbrev RemainingBranchReflectionConnector
    (h : D19ActsOnMoore57 V Γ) : Prop :=
  RemainingCanonicalAllFibersPackage h ∨
  RemainingCanonicalCompactSplitPackage h ∨
  RemainingReflectionLabeledCompactSplitPackage h ∨
  RemainingFixedStarReferenceMatchingPackage h ∨
  RemainingLeanAwareFixedStarPackage h

/-- The public branch/reflection connector package surfaces are all already
refuted once supplied. -/
theorem no_remainingBranchReflectionConnector
    (h : D19ActsOnMoore57 V Γ) :
    ¬ RemainingBranchReflectionConnector h := by
  intro hfrontier
  rcases hfrontier with
    hAllFibers | hCompact | hLabeled | hFixedStar | hLeanAware
  · exact no_remaining_canonicalAllFibersPackage h hAllFibers
  · exact no_remaining_canonicalCompactSplitPackage h hCompact
  · exact no_remaining_reflectionLabeledCompactSplitPackage h hLabeled
  · exact no_remaining_fixedStarReferenceMatchingPackage h hFixedStar
  · exact no_remaining_leanAwareFixedStarPackage h hLeanAware

/-! ## Mathlib-character-to-raw-geometry surface -/

/-- The branch geometry left after the representation side has been supplied:
a labeled B/C reflection pair and the reference-fiber matching equation with
two solutions at every nonzero offset. -/
abbrev RemainingLabeledReflectionMatchingEquationConnector
    (h : D19ActsOnMoore57 V Γ) : Prop :=
  ∃ hp : BranchOrbitABCReflectionLabeling.HasLabeledReflectionPair h,
    let labeling :=
      BranchOrbitABCReflectionLabeling.ofHasLabeledReflectionPair
        (h := h) hp
    ∀ d : ZMod 19, ∀ hd : d ≠ 0,
      ((Finset.univ :
          Finset
            labeling.data.toBranchOrbitABCData.toAFiberCoordinates.P).filter fun p =>
        AFiberCoordinates.matchingEquiv h.isMoore
            labeling.data.toBranchOrbitABCData.toAFiberCoordinates
            0 (0 + d) (index_ne_add_of_ne_zero hd) p =
          (labeling.data.toBranchOrbitABCData.toAFiberRotationEquivariance).coordPerm
            d 0 p).card =
        2

/-- If the representation component boundary is supplied, the labeled
reflection/matching-equation connector is refuted by the existing public
surface. -/
theorem no_remainingLabeledReflectionMatchingEquationConnector_of_components
    (h : D19ActsOnMoore57 V Γ) :
    ¬ ∃ _representationComponents : RemainingRepresentationComponents h,
        RemainingLabeledReflectionMatchingEquationConnector h := by
  simpa [RemainingRepresentationComponents,
    RemainingLabeledReflectionMatchingEquationConnector] using
    no_D19_hasLabeledReflectionPair_referenceFiberMatchingEquation_boundary h

/-- Mathlib-character version of the same connector frontier.  After these
representation-theoretic hypotheses, the remaining non-mathlib/raw-action
assumption is exactly `RemainingLabeledReflectionMatchingEquationConnector`. -/
theorem no_remainingLabeledReflectionMatchingEquationConnector_of_mathlibCharacter
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
    ¬ RemainingLabeledReflectionMatchingEquationConnector h := by
  simpa [RemainingLabeledReflectionMatchingEquationConnector] using
    no_D19_mathlibCharacter_hasLabeledReflectionPair_referenceFiberMatchingEquation_boundary
      h ρ alpha beta gamma finrank_eq trace_eq_character
      character_eq_d19Linear reflection minus8_trivial_nonneg
      minus8_sign_nonneg

/-! ## Combined diagnostic surface -/

/-- Combined public frontier of connector assumptions that remain outside the
raw action itself. -/
abbrev RemainingPublicRawActionFrontier
    (h : D19ActsOnMoore57 V Γ) : Prop :=
  RemainingConcreteOrbitDataConnector h ∨
  RemainingPublicFinalBoundaryConnector.{u, uP} h ∨
  RemainingAllOffsetClosedConnector h ∨
  RemainingBranchReflectionConnector h

/-- The combined diagnostic frontier is only an inventory: each disjunct is an
existing public no-go surface once its connector package is supplied. -/
theorem no_remainingPublicRawActionFrontier
    (h : D19ActsOnMoore57 V Γ) :
    ¬ RemainingPublicRawActionFrontier.{u, uP} h := by
  intro hfrontier
  rcases hfrontier with hConcrete | hFinal | hAllOffset | hBranch
  · exact no_remainingConcreteOrbitDataConnector h hConcrete
  · exact no_remainingPublicFinalBoundaryConnector h hFinal
  · exact no_remainingAllOffsetClosedConnector h hAllOffset
  · exact no_remainingBranchReflectionConnector h hBranch

end

end Moore57
