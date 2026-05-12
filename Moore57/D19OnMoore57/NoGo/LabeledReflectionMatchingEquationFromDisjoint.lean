import Moore57.D19OnMoore57.BranchOrbit.ABCReferenceFiberMatchingEquationFrontier

/-!
# Labeled-reflection matching equation from disjoint reference fibers

This file combines the reference-fiber matching-equation frontier with the
public labeled-reflection matching-equation connector.  It stays on the
non-representation side: the only inputs are a labeled reflection pair and the
two reference-fiber boundary packages on the pair's canonical labeling.
-/

namespace Moore57

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- A labeled reflection pair plus the reference matching pipeline and
midpoint-exception disjointness boundary on its canonical labeling supplies the
remaining labeled-reflection matching-equation connector. -/
theorem remainingLabeledReflectionMatchingEquationConnector_of_referenceMatchingPipeline_disjoint
    {h : D19ActsOnMoore57 V Γ}
    (hp : BranchOrbitABCReflectionLabeling.HasLabeledReflectionPair h)
    (referenceMatching :
      BranchOrbitABCReflectionLabeling.ReferenceMatchingPipelineBoundary
        (BranchOrbitABCReflectionLabeling.ofHasLabeledReflectionPair
          (h := h) hp))
    (disjoint :
      BranchOrbitABCReflectionLabeling.MidpointExceptionDisjointAFixingSupportBoundary
        (BranchOrbitABCReflectionLabeling.ofHasLabeledReflectionPair
          (h := h) hp)) :
    RemainingLabeledReflectionMatchingEquationConnector h :=
  ⟨hp,
    BranchOrbitABCReflectionLabeling.referenceFiberMatchingEquationCardTwoOfPair_of_referenceMatchingPipeline_disjoint
      (h := h) hp referenceMatching disjoint⟩

/-- Bundled non-representation connector from the labeled reflection pair and
the two disjoint-reference-fiber boundary packages to the public
matching-equation connector. -/
structure RemainingLabeledReflectionMatchingEquationFromDisjointConnector
    (h : D19ActsOnMoore57 V Γ) : Prop where
  pair : BranchOrbitABCReflectionLabeling.HasLabeledReflectionPair h
  referenceMatching :
    BranchOrbitABCReflectionLabeling.ReferenceMatchingPipelineBoundary
      (BranchOrbitABCReflectionLabeling.ofHasLabeledReflectionPair
        (h := h) pair)
  midpointExceptionDisjoint :
    BranchOrbitABCReflectionLabeling.MidpointExceptionDisjointAFixingSupportBoundary
      (BranchOrbitABCReflectionLabeling.ofHasLabeledReflectionPair
        (h := h) pair)

namespace RemainingLabeledReflectionMatchingEquationFromDisjointConnector

variable {h : D19ActsOnMoore57 V Γ}

/-- Forget the disjoint-reference-fiber provenance back to the raw
labeled-reflection matching-equation connector. -/
theorem toRemainingLabeledReflectionMatchingEquationConnector
    (connector :
      RemainingLabeledReflectionMatchingEquationFromDisjointConnector h) :
    RemainingLabeledReflectionMatchingEquationConnector h :=
  remainingLabeledReflectionMatchingEquationConnector_of_referenceMatchingPipeline_disjoint
    (h := h) connector.pair connector.referenceMatching
    connector.midpointExceptionDisjoint

end RemainingLabeledReflectionMatchingEquationFromDisjointConnector

/-- With representation components supplied, the bundled
disjoint-reference-fiber connector is impossible by the existing
labeled-reflection matching-equation no-go theorem. -/
theorem no_remainingLabeledReflectionMatchingEquationFromDisjointConnector_of_components
    (h : D19ActsOnMoore57 V Γ) :
    ¬ ∃ _representationComponents : RemainingRepresentationComponents h,
        RemainingLabeledReflectionMatchingEquationFromDisjointConnector h := by
  rintro ⟨representationComponents, connector⟩
  exact no_remainingLabeledReflectionMatchingEquationConnector_of_components h
    ⟨representationComponents,
      connector.toRemainingLabeledReflectionMatchingEquationConnector⟩

end

end Moore57
