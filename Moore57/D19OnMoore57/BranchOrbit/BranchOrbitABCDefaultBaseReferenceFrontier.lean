import Moore57.D19OnMoore57.BranchOrbit.BranchOrbitABCCenterNeighborBaseFrontier
import Moore57.D19OnMoore57.BranchOrbit.BranchOrbitABCReferenceFiberMatchingEquationFrontier

/-!
# Default-base reference matching frontier

This file specializes the fixed-center-leaf/default-center-neighbor-base
frontier to the reference-fiber matching-equation connector.  The default base
and the fixed-center-leaf boundary supply the labeled reflection pair; the
remaining non-representation fields are the reference matching pipeline and
the midpoint-exception/A-fixing-support disjointness boundary.
-/

namespace Moore57

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

namespace BranchOrbitABCReflectionLabeling

variable {h : D19ActsOnMoore57 V Γ}

/-- Stable name for the labeled reflection-pair boundary obtained from the
default center-neighbor base and a fixed-center-leaf boundary. -/
noncomputable abbrev fixedCenterLeafDefaultBasePair
    (fixedCenterLeaf : ReflectionFixedCenterLeafBoundary h)
    (k : ZMod 19) :
    HasLabeledReflectionPair h :=
  hasLabeledReflectionPair_of_fixedCenterLeaf_defaultBase
    (h := h) fixedCenterLeaf k

/-- Stable name for the canonical labeling attached to the default-base
fixed-center-leaf pair. -/
noncomputable abbrev fixedCenterLeafDefaultBaseLabeling
    (fixedCenterLeaf : ReflectionFixedCenterLeafBoundary h)
    (k : ZMod 19) :
    BranchOrbitABCReflectionLabeling h :=
  ofHasLabeledReflectionPair
    (h := h)
    (fixedCenterLeafDefaultBasePair (h := h) fixedCenterLeaf k)

end BranchOrbitABCReflectionLabeling

/-- Bundled default-base/fixed-center-leaf reference frontier.  The default
center-neighbor base is fixed by
`hasLabeledReflectionPair_of_fixedCenterLeaf_defaultBase`; the remaining
non-representation fields are named explicitly. -/
structure RemainingDefaultBaseFixedCenterLeafReferenceConnector
    (h : D19ActsOnMoore57 V Γ) where
  fixedCenterLeaf : ReflectionFixedCenterLeafBoundary h
  k : ZMod 19
  referenceMatching :
    BranchOrbitABCReflectionLabeling.ReferenceMatchingPipelineBoundary
      (BranchOrbitABCReflectionLabeling.fixedCenterLeafDefaultBaseLabeling
        (h := h) fixedCenterLeaf k)
  midpointExceptionDisjoint :
    BranchOrbitABCReflectionLabeling.MidpointExceptionDisjointAFixingSupportBoundary
      (BranchOrbitABCReflectionLabeling.fixedCenterLeafDefaultBaseLabeling
        (h := h) fixedCenterLeaf k)

namespace RemainingDefaultBaseFixedCenterLeafReferenceConnector

variable {h : D19ActsOnMoore57 V Γ}

/-- Rebundle the named remaining fields as the reference-fiber
matching-equation frontier boundary. -/
noncomputable def toReferenceFiberMatchingEquationFrontierBoundary
    (connector : RemainingDefaultBaseFixedCenterLeafReferenceConnector h) :
    BranchOrbitABCReflectionLabeling.ReferenceFiberMatchingEquationFrontierBoundary
      (BranchOrbitABCReflectionLabeling.fixedCenterLeafDefaultBaseLabeling
        (h := h) connector.fixedCenterLeaf connector.k) where
  referenceMatching := connector.referenceMatching
  midpointExceptionDisjoint := connector.midpointExceptionDisjoint

/-- Collapse the reference-matching pipeline and disjointness fields to the
two-solution reference-fiber matching equation for the default-base pair. -/
theorem referenceMatchingEquationCardTwo
    (connector : RemainingDefaultBaseFixedCenterLeafReferenceConnector h) :
    BranchOrbitABCReflectionLabeling.ReferenceFiberMatchingEquationCardTwoOfPair
      (h := h)
      (BranchOrbitABCReflectionLabeling.fixedCenterLeafDefaultBasePair
        (h := h) connector.fixedCenterLeaf connector.k) :=
  BranchOrbitABCReflectionLabeling.ReferenceFiberMatchingEquationFrontierBoundary.toReferenceFiberMatchingEquationCardTwoOfPair
    (h := h)
    (BranchOrbitABCReflectionLabeling.fixedCenterLeafDefaultBasePair
      (h := h) connector.fixedCenterLeaf connector.k)
    connector.toReferenceFiberMatchingEquationFrontierBoundary

/-- Forget the reference-pipeline provenance back to the fixed-center-leaf
matching-equation connector. -/
noncomputable def toRemainingFixedCenterLeafMatchingEquationConnector
    (connector : RemainingDefaultBaseFixedCenterLeafReferenceConnector h) :
    RemainingFixedCenterLeafMatchingEquationConnector h where
  fixedCenterLeaf := connector.fixedCenterLeaf
  k := connector.k
  referenceMatchingEquationCardTwo :=
    connector.referenceMatchingEquationCardTwo

/-- Forget all default-base/reference-pipeline provenance back to the raw
labeled-reflection matching-equation connector. -/
noncomputable def toRemainingLabeledReflectionMatchingEquationConnector
    (connector : RemainingDefaultBaseFixedCenterLeafReferenceConnector h) :
    RemainingLabeledReflectionMatchingEquationConnector h :=
  connector.toRemainingFixedCenterLeafMatchingEquationConnector
    |>.toRemainingLabeledReflectionMatchingEquationConnector

end RemainingDefaultBaseFixedCenterLeafReferenceConnector

/-- Once representation components are supplied, the default-base
fixed-center-leaf reference connector is refuted by the existing
fixed-center-leaf matching-equation frontier. -/
theorem no_remainingDefaultBaseFixedCenterLeafReferenceConnector_of_components
    (h : D19ActsOnMoore57 V Γ) :
    ¬ ∃ _representationComponents : RemainingRepresentationComponents h,
        Nonempty (RemainingDefaultBaseFixedCenterLeafReferenceConnector h) := by
  rintro ⟨representationComponents, ⟨connector⟩⟩
  exact no_remainingFixedCenterLeafMatchingEquationConnector_of_components h
    ⟨representationComponents,
      ⟨connector.toRemainingFixedCenterLeafMatchingEquationConnector⟩⟩

end

end Moore57
