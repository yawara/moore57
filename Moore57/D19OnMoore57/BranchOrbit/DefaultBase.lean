import Moore57.D19OnMoore57.BranchOrbit.ABCCenterNeighborBaseFrontier
import Moore57.D19OnMoore57.BranchOrbit.ABCReferenceFiberMatchingEquationFrontier
import Moore57.D19OnMoore57.BranchOrbit.ABCMidpointDisjointnessFrontier
import Moore57.D19OnMoore57.BranchOrbit.ABCReferenceMatchingLocalObstructionBridge

/-!
# Default-base fixed-center-leaf frontier and local obstruction

This file unifies two thematic layers of the default-base/fixed-center-leaf
frontier:

* **Reference frontier** (formerly `ABCDefaultBaseReferenceFrontier`):
  the default-base/fixed-center-leaf reference-fiber matching-equation
  connector with the raw midpoint-exception/A-fixing-support disjointness
  field.
* **Local obstruction frontier** (formerly
  `ABCDefaultBaseLocalObstructionFrontier`): replaces the raw disjointness
  field by the finite midpoint-disjointness package and by the
  reference-matching/local-obstruction package, keeping the default base
  and fixed-center-leaf provenance explicit.

The combined frontier (`ABCDefaultBaseCombinedFrontier`) lives in a separate
file because it independently depends on `SupportCardFrontier`, `NoFrontier`,
and the lean-aware default-base frontier.
-/

namespace Moore57

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

namespace BranchOrbitABCReflectionLabeling

variable {h : D19ActsOnMoore57 V Γ}

/-! ## Default-base labeled reflection pair -/

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

/-! ## Default-base reference-matching frontier -/

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

/-! ## Default-base local-obstruction frontier -/

namespace BranchOrbitABCReflectionLabeling

variable {h : D19ActsOnMoore57 V Γ}

namespace ReferenceMatchingLocalObstructionBoundary

variable {star : ReflectionFixedStarBoundary h}
variable {labeling : BranchOrbitABCReflectionLabeling h}

/-- The reference-matching/local-obstruction package is a concrete source of
the finite midpoint-disjointness wrapper: A-fixing gives support size,
singleton fixedness rules out card one, and endpoint obstruction rules out
card two using the reference-matching criterion. -/
def toReferenceFiberMatchingEquationMidpointDisjointnessBoundary
    (boundary : ReferenceMatchingLocalObstructionBoundary star labeling) :
    ReferenceFiberMatchingEquationMidpointDisjointnessBoundary labeling where
  referenceMatching := boundary.referenceMatching
  support_card_boundary :=
    boundary.aFixing.toAFixingReflectionFixedNeighborCardBoundary
  no_card_one := boundary.singletonFixed.no_card_one
  noAllEndpointAdj := boundary.noAllEndpointAdj

end ReferenceMatchingLocalObstructionBoundary

end BranchOrbitABCReflectionLabeling

/-- Default-base/fixed-center-leaf connector with the finite
midpoint-disjointness package replacing the raw disjointness field. -/
structure RemainingDefaultBaseFixedCenterLeafMidpointDisjointnessConnector
    (h : D19ActsOnMoore57 V Γ) where
  fixedCenterLeaf : ReflectionFixedCenterLeafBoundary h
  k : ZMod 19
  midpointDisjointness :
    BranchOrbitABCReflectionLabeling.ReferenceFiberMatchingEquationMidpointDisjointnessBoundary
      (BranchOrbitABCReflectionLabeling.fixedCenterLeafDefaultBaseLabeling
        (h := h) fixedCenterLeaf k)

namespace RemainingDefaultBaseFixedCenterLeafMidpointDisjointnessConnector

variable {h : D19ActsOnMoore57 V Γ}

/-- Collapse the finite midpoint-disjointness package to the existing
default-base fixed-center-leaf reference connector. -/
noncomputable def toRemainingDefaultBaseFixedCenterLeafReferenceConnector
    (connector :
      RemainingDefaultBaseFixedCenterLeafMidpointDisjointnessConnector h) :
    RemainingDefaultBaseFixedCenterLeafReferenceConnector h where
  fixedCenterLeaf := connector.fixedCenterLeaf
  k := connector.k
  referenceMatching := connector.midpointDisjointness.referenceMatching
  midpointExceptionDisjoint :=
    connector.midpointDisjointness
      |>.toMidpointExceptionDisjointAFixingSupportBoundary

/-- Collapse to the fixed-center-leaf matching-equation connector. -/
noncomputable def toRemainingFixedCenterLeafMatchingEquationConnector
    (connector :
      RemainingDefaultBaseFixedCenterLeafMidpointDisjointnessConnector h) :
    RemainingFixedCenterLeafMatchingEquationConnector h :=
  connector.toRemainingDefaultBaseFixedCenterLeafReferenceConnector
    |>.toRemainingFixedCenterLeafMatchingEquationConnector

/-- Collapse to the raw labeled-reflection matching-equation connector. -/
noncomputable def toRemainingLabeledReflectionMatchingEquationConnector
    (connector :
      RemainingDefaultBaseFixedCenterLeafMidpointDisjointnessConnector h) :
    RemainingLabeledReflectionMatchingEquationConnector h :=
  connector.toRemainingFixedCenterLeafMatchingEquationConnector
    |>.toRemainingLabeledReflectionMatchingEquationConnector

end RemainingDefaultBaseFixedCenterLeafMidpointDisjointnessConnector

/-- With representation components supplied, the finite midpoint-disjointness
default-base connector is refuted by the existing fixed-center-leaf
matching-equation frontier. -/
theorem no_remainingDefaultBaseFixedCenterLeafMidpointDisjointnessConnector_of_components
    (h : D19ActsOnMoore57 V Γ) :
    ¬ ∃ _representationComponents : RemainingRepresentationComponents h,
        Nonempty
          (RemainingDefaultBaseFixedCenterLeafMidpointDisjointnessConnector
            h) := by
  rintro ⟨representationComponents, ⟨connector⟩⟩
  exact no_remainingFixedCenterLeafMatchingEquationConnector_of_components h
    ⟨representationComponents,
      ⟨connector.toRemainingFixedCenterLeafMatchingEquationConnector⟩⟩

/-- Default-base/fixed-center-leaf connector whose disjointness input is
supplied by the reference-matching/local-obstruction package. -/
structure RemainingDefaultBaseFixedCenterLeafLocalObstructionConnector
    (h : D19ActsOnMoore57 V Γ) where
  star : ReflectionFixedStarBoundary h
  fixedCenterLeaf : ReflectionFixedCenterLeafBoundary h
  k : ZMod 19
  localObstruction :
    BranchOrbitABCReflectionLabeling.ReferenceMatchingLocalObstructionBoundary
      star
      (BranchOrbitABCReflectionLabeling.fixedCenterLeafDefaultBaseLabeling
        (h := h) fixedCenterLeaf k)

namespace RemainingDefaultBaseFixedCenterLeafLocalObstructionConnector

variable {h : D19ActsOnMoore57 V Γ}

/-- Convert the local-obstruction connector to the finite midpoint-disjointness
default-base connector. -/
noncomputable def toRemainingDefaultBaseFixedCenterLeafMidpointDisjointnessConnector
    (connector :
      RemainingDefaultBaseFixedCenterLeafLocalObstructionConnector h) :
    RemainingDefaultBaseFixedCenterLeafMidpointDisjointnessConnector h where
  fixedCenterLeaf := connector.fixedCenterLeaf
  k := connector.k
  midpointDisjointness :=
    connector.localObstruction
      |>.toReferenceFiberMatchingEquationMidpointDisjointnessBoundary

/-- Collapse the local-obstruction package to the existing default-base
fixed-center-leaf reference connector. -/
noncomputable def toRemainingDefaultBaseFixedCenterLeafReferenceConnector
    (connector :
      RemainingDefaultBaseFixedCenterLeafLocalObstructionConnector h) :
    RemainingDefaultBaseFixedCenterLeafReferenceConnector h :=
  connector.toRemainingDefaultBaseFixedCenterLeafMidpointDisjointnessConnector
    |>.toRemainingDefaultBaseFixedCenterLeafReferenceConnector

/-- Collapse to the fixed-center-leaf matching-equation connector. -/
noncomputable def toRemainingFixedCenterLeafMatchingEquationConnector
    (connector :
      RemainingDefaultBaseFixedCenterLeafLocalObstructionConnector h) :
    RemainingFixedCenterLeafMatchingEquationConnector h :=
  connector.toRemainingDefaultBaseFixedCenterLeafReferenceConnector
    |>.toRemainingFixedCenterLeafMatchingEquationConnector

/-- Collapse to the raw labeled-reflection matching-equation connector. -/
noncomputable def toRemainingLabeledReflectionMatchingEquationConnector
    (connector :
      RemainingDefaultBaseFixedCenterLeafLocalObstructionConnector h) :
    RemainingLabeledReflectionMatchingEquationConnector h :=
  connector.toRemainingFixedCenterLeafMatchingEquationConnector
    |>.toRemainingLabeledReflectionMatchingEquationConnector

end RemainingDefaultBaseFixedCenterLeafLocalObstructionConnector

/-- With representation components supplied, the local-obstruction default-base
connector is refuted by the existing fixed-center-leaf matching-equation
frontier. -/
theorem no_remainingDefaultBaseFixedCenterLeafLocalObstructionConnector_of_components
    (h : D19ActsOnMoore57 V Γ) :
    ¬ ∃ _representationComponents : RemainingRepresentationComponents h,
        Nonempty
          (RemainingDefaultBaseFixedCenterLeafLocalObstructionConnector h) := by
  rintro ⟨representationComponents, ⟨connector⟩⟩
  exact no_remainingFixedCenterLeafMatchingEquationConnector_of_components h
    ⟨representationComponents,
      ⟨connector.toRemainingFixedCenterLeafMatchingEquationConnector⟩⟩

end

end Moore57
