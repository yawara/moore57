import Moore57.D19OnMoore57.Reflection.ReflectionRemainingCandidateGeometryBoundary
import Moore57.D19OnMoore57.BranchOrbit.BranchOrbitABCDefaultBaseLocalObstructionFrontier

/-!
# Local-leaf connectors for remaining reflection candidates

This file keeps the trace-remaining/local-leaf route close to the raw
`RemainingNon56FixedCenterLeafIndexMatchingEquationConnector`.  A local
`ReflectionFixedCenterLeafAt h k` canonically supplies a moved default-base
center-neighbor index; the wrappers below only add the reference matching
inputs needed to build the existing index matching-equation connector.
-/

namespace Moore57

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

namespace ReflectionFixedCenterLeafAt

variable {h : D19ActsOnMoore57 V Γ} {k : ZMod 19}

/-- Canonical moved default-base center-neighbor index supplied by a local
fixed-center leaf. -/
noncomputable def remainingCenterNeighborBaseMovedIndex
    (leaf : ReflectionFixedCenterLeafAt h k) :
    { b : Fin 3 //
      BranchOrbitABCReflectionLabeling.reflectionCenterNeighborOrbitIndex
        (h := h)
        (remainingCenterNeighborOrbitBase h)
        (remainingCenterNeighborOrbitBase_adj (h := h))
        (remainingCenterNeighborOrbitBase_cover (h := h))
        k b ≠ b } :=
  let moved := leaf.exists_remainingCenterNeighborBase_index_ne
  ⟨Classical.choose moved, Classical.choose_spec moved⟩

/-- The labeled reflection pair induced by the canonical moved index of a
local fixed-center leaf. -/
noncomputable abbrev remainingCenterNeighborBasePair
    (leaf : ReflectionFixedCenterLeafAt h k) :
    BranchOrbitABCReflectionLabeling.HasLabeledReflectionPair h :=
  BranchOrbitABCReflectionLabeling.hasLabeledReflectionPair_of_remainingCenterNeighborBase_index_ne
    (h := h) leaf.remainingCenterNeighborBaseMovedIndex.property

/-- The canonical labeling attached to the local-leaf default-base pair. -/
noncomputable abbrev remainingCenterNeighborBaseLabeling
    (leaf : ReflectionFixedCenterLeafAt h k) :
    BranchOrbitABCReflectionLabeling h :=
  BranchOrbitABCReflectionLabeling.ofHasLabeledReflectionPair
    (h := h) leaf.remainingCenterNeighborBasePair

end ReflectionFixedCenterLeafAt

/-- Local-leaf connector whose extra inputs are the reference matching pipeline
and raw midpoint-exception/A-fixing-support disjointness for the induced
default-base labeled pair. -/
structure RemainingNon56FixedCenterLeafReferenceConnector
    (h : D19ActsOnMoore57 V Γ) where
  k : ZMod 19
  non56Candidate : ReflectionTraceRemainingNon56Candidate h k
  leaf : ReflectionFixedCenterLeafAt h k
  referenceMatching :
    BranchOrbitABCReflectionLabeling.ReferenceMatchingPipelineBoundary
      leaf.remainingCenterNeighborBaseLabeling
  midpointExceptionDisjoint :
    BranchOrbitABCReflectionLabeling.MidpointExceptionDisjointAFixingSupportBoundary
      leaf.remainingCenterNeighborBaseLabeling

namespace RemainingNon56FixedCenterLeafReferenceConnector

variable {h : D19ActsOnMoore57 V Γ}

/-- Rebundle the reference-matching inputs as the frontier package. -/
noncomputable def toReferenceFiberMatchingEquationFrontierBoundary
    (connector : RemainingNon56FixedCenterLeafReferenceConnector h) :
    BranchOrbitABCReflectionLabeling.ReferenceFiberMatchingEquationFrontierBoundary
      connector.leaf.remainingCenterNeighborBaseLabeling where
  referenceMatching := connector.referenceMatching
  midpointExceptionDisjoint := connector.midpointExceptionDisjoint

/-- Collapse the reference-matching inputs to the card-two equation for the
local-leaf induced pair. -/
theorem referenceMatchingEquationCardTwo
    (connector : RemainingNon56FixedCenterLeafReferenceConnector h) :
    BranchOrbitABCReflectionLabeling.ReferenceFiberMatchingEquationCardTwoOfPair
      (h := h) connector.leaf.remainingCenterNeighborBasePair :=
  BranchOrbitABCReflectionLabeling.ReferenceFiberMatchingEquationFrontierBoundary.toReferenceFiberMatchingEquationCardTwoOfPair
    (h := h) connector.leaf.remainingCenterNeighborBasePair
    connector.toReferenceFiberMatchingEquationFrontierBoundary

/-- Build the trace-remaining local-leaf index matching-equation connector. -/
noncomputable def toRemainingNon56FixedCenterLeafIndexMatchingEquationConnector
    (connector : RemainingNon56FixedCenterLeafReferenceConnector h) :
    RemainingNon56FixedCenterLeafIndexMatchingEquationConnector h where
  k := connector.k
  non56Candidate := connector.non56Candidate
  leaf := connector.leaf
  b := connector.leaf.remainingCenterNeighborBaseMovedIndex.val
  hmove := connector.leaf.remainingCenterNeighborBaseMovedIndex.property
  referenceMatchingEquationCardTwo := connector.referenceMatchingEquationCardTwo

/-- Forget to the reflected-index matching-equation connector. -/
noncomputable def toRemainingReflectionIndexMatchingEquationConnector
    (connector : RemainingNon56FixedCenterLeafReferenceConnector h) :
    RemainingReflectionIndexMatchingEquationConnector h :=
  connector.toRemainingNon56FixedCenterLeafIndexMatchingEquationConnector
    |>.toRemainingReflectionIndexMatchingEquationConnector

/-- Forget to the raw labeled-reflection matching-equation connector. -/
noncomputable def toRemainingLabeledReflectionMatchingEquationConnector
    (connector : RemainingNon56FixedCenterLeafReferenceConnector h) :
    RemainingLabeledReflectionMatchingEquationConnector h :=
  connector.toRemainingNon56FixedCenterLeafIndexMatchingEquationConnector
    |>.toRemainingLabeledReflectionMatchingEquationConnector

end RemainingNon56FixedCenterLeafReferenceConnector

/-- Component-level no-go inherited from the raw local-leaf connector. -/
theorem no_remainingNon56FixedCenterLeafReferenceConnector_of_components
    (h : D19ActsOnMoore57 V Γ) :
    ¬ ∃ _representationComponents : RemainingRepresentationComponents h,
        Nonempty (RemainingNon56FixedCenterLeafReferenceConnector h) := by
  rintro ⟨representationComponents, ⟨connector⟩⟩
  exact no_remainingNon56FixedCenterLeafIndexMatchingEquationConnector_of_components h
    ⟨representationComponents,
      ⟨connector.toRemainingNon56FixedCenterLeafIndexMatchingEquationConnector⟩⟩

/-- Local-leaf connector whose disjointness input is the finite
midpoint-disjointness package for the induced default-base labeled pair. -/
structure RemainingNon56FixedCenterLeafMidpointDisjointnessConnector
    (h : D19ActsOnMoore57 V Γ) where
  k : ZMod 19
  non56Candidate : ReflectionTraceRemainingNon56Candidate h k
  leaf : ReflectionFixedCenterLeafAt h k
  midpointDisjointness :
    BranchOrbitABCReflectionLabeling.ReferenceFiberMatchingEquationMidpointDisjointnessBoundary
      leaf.remainingCenterNeighborBaseLabeling

namespace RemainingNon56FixedCenterLeafMidpointDisjointnessConnector

variable {h : D19ActsOnMoore57 V Γ}

/-- Collapse the finite midpoint-disjointness package to the raw
reference/disjointness connector. -/
noncomputable def toRemainingNon56FixedCenterLeafReferenceConnector
    (connector :
      RemainingNon56FixedCenterLeafMidpointDisjointnessConnector h) :
    RemainingNon56FixedCenterLeafReferenceConnector h where
  k := connector.k
  non56Candidate := connector.non56Candidate
  leaf := connector.leaf
  referenceMatching := connector.midpointDisjointness.referenceMatching
  midpointExceptionDisjoint :=
    connector.midpointDisjointness
      |>.toMidpointExceptionDisjointAFixingSupportBoundary

/-- Build the trace-remaining local-leaf index matching-equation connector. -/
noncomputable def toRemainingNon56FixedCenterLeafIndexMatchingEquationConnector
    (connector :
      RemainingNon56FixedCenterLeafMidpointDisjointnessConnector h) :
    RemainingNon56FixedCenterLeafIndexMatchingEquationConnector h :=
  connector.toRemainingNon56FixedCenterLeafReferenceConnector
    |>.toRemainingNon56FixedCenterLeafIndexMatchingEquationConnector

/-- Forget to the reflected-index matching-equation connector. -/
noncomputable def toRemainingReflectionIndexMatchingEquationConnector
    (connector :
      RemainingNon56FixedCenterLeafMidpointDisjointnessConnector h) :
    RemainingReflectionIndexMatchingEquationConnector h :=
  connector.toRemainingNon56FixedCenterLeafIndexMatchingEquationConnector
    |>.toRemainingReflectionIndexMatchingEquationConnector

/-- Forget to the raw labeled-reflection matching-equation connector. -/
noncomputable def toRemainingLabeledReflectionMatchingEquationConnector
    (connector :
      RemainingNon56FixedCenterLeafMidpointDisjointnessConnector h) :
    RemainingLabeledReflectionMatchingEquationConnector h :=
  connector.toRemainingNon56FixedCenterLeafIndexMatchingEquationConnector
    |>.toRemainingLabeledReflectionMatchingEquationConnector

end RemainingNon56FixedCenterLeafMidpointDisjointnessConnector

/-- Component-level no-go inherited from the raw local-leaf connector. -/
theorem no_remainingNon56FixedCenterLeafMidpointDisjointnessConnector_of_components
    (h : D19ActsOnMoore57 V Γ) :
    ¬ ∃ _representationComponents : RemainingRepresentationComponents h,
        Nonempty
          (RemainingNon56FixedCenterLeafMidpointDisjointnessConnector h) := by
  rintro ⟨representationComponents, ⟨connector⟩⟩
  exact no_remainingNon56FixedCenterLeafIndexMatchingEquationConnector_of_components h
    ⟨representationComponents,
      ⟨connector.toRemainingNon56FixedCenterLeafIndexMatchingEquationConnector⟩⟩

/-- Local-leaf connector whose disjointness input is supplied by the
reference-matching/local-obstruction package for the induced default-base
labeled pair. -/
structure RemainingNon56FixedCenterLeafLocalObstructionConnector
    (h : D19ActsOnMoore57 V Γ) where
  star : ReflectionFixedStarBoundary h
  k : ZMod 19
  non56Candidate : ReflectionTraceRemainingNon56Candidate h k
  leaf : ReflectionFixedCenterLeafAt h k
  localObstruction :
    BranchOrbitABCReflectionLabeling.ReferenceMatchingLocalObstructionBoundary
      star
      leaf.remainingCenterNeighborBaseLabeling

namespace RemainingNon56FixedCenterLeafLocalObstructionConnector

variable {h : D19ActsOnMoore57 V Γ}

/-- Convert the local-obstruction package to the finite midpoint-disjointness
connector. -/
noncomputable def toRemainingNon56FixedCenterLeafMidpointDisjointnessConnector
    (connector :
      RemainingNon56FixedCenterLeafLocalObstructionConnector h) :
    RemainingNon56FixedCenterLeafMidpointDisjointnessConnector h where
  k := connector.k
  non56Candidate := connector.non56Candidate
  leaf := connector.leaf
  midpointDisjointness :=
    connector.localObstruction
      |>.toReferenceFiberMatchingEquationMidpointDisjointnessBoundary

/-- Collapse the local-obstruction package to the raw reference/disjointness
connector. -/
noncomputable def toRemainingNon56FixedCenterLeafReferenceConnector
    (connector :
      RemainingNon56FixedCenterLeafLocalObstructionConnector h) :
    RemainingNon56FixedCenterLeafReferenceConnector h :=
  connector.toRemainingNon56FixedCenterLeafMidpointDisjointnessConnector
    |>.toRemainingNon56FixedCenterLeafReferenceConnector

/-- Build the trace-remaining local-leaf index matching-equation connector. -/
noncomputable def toRemainingNon56FixedCenterLeafIndexMatchingEquationConnector
    (connector :
      RemainingNon56FixedCenterLeafLocalObstructionConnector h) :
    RemainingNon56FixedCenterLeafIndexMatchingEquationConnector h :=
  connector.toRemainingNon56FixedCenterLeafReferenceConnector
    |>.toRemainingNon56FixedCenterLeafIndexMatchingEquationConnector

/-- Forget to the reflected-index matching-equation connector. -/
noncomputable def toRemainingReflectionIndexMatchingEquationConnector
    (connector :
      RemainingNon56FixedCenterLeafLocalObstructionConnector h) :
    RemainingReflectionIndexMatchingEquationConnector h :=
  connector.toRemainingNon56FixedCenterLeafIndexMatchingEquationConnector
    |>.toRemainingReflectionIndexMatchingEquationConnector

/-- Forget to the raw labeled-reflection matching-equation connector. -/
noncomputable def toRemainingLabeledReflectionMatchingEquationConnector
    (connector :
      RemainingNon56FixedCenterLeafLocalObstructionConnector h) :
    RemainingLabeledReflectionMatchingEquationConnector h :=
  connector.toRemainingNon56FixedCenterLeafIndexMatchingEquationConnector
    |>.toRemainingLabeledReflectionMatchingEquationConnector

end RemainingNon56FixedCenterLeafLocalObstructionConnector

/-- Component-level no-go inherited from the raw local-leaf connector. -/
theorem no_remainingNon56FixedCenterLeafLocalObstructionConnector_of_components
    (h : D19ActsOnMoore57 V Γ) :
    ¬ ∃ _representationComponents : RemainingRepresentationComponents h,
        Nonempty
          (RemainingNon56FixedCenterLeafLocalObstructionConnector h) := by
  rintro ⟨representationComponents, ⟨connector⟩⟩
  exact no_remainingNon56FixedCenterLeafIndexMatchingEquationConnector_of_components h
    ⟨representationComponents,
      ⟨connector.toRemainingNon56FixedCenterLeafIndexMatchingEquationConnector⟩⟩

end

end Moore57
