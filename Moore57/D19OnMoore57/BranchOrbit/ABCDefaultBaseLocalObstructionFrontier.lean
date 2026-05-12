import Moore57.D19OnMoore57.BranchOrbit.ABCDefaultBaseReferenceFrontier
import Moore57.D19OnMoore57.BranchOrbit.ABCMidpointDisjointnessFrontier
import Moore57.D19OnMoore57.BranchOrbit.ABCReferenceMatchingLocalObstructionBridge

/-!
# Default-base local-obstruction frontier

This file specializes the default-base/fixed-center-leaf reference connector
to the finite midpoint-disjointness and local-obstruction packages.  It keeps
the default base and fixed-center-leaf provenance explicit while replacing the
raw disjointness field with boundary shapes closer to the current fixed-star
final inputs.
-/

namespace Moore57

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

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
