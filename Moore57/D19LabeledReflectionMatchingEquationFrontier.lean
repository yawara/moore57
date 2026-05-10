import Moore57.D19RemainingRawActionFrontier
import Moore57.ReflectionFixedCenterLeafBoundary

/-!
# Labeled reflection matching-equation frontier

This file keeps the remaining labeled-reflection matching-equation connector
separate from the broader raw-action frontier.  It records only wiring already
available in the branch/reflection modules:

* a moved reflection index supplies the labeled reflection pair;
* a fixed-neighbor bound supplies such a moved index for the chosen
  center-neighbor decomposition;
* a fixed-center-leaf boundary supplies the fixed-neighbor bound.

In all cases the reference-fiber matching equation itself remains an explicit
field.
-/

namespace Moore57

open Finset

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

local instance instD19LabeledReflectionMatchingEquationFrontierPFintype
    {h : D19ActsOnMoore57 V Γ}
    (labeling : BranchOrbitABCReflectionLabeling h) :
    Fintype labeling.data.toAFiberCoordinates.P :=
  labeling.data.toAFiberCoordinates.P_fintype

local instance instD19LabeledReflectionMatchingEquationFrontierBranchDataPFintype
    {h : D19ActsOnMoore57 V Γ}
    (labeling : BranchOrbitABCReflectionLabeling h) :
    Fintype labeling.data.toBranchOrbitABCData.toAFiberCoordinates.P :=
  labeling.data.toBranchOrbitABCData.toAFiberCoordinates.P_fintype

local instance instD19LabeledReflectionMatchingEquationFrontierDecidableEq
    (α : Type*) : DecidableEq α :=
  Classical.decEq α

namespace BranchOrbitABCReflectionLabeling

variable {h : D19ActsOnMoore57 V Γ}

/-- The reference-fiber matching equation with two solutions for the labeling
canonically built from a labeled reflection pair. -/
abbrev ReferenceFiberMatchingEquationCardTwoOfPair
    (hp : HasLabeledReflectionPair h) : Prop :=
  let labeling := ofHasLabeledReflectionPair (h := h) hp
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

end BranchOrbitABCReflectionLabeling

/-- The raw frontier connector is exactly a labeled reflection pair plus the
reference-fiber matching equation for the induced labeling. -/
theorem remainingLabeledReflectionMatchingEquationConnector_iff
    (h : D19ActsOnMoore57 V Γ) :
    RemainingLabeledReflectionMatchingEquationConnector h ↔
      ∃ hp : BranchOrbitABCReflectionLabeling.HasLabeledReflectionPair h,
        BranchOrbitABCReflectionLabeling.ReferenceFiberMatchingEquationCardTwoOfPair
          (h := h) hp :=
  Iff.rfl

/-! ## Explicit moved reflected-orbit index -/

/-- Connector form where the labeled reflection pair is supplied by a
nontrivial reflected action on the three center-neighbor rotation orbits.  The
only extra field is the reference-fiber matching equation for the induced
labeling. -/
structure RemainingReflectionIndexMatchingEquationConnector
    (h : D19ActsOnMoore57 V Γ) where
  base : Fin 3 → V
  base_adj : ∀ q : Fin 3, Γ.Adj h.rotationFixedCenter (base q)
  base_pairwise_disjoint :
    ∀ q r : Fin 3, q ≠ r →
      Disjoint (h.rotationOrbitFinset (base q))
        (h.rotationOrbitFinset (base r))
  base_cover :
    Γ.neighborFinset h.rotationFixedCenter = h.orbitFamilyUnion base
  k : ZMod 19
  b : Fin 3
  hmove :
    BranchOrbitABCReflectionLabeling.reflectionCenterNeighborOrbitIndex
      (h := h) base base_adj base_cover k b ≠ b
  referenceMatchingEquationCardTwo :
    BranchOrbitABCReflectionLabeling.ReferenceFiberMatchingEquationCardTwoOfPair
      (h := h)
      (BranchOrbitABCReflectionLabeling.hasLabeledReflectionPair_of_reflectionCenterNeighborOrbitIndex_ne
        (h := h) base base_adj base_pairwise_disjoint base_cover hmove)

namespace RemainingReflectionIndexMatchingEquationConnector

variable {h : D19ActsOnMoore57 V Γ}

/-- Forget the reflected-orbit-index provenance back to the raw labeled
reflection/matching-equation connector. -/
noncomputable def toRemainingLabeledReflectionMatchingEquationConnector
    (connector : RemainingReflectionIndexMatchingEquationConnector h) :
    RemainingLabeledReflectionMatchingEquationConnector h :=
  ⟨BranchOrbitABCReflectionLabeling.hasLabeledReflectionPair_of_reflectionCenterNeighborOrbitIndex_ne
      (h := h) connector.base connector.base_adj
      connector.base_pairwise_disjoint connector.base_cover connector.hmove,
    connector.referenceMatchingEquationCardTwo⟩

end RemainingReflectionIndexMatchingEquationConnector

/-- Once representation components are supplied, the reflected-index
matching-equation connector is already refuted by the existing
reflection-labeled compact-split no-go theorem. -/
theorem no_remainingReflectionIndexMatchingEquationConnector_of_components
    (h : D19ActsOnMoore57 V Γ) :
    ¬ ∃ _representationComponents : RemainingRepresentationComponents h,
        Nonempty (RemainingReflectionIndexMatchingEquationConnector h) := by
  rintro ⟨representationComponents, ⟨connector⟩⟩
  exact no_remainingLabeledReflectionMatchingEquationConnector_of_components h
    ⟨representationComponents,
      connector.toRemainingLabeledReflectionMatchingEquationConnector⟩

/-! ## Chosen center-neighbor decomposition plus fixed-neighbor bound -/

/-- The center-neighbor orbit decomposition canonically chosen from the raw
action for this diagnostic frontier. -/
noncomputable def remainingCenterNeighborBase
    (h : D19ActsOnMoore57 V Γ) : Fin 3 → V :=
  Classical.choose h.exists_three_rotationOrbitFinset_neighbors_rotationFixedCenter

theorem remainingCenterNeighborBase_adj
    (h : D19ActsOnMoore57 V Γ) :
    ∀ q : Fin 3,
      Γ.Adj h.rotationFixedCenter (remainingCenterNeighborBase h q) :=
  (Classical.choose_spec
    h.exists_three_rotationOrbitFinset_neighbors_rotationFixedCenter).1

theorem remainingCenterNeighborBase_pairwise_disjoint
    (h : D19ActsOnMoore57 V Γ) :
    ∀ q r : Fin 3, q ≠ r →
      Disjoint (h.rotationOrbitFinset (remainingCenterNeighborBase h q))
        (h.rotationOrbitFinset (remainingCenterNeighborBase h r)) :=
  (Classical.choose_spec
    h.exists_three_rotationOrbitFinset_neighbors_rotationFixedCenter).2.2.1

theorem remainingCenterNeighborBase_cover
    (h : D19ActsOnMoore57 V Γ) :
    Γ.neighborFinset h.rotationFixedCenter =
      h.orbitFamilyUnion (remainingCenterNeighborBase h) :=
  (Classical.choose_spec
    h.exists_three_rotationOrbitFinset_neighbors_rotationFixedCenter).2.2.2

/-- Existing fixed-neighbor bound constructor, specialized to the chosen
center-neighbor decomposition. -/
noncomputable def hasLabeledReflectionPair_of_fixedNeighborBound_defaultBase
    {h : D19ActsOnMoore57 V Γ}
    (fixedNeighbor_le_one :
      ∀ k : ZMod 19,
        ((Γ.neighborFinset h.rotationFixedCenter).filter fun y =>
          h.smul (DihedralGroup.sr k) y = y).card ≤ 1)
    (k : ZMod 19) :
    BranchOrbitABCReflectionLabeling.HasLabeledReflectionPair h := by
  classical
  let base := remainingCenterNeighborBase h
  have base_adj :
      ∀ q : Fin 3, Γ.Adj h.rotationFixedCenter (base q) := by
    simpa [base] using remainingCenterNeighborBase_adj (h := h)
  have base_pairwise_disjoint :
      ∀ q r : Fin 3, q ≠ r →
        Disjoint (h.rotationOrbitFinset (base q))
          (h.rotationOrbitFinset (base r)) := by
    simpa [base] using
      remainingCenterNeighborBase_pairwise_disjoint (h := h)
  have base_cover :
      Γ.neighborFinset h.rotationFixedCenter =
        h.orbitFamilyUnion base := by
    simpa [base] using remainingCenterNeighborBase_cover (h := h)
  let hb :=
    BranchOrbitABCReflectionLabeling.exists_reflectionCenterNeighborOrbitIndex_ne_of_fixed_neighbors_card_le_one
      (h := h) base base_adj base_pairwise_disjoint base_cover k
      (fixedNeighbor_le_one k)
  exact
    BranchOrbitABCReflectionLabeling.hasLabeledReflectionPair_of_reflectionCenterNeighborOrbitIndex_ne
      (h := h) base base_adj base_pairwise_disjoint base_cover
      (Classical.choose_spec hb)

/-- Connector form after the branch/reflection modules have converted a
fixed-neighbor bound into a labeled reflection pair.  The matching equation
for the induced labeling is still explicit. -/
structure RemainingFixedNeighborBoundMatchingEquationConnector
    (h : D19ActsOnMoore57 V Γ) where
  fixedNeighbor_le_one :
    ∀ k : ZMod 19,
      ((Γ.neighborFinset h.rotationFixedCenter).filter fun y =>
        h.smul (DihedralGroup.sr k) y = y).card ≤ 1
  k : ZMod 19
  referenceMatchingEquationCardTwo :
    BranchOrbitABCReflectionLabeling.ReferenceFiberMatchingEquationCardTwoOfPair
      (h := h)
      (hasLabeledReflectionPair_of_fixedNeighborBound_defaultBase
        (h := h) fixedNeighbor_le_one k)

namespace RemainingFixedNeighborBoundMatchingEquationConnector

variable {h : D19ActsOnMoore57 V Γ}

/-- Forget the fixed-neighbor-bound provenance back to the raw labeled
reflection/matching-equation connector. -/
noncomputable def toRemainingLabeledReflectionMatchingEquationConnector
    (connector : RemainingFixedNeighborBoundMatchingEquationConnector h) :
    RemainingLabeledReflectionMatchingEquationConnector h :=
  ⟨hasLabeledReflectionPair_of_fixedNeighborBound_defaultBase
      (h := h) connector.fixedNeighbor_le_one connector.k,
    connector.referenceMatchingEquationCardTwo⟩

end RemainingFixedNeighborBoundMatchingEquationConnector

/-- With representation components supplied, the fixed-neighbor-bound
matching-equation connector is impossible. -/
theorem no_remainingFixedNeighborBoundMatchingEquationConnector_of_components
    (h : D19ActsOnMoore57 V Γ) :
    ¬ ∃ _representationComponents : RemainingRepresentationComponents h,
        Nonempty (RemainingFixedNeighborBoundMatchingEquationConnector h) := by
  rintro ⟨representationComponents, ⟨connector⟩⟩
  exact no_remainingLabeledReflectionMatchingEquationConnector_of_components h
    ⟨representationComponents,
      connector.toRemainingLabeledReflectionMatchingEquationConnector⟩

/-! ## Fixed-center leaf boundary -/

/-- Existing fixed-center-leaf constructor, specialized to the chosen
center-neighbor decomposition. -/
noncomputable def hasLabeledReflectionPair_of_fixedCenterLeaf_defaultBase
    {h : D19ActsOnMoore57 V Γ}
    (fixedCenterLeaf : ReflectionFixedCenterLeafBoundary h)
    (k : ZMod 19) :
    BranchOrbitABCReflectionLabeling.HasLabeledReflectionPair h :=
  hasLabeledReflectionPair_of_fixedNeighborBound_defaultBase
    (h := h) fixedCenterLeaf.fixed_center_neighbors_card_le_one k

/-- Connector form after a fixed-center-leaf boundary has supplied the
fixed-neighbor bound and hence the labeled reflection pair.  The only remaining
geometric field is the reference-fiber matching equation for that induced
labeling. -/
structure RemainingFixedCenterLeafMatchingEquationConnector
    (h : D19ActsOnMoore57 V Γ) where
  fixedCenterLeaf : ReflectionFixedCenterLeafBoundary h
  k : ZMod 19
  referenceMatchingEquationCardTwo :
    BranchOrbitABCReflectionLabeling.ReferenceFiberMatchingEquationCardTwoOfPair
      (h := h)
      (hasLabeledReflectionPair_of_fixedCenterLeaf_defaultBase
        (h := h) fixedCenterLeaf k)

namespace RemainingFixedCenterLeafMatchingEquationConnector

variable {h : D19ActsOnMoore57 V Γ}

/-- Forget the fixed-center-leaf provenance back to the raw labeled
reflection/matching-equation connector. -/
noncomputable def toRemainingLabeledReflectionMatchingEquationConnector
    (connector : RemainingFixedCenterLeafMatchingEquationConnector h) :
    RemainingLabeledReflectionMatchingEquationConnector h :=
  ⟨hasLabeledReflectionPair_of_fixedCenterLeaf_defaultBase
      (h := h) connector.fixedCenterLeaf connector.k,
    connector.referenceMatchingEquationCardTwo⟩

end RemainingFixedCenterLeafMatchingEquationConnector

/-- With representation components supplied, the fixed-center-leaf
matching-equation connector is impossible. -/
theorem no_remainingFixedCenterLeafMatchingEquationConnector_of_components
    (h : D19ActsOnMoore57 V Γ) :
    ¬ ∃ _representationComponents : RemainingRepresentationComponents h,
        Nonempty (RemainingFixedCenterLeafMatchingEquationConnector h) := by
  rintro ⟨representationComponents, ⟨connector⟩⟩
  exact no_remainingLabeledReflectionMatchingEquationConnector_of_components h
    ⟨representationComponents,
      connector.toRemainingLabeledReflectionMatchingEquationConnector⟩

end

end Moore57
