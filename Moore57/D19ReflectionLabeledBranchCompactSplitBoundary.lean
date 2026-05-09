import Moore57.BranchOrbitABCReflectionLabeling
import Moore57.BranchOrbitABCResidualContribution
import Moore57.BranchOrbitABCAllFibersFinalBridge
import Moore57.AFiberContributionRotationInvariance
import Moore57.D19RepresentationMathlibCharacterTools
import Moore57.D19FinalRepresentationUpperBoundCompactSplit

/-!
# Reflection-labeled branch compact-split final boundary

This boundary is the compact Section 7 split in the shape where the A/B/C
branch labels have already been chosen compatibly with a reflection.  Unlike
the canonical arbitrary A/B/C labeling, this is the natural entry point for the
proof step that relabels the three center-neighbor orbits before selecting the
B-side fiber bases.
-/

namespace Moore57

open Finset

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

local instance instD19ReflectionLabeledBranchCompactSplitBoundaryPFintype
    {h : D19ActsOnMoore57 V Γ}
    (labeling : BranchOrbitABCReflectionLabeling h) :
    Fintype labeling.data.toAFiberCoordinates.P :=
  labeling.data.toAFiberCoordinates.P_fintype

local instance instD19ReflectionLabeledBranchCompactSplitBoundaryBranchDataPFintype
    {h : D19ActsOnMoore57 V Γ}
    (labeling : BranchOrbitABCReflectionLabeling h) :
    Fintype labeling.data.toBranchOrbitABCData.toAFiberCoordinates.P :=
  labeling.data.toBranchOrbitABCData.toAFiberCoordinates.P_fintype

local instance instD19ReflectionLabeledBranchCompactSplitBoundaryDecidableEq
    (α : Type*) : DecidableEq α :=
  Classical.decEq α

/-- Branch compact-split boundary using an explicitly reflection-compatible
A/B/C labeling. -/
structure D19ReflectionLabeledBranchCompactSplitBoundaryInputs
    (h : D19ActsOnMoore57 V Γ) where
  /-- Representation-character data, exposed through the existing component
  boundary. -/
  representationComponents :
    D19ActsOnMoore57.RepresentationCharacterComponentsBoundary h
  /-- Fixed-center A/B/C labels selected so that one reflection sends `b0`
  exactly to `c0`. -/
  labeling : BranchOrbitABCReflectionLabeling h
  /-- The all-A-fiber side has adjacent-moved contribution `38`. -/
  aFiberCardinality :
    AFiberCardinality38Boundary h labeling.data.toAFiberCoordinates
      (Finset.univ : Finset (ZMod 19))

namespace D19ReflectionLabeledBranchCompactSplitBoundaryInputs

variable {h : D19ActsOnMoore57 V Γ}

/-- Constructor from the matching-equation two-solution statement for the
reflection-compatible labeling. -/
noncomputable def ofMatchingEquationCardTwo
    (representationComponents :
      D19ActsOnMoore57.RepresentationCharacterComponentsBoundary h)
    (labeling : BranchOrbitABCReflectionLabeling h)
    (matchingEquationCardTwo :
      ∀ d : ZMod 19, ∀ hd : d ≠ 0, ∀ i : ZMod 19,
        ((Finset.univ :
            Finset
              labeling.data.toBranchOrbitABCData.toAFiberCoordinates.P).filter fun p =>
          AFiberCoordinates.matchingEquiv h.isMoore
              labeling.data.toBranchOrbitABCData.toAFiberCoordinates
              i (i + d) (index_ne_add_of_ne_zero hd) p =
            (labeling.data.toBranchOrbitABCData.toAFiberRotationEquivariance).coordPerm
              d i p).card =
          2) :
    D19ReflectionLabeledBranchCompactSplitBoundaryInputs h where
  representationComponents := representationComponents
  labeling := labeling
  aFiberCardinality := by
    have hboundary :
        AFiberCardinality38Boundary h
          labeling.data.toBranchOrbitABCData.toAFiberCoordinates
          (Finset.univ : Finset (ZMod 19)) :=
      labeling.data.toBranchOrbitABCData
        |>.toAllFibersCardinalityFromMatchingEquationTwo
          matchingEquationCardTwo
    simpa using hboundary

/-- Constructor from checking the matching-rotation fixed count only on the
reference A-fiber `0`.  Rotation equivariance promotes this to all fibers. -/
noncomputable def ofReferenceFiberMatchingSupportTwo
    (representationComponents :
      D19ActsOnMoore57.RepresentationCharacterComponentsBoundary h)
    (labeling : BranchOrbitABCReflectionLabeling h)
    (referenceSupportCardTwo :
      ∀ d : ZMod 19, ∀ hd : d ≠ 0,
        ((labeling.data.toBranchOrbitABCData.toAFiberRotationEquivariance)
          |>.matchingRotationPerm d 0 hd).supportᶜ.card =
          2) :
    D19ReflectionLabeledBranchCompactSplitBoundaryInputs h where
  representationComponents := representationComponents
  labeling := labeling
  aFiberCardinality := by
    have hboundary :
      AFiberCardinality38Boundary h
          labeling.data.toBranchOrbitABCData.toAFiberCoordinates
          (Finset.univ : Finset (ZMod 19)) :=
      AFiberCardinality38Boundary.of_allFibers_matchingRotationPerm_zero_support_compl_card_eq_two
        labeling.data.toBranchOrbitABCData.toAFiberRotationEquivariance
        referenceSupportCardTwo
    simpa using hboundary

/-- Constructor from the explicit matching equation on the reference A-fiber
`0`.  This is the coordinate-equation spelling of
`ofReferenceFiberMatchingSupportTwo`. -/
noncomputable def ofReferenceFiberMatchingEquationTwo
    (representationComponents :
      D19ActsOnMoore57.RepresentationCharacterComponentsBoundary h)
    (labeling : BranchOrbitABCReflectionLabeling h)
    (referenceMatchingEquationCardTwo :
      ∀ d : ZMod 19, ∀ hd : d ≠ 0,
        ((Finset.univ :
            Finset
              labeling.data.toBranchOrbitABCData.toAFiberCoordinates.P).filter fun p =>
          AFiberCoordinates.matchingEquiv h.isMoore
              labeling.data.toBranchOrbitABCData.toAFiberCoordinates
              0 (0 + d) (index_ne_add_of_ne_zero hd) p =
            (labeling.data.toBranchOrbitABCData.toAFiberRotationEquivariance).coordPerm
              d 0 p).card =
          2) :
    D19ReflectionLabeledBranchCompactSplitBoundaryInputs h :=
  ofReferenceFiberMatchingSupportTwo representationComponents labeling (by
    intro d hd
    rw [AFiberRotationEquivariance.matchingRotationPerm_support_compl_card_eq_filter_card
      labeling.data.toBranchOrbitABCData.toAFiberRotationEquivariance d 0 hd]
    exact referenceMatchingEquationCardTwo d hd)

/-- Convert the reflection-labeled compact-split boundary to the already
refuted final compact-split representation boundary. -/
noncomputable def toD19FinalRepresentationUpperBoundCompactSplitInputs
    (data : D19ReflectionLabeledBranchCompactSplitBoundaryInputs h) :
    D19FinalRepresentationUpperBoundCompactSplitInputs h :=
  let centerData := data.labeling.data
  let representation :
      D19ActsOnMoore57.D19RepresentationCharacterInput h :=
    Classical.choice
      ((D19ActsOnMoore57.D19RepresentationCharacterInput.nonempty_iff_componentsBoundary
        h).mpr
          data.representationComponents)
  { representation := representation
    fixedUpperBound :=
      D19ActsOnMoore57.RotationFixedUpperBoundInput.of_rotation_one_le_nineteen
        (by
          rw [h.rotation_one_fixedVertexCount_eq_one]
          norm_num)
    orbitBase := centerData.toOrbitBaseSelectionInputFromBFibers
    adjacentMoved :=
      centerData.toComplementResidualSplit38WitnessFromBFibersOfReflection
        data.aFiberCardinality data.labeling.reflection_b0_eq_c0 }

/-- The reflection-labeled branch compact-split boundary cannot exist. -/
theorem not_nonempty (h : D19ActsOnMoore57 V Γ) :
    ¬ Nonempty (D19ReflectionLabeledBranchCompactSplitBoundaryInputs h) := by
  rintro ⟨data⟩
  exact D19FinalRepresentationUpperBoundCompactSplitInputs.not_nonempty h
    ⟨data.toD19FinalRepresentationUpperBoundCompactSplitInputs⟩

end D19ReflectionLabeledBranchCompactSplitBoundaryInputs

/-- Public alias for the reflection-labeled branch compact-split boundary. -/
theorem no_D19_reflection_labeled_branch_compact_split_boundary
    (h : D19ActsOnMoore57 V Γ) :
    ¬ Nonempty (D19ReflectionLabeledBranchCompactSplitBoundaryInputs h) :=
  D19ReflectionLabeledBranchCompactSplitBoundaryInputs.not_nonempty h

/-- Public no-go statement exposing the current reflection-labeled path as
three raw remaining inputs: representation components, a minimal labeled
reflection pair, and the reference-fiber matching equation with two solutions. -/
theorem no_D19_hasLabeledReflectionPair_referenceFiberMatchingEquation_boundary
    (h : D19ActsOnMoore57 V Γ) :
    ¬ ∃ _representationComponents :
          D19ActsOnMoore57.RepresentationCharacterComponentsBoundary h,
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
              2 := by
  rintro ⟨representationComponents, hp, referenceMatchingEquationCardTwo⟩
  let labeling :=
    BranchOrbitABCReflectionLabeling.ofHasLabeledReflectionPair (h := h) hp
  have hreference :
      ∀ d : ZMod 19, ∀ hd : d ≠ 0,
        ((Finset.univ :
            Finset
              labeling.data.toBranchOrbitABCData.toAFiberCoordinates.P).filter fun p =>
          AFiberCoordinates.matchingEquiv h.isMoore
              labeling.data.toBranchOrbitABCData.toAFiberCoordinates
              0 (0 + d) (index_ne_add_of_ne_zero hd) p =
            (labeling.data.toBranchOrbitABCData.toAFiberRotationEquivariance).coordPerm
              d 0 p).card =
          2 := by
    simpa [labeling] using referenceMatchingEquationCardTwo
  exact no_D19_reflection_labeled_branch_compact_split_boundary h
    ⟨D19ReflectionLabeledBranchCompactSplitBoundaryInputs.ofReferenceFiberMatchingEquationTwo
      representationComponents labeling hreference⟩

/-- Same no-go statement as
`no_D19_hasLabeledReflectionPair_referenceFiberMatchingEquation_boundary`, but
with the representation component boundary supplied from a mathlib
representation character.  The dimension equation is supplied internally by
`Representation.char_one`. -/
theorem no_D19_mathlibCharacter_hasLabeledReflectionPair_referenceFiberMatchingEquation_boundary
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
    ¬ ∃ hp : BranchOrbitABCReflectionLabeling.HasLabeledReflectionPair h,
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
            2 := by
  intro hgeometry
  exact no_D19_hasLabeledReflectionPair_referenceFiberMatchingEquation_boundary h
    ⟨D19ActsOnMoore57.representationCharacterComponentsBoundary_of_representationCharacterComponents
      h ρ alpha beta gamma finrank_eq trace_eq_character
      character_eq_d19Linear reflection minus8_trivial_nonneg
      minus8_sign_nonneg,
      hgeometry⟩

/-- Mathlib-character no-go statement with the reflection input exposed as
nontrivial action on the three center-neighbor rotation orbits. -/
theorem no_D19_mathlibCharacter_reflectionIndex_referenceFiberMatchingEquation_boundary
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
    (minus8_sign_nonneg : beta ≤ 58)
    (base : Fin 3 → V)
    (base_adj : ∀ q : Fin 3, Γ.Adj h.rotationFixedCenter (base q))
    (base_pairwise_disjoint :
      ∀ q r : Fin 3, q ≠ r →
        Disjoint (h.rotationOrbitFinset (base q))
          (h.rotationOrbitFinset (base r)))
    (base_cover :
      Γ.neighborFinset h.rotationFixedCenter = h.orbitFamilyUnion base) :
    ¬ ∃ k : ZMod 19, ∃ b : Fin 3,
        ∃ hmove :
          BranchOrbitABCReflectionLabeling.reflectionCenterNeighborOrbitIndex
            (h := h) base base_adj base_cover k b ≠ b,
          let hp :=
            BranchOrbitABCReflectionLabeling.hasLabeledReflectionPair_of_reflectionCenterNeighborOrbitIndex_ne
              (h := h) base base_adj base_pairwise_disjoint base_cover
              hmove
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
              2 := by
  rintro ⟨k, b, hmove, hreference⟩
  let hp :=
    BranchOrbitABCReflectionLabeling.hasLabeledReflectionPair_of_reflectionCenterNeighborOrbitIndex_ne
      (h := h) base base_adj base_pairwise_disjoint base_cover hmove
  let labeling :=
    BranchOrbitABCReflectionLabeling.ofHasLabeledReflectionPair (h := h) hp
  exact no_D19_mathlibCharacter_hasLabeledReflectionPair_referenceFiberMatchingEquation_boundary
    h ρ alpha beta gamma finrank_eq trace_eq_character
      character_eq_d19Linear reflection minus8_trivial_nonneg
      minus8_sign_nonneg
    ⟨hp, by
      simpa [hp, labeling] using hreference⟩

/-- Version of
`no_D19_mathlibCharacter_reflectionIndex_referenceFiberMatchingEquation_boundary`
whose character input is only the values on identity, nontrivial rotations,
and reflections. -/
theorem no_D19_mathlibCharacterValues_reflectionIndex_referenceFiberMatchingEquation_boundary
    (h : D19ActsOnMoore57 V Γ)
    {W : Type*} [AddCommGroup W] [Module ℚ W] [FiniteDimensional ℚ W]
    (ρ : Representation ℚ (DihedralGroup 19) W)
    (alpha beta gamma : ℕ)
    (finrank_eq : Module.finrank ℚ W = 1729)
    (trace_eq_character :
      ∀ g : DihedralGroup 19,
        Matrix.trace (E7Matrix Γ * permMatrix (h.smulEquiv g)) =
          ρ.character g)
    (one_value :
      ρ.character (1 : DihedralGroup 19) =
        (alpha : ℚ) + (beta : ℚ) + 18 * (gamma : ℚ))
    (rotation_value :
      ∀ d : ZMod 19, d ≠ 0 →
        ρ.character (DihedralGroup.r d) =
          (alpha : ℚ) + (beta : ℚ) - (gamma : ℚ))
    (reflection_value :
      ∀ k : ZMod 19,
        ρ.character (DihedralGroup.sr k) = (alpha : ℚ) - (beta : ℚ))
    (reflection : (alpha : ℤ) - (beta : ℤ) = 33)
    (minus8_trivial_nonneg : alpha ≤ 113)
    (minus8_sign_nonneg : beta ≤ 58)
    (base : Fin 3 → V)
    (base_adj : ∀ q : Fin 3, Γ.Adj h.rotationFixedCenter (base q))
    (base_pairwise_disjoint :
      ∀ q r : Fin 3, q ≠ r →
        Disjoint (h.rotationOrbitFinset (base q))
          (h.rotationOrbitFinset (base r)))
    (base_cover :
      Γ.neighborFinset h.rotationFixedCenter = h.orbitFamilyUnion base) :
    ¬ ∃ k : ZMod 19, ∃ b : Fin 3,
        ∃ hmove :
          BranchOrbitABCReflectionLabeling.reflectionCenterNeighborOrbitIndex
            (h := h) base base_adj base_cover k b ≠ b,
          let hp :=
            BranchOrbitABCReflectionLabeling.hasLabeledReflectionPair_of_reflectionCenterNeighborOrbitIndex_ne
              (h := h) base base_adj base_pairwise_disjoint base_cover
              hmove
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
              2 := by
  exact no_D19_mathlibCharacter_reflectionIndex_referenceFiberMatchingEquation_boundary
    h ρ alpha beta gamma finrank_eq trace_eq_character
    (character_eq_d19Linear_of_values ρ.character alpha beta gamma
      one_value rotation_value reflection_value)
    reflection minus8_trivial_nonneg minus8_sign_nonneg
    base base_adj base_pairwise_disjoint base_cover

/-- Version where the nontrivial reflection-index input is supplied by the
local fixed-neighbor bound around the rotation-fixed center. -/
theorem no_D19_mathlibCharacterValues_fixedNeighborBound_referenceFiberMatchingEquation_boundary
    (h : D19ActsOnMoore57 V Γ)
    {W : Type*} [AddCommGroup W] [Module ℚ W] [FiniteDimensional ℚ W]
    (ρ : Representation ℚ (DihedralGroup 19) W)
    (alpha beta gamma : ℕ)
    (finrank_eq : Module.finrank ℚ W = 1729)
    (trace_eq_character :
      ∀ g : DihedralGroup 19,
        Matrix.trace (E7Matrix Γ * permMatrix (h.smulEquiv g)) =
          ρ.character g)
    (one_value :
      ρ.character (1 : DihedralGroup 19) =
        (alpha : ℚ) + (beta : ℚ) + 18 * (gamma : ℚ))
    (rotation_value :
      ∀ d : ZMod 19, d ≠ 0 →
        ρ.character (DihedralGroup.r d) =
          (alpha : ℚ) + (beta : ℚ) - (gamma : ℚ))
    (reflection_value :
      ∀ k : ZMod 19,
        ρ.character (DihedralGroup.sr k) = (alpha : ℚ) - (beta : ℚ))
    (reflection : (alpha : ℤ) - (beta : ℤ) = 33)
    (minus8_trivial_nonneg : alpha ≤ 113)
    (minus8_sign_nonneg : beta ≤ 58)
    (base : Fin 3 → V)
    (base_adj : ∀ q : Fin 3, Γ.Adj h.rotationFixedCenter (base q))
    (base_pairwise_disjoint :
      ∀ q r : Fin 3, q ≠ r →
        Disjoint (h.rotationOrbitFinset (base q))
          (h.rotationOrbitFinset (base r)))
    (base_cover :
      Γ.neighborFinset h.rotationFixedCenter = h.orbitFamilyUnion base)
    (fixedNeighbor_le_one :
      ∀ k : ZMod 19,
        ((Γ.neighborFinset h.rotationFixedCenter).filter fun y =>
          h.smul (DihedralGroup.sr k) y = y).card ≤ 1) :
    ¬ ∃ k : ZMod 19,
        let hb :=
          BranchOrbitABCReflectionLabeling.exists_reflectionCenterNeighborOrbitIndex_ne_of_fixed_neighbors_card_le_one
            (h := h) base base_adj base_pairwise_disjoint base_cover k
            (fixedNeighbor_le_one k)
        let b : Fin 3 :=
          Classical.choose
            hb
        let hmove :
          BranchOrbitABCReflectionLabeling.reflectionCenterNeighborOrbitIndex
            (h := h) base base_adj base_cover k b ≠ b :=
          Classical.choose_spec hb
        let hp :=
          BranchOrbitABCReflectionLabeling.hasLabeledReflectionPair_of_reflectionCenterNeighborOrbitIndex_ne
            (h := h) base base_adj base_pairwise_disjoint base_cover hmove
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
            2 := by
  rintro ⟨k, hreference⟩
  let hb :=
    BranchOrbitABCReflectionLabeling.exists_reflectionCenterNeighborOrbitIndex_ne_of_fixed_neighbors_card_le_one
      (h := h) base base_adj base_pairwise_disjoint base_cover k
      (fixedNeighbor_le_one k)
  let b : Fin 3 := Classical.choose hb
  have hmove :
      BranchOrbitABCReflectionLabeling.reflectionCenterNeighborOrbitIndex
        (h := h) base base_adj base_cover k b ≠ b :=
    Classical.choose_spec hb
  exact no_D19_mathlibCharacterValues_reflectionIndex_referenceFiberMatchingEquation_boundary
    h ρ alpha beta gamma finrank_eq trace_eq_character one_value
    rotation_value reflection_value reflection minus8_trivial_nonneg
    minus8_sign_nonneg base base_adj base_pairwise_disjoint base_cover
    ⟨k, b, hmove, by
      simpa [hb, b, hmove] using hreference⟩

/-- Same fixed-neighbor-bound no-go, with the representation side bundled as
`D19CharacterValueBoundary`.  This leaves only one reflection representative
value in the representation-theoretic boundary. -/
theorem no_D19_characterValueBoundary_fixedNeighborBound_referenceFiberMatchingEquation_boundary
    (h : D19ActsOnMoore57 V Γ)
    {W : Type*} [AddCommGroup W] [Module ℚ W] [FiniteDimensional ℚ W]
    (ρ : Representation ℚ (DihedralGroup 19) W)
    (alpha beta gamma : ℕ)
    (finrank_eq : Module.finrank ℚ W = 1729)
    (trace_eq_character :
      ∀ g : DihedralGroup 19,
        Matrix.trace (E7Matrix Γ * permMatrix (h.smulEquiv g)) =
          ρ.character g)
    (characterValues : D19CharacterValueBoundary ρ alpha beta gamma)
    (reflection : (alpha : ℤ) - (beta : ℤ) = 33)
    (minus8_trivial_nonneg : alpha ≤ 113)
    (minus8_sign_nonneg : beta ≤ 58)
    (base : Fin 3 → V)
    (base_adj : ∀ q : Fin 3, Γ.Adj h.rotationFixedCenter (base q))
    (base_pairwise_disjoint :
      ∀ q r : Fin 3, q ≠ r →
        Disjoint (h.rotationOrbitFinset (base q))
          (h.rotationOrbitFinset (base r)))
    (base_cover :
      Γ.neighborFinset h.rotationFixedCenter = h.orbitFamilyUnion base)
    (fixedNeighbor_le_one :
      ∀ k : ZMod 19,
        ((Γ.neighborFinset h.rotationFixedCenter).filter fun y =>
          h.smul (DihedralGroup.sr k) y = y).card ≤ 1) :
    ¬ ∃ k : ZMod 19,
        let hb :=
          BranchOrbitABCReflectionLabeling.exists_reflectionCenterNeighborOrbitIndex_ne_of_fixed_neighbors_card_le_one
            (h := h) base base_adj base_pairwise_disjoint base_cover k
            (fixedNeighbor_le_one k)
        let b : Fin 3 :=
          Classical.choose
            hb
        let hmove :
          BranchOrbitABCReflectionLabeling.reflectionCenterNeighborOrbitIndex
            (h := h) base base_adj base_cover k b ≠ b :=
          Classical.choose_spec hb
        let hp :=
          BranchOrbitABCReflectionLabeling.hasLabeledReflectionPair_of_reflectionCenterNeighborOrbitIndex_ne
            (h := h) base base_adj base_pairwise_disjoint base_cover hmove
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
            2 := by
  exact no_D19_mathlibCharacterValues_fixedNeighborBound_referenceFiberMatchingEquation_boundary
    h ρ alpha beta gamma finrank_eq trace_eq_character
    characterValues.one_value characterValues.rotation_value
    characterValues.reflection_value reflection minus8_trivial_nonneg
    minus8_sign_nonneg base base_adj base_pairwise_disjoint base_cover
    fixedNeighbor_le_one

/-- Same fixed-neighbor-bound no-go, with the representation side in the
class-boundary form closest to the natural-language character argument. -/
theorem no_D19_characterClassBoundary_fixedNeighborBound_referenceFiberMatchingEquation_boundary
    (h : D19ActsOnMoore57 V Γ)
    {W : Type*} [AddCommGroup W] [Module ℚ W] [FiniteDimensional ℚ W]
    (ρ : Representation ℚ (DihedralGroup 19) W)
    (alpha beta gamma : ℕ)
    (finrank_eq : Module.finrank ℚ W = 1729)
    (trace_eq_character :
      ∀ g : DihedralGroup 19,
        Matrix.trace (E7Matrix Γ * permMatrix (h.smulEquiv g)) =
          ρ.character g)
    (characterClass : D19CharacterClassBoundary ρ alpha beta gamma)
    (reflection : (alpha : ℤ) - (beta : ℤ) = 33)
    (minus8_trivial_nonneg : alpha ≤ 113)
    (minus8_sign_nonneg : beta ≤ 58)
    (base : Fin 3 → V)
    (base_adj : ∀ q : Fin 3, Γ.Adj h.rotationFixedCenter (base q))
    (base_pairwise_disjoint :
      ∀ q r : Fin 3, q ≠ r →
        Disjoint (h.rotationOrbitFinset (base q))
          (h.rotationOrbitFinset (base r)))
    (base_cover :
      Γ.neighborFinset h.rotationFixedCenter = h.orbitFamilyUnion base)
    (fixedNeighbor_le_one :
      ∀ k : ZMod 19,
        ((Γ.neighborFinset h.rotationFixedCenter).filter fun y =>
          h.smul (DihedralGroup.sr k) y = y).card ≤ 1) :
    ¬ ∃ k : ZMod 19,
        let hb :=
          BranchOrbitABCReflectionLabeling.exists_reflectionCenterNeighborOrbitIndex_ne_of_fixed_neighbors_card_le_one
            (h := h) base base_adj base_pairwise_disjoint base_cover k
            (fixedNeighbor_le_one k)
        let b : Fin 3 :=
          Classical.choose
            hb
        let hmove :
          BranchOrbitABCReflectionLabeling.reflectionCenterNeighborOrbitIndex
            (h := h) base base_adj base_cover k b ≠ b :=
          Classical.choose_spec hb
        let hp :=
          BranchOrbitABCReflectionLabeling.hasLabeledReflectionPair_of_reflectionCenterNeighborOrbitIndex_ne
            (h := h) base base_adj base_pairwise_disjoint base_cover hmove
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
            2 := by
  exact no_D19_characterValueBoundary_fixedNeighborBound_referenceFiberMatchingEquation_boundary
    h ρ alpha beta gamma finrank_eq trace_eq_character
    (characterClass.toValueBoundary finrank_eq) reflection
    minus8_trivial_nonneg minus8_sign_nonneg base base_adj
    base_pairwise_disjoint base_cover fixedNeighbor_le_one

end

end Moore57
