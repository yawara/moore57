import Moore57.BranchOrbitABCReflectionLabeling
import Moore57.BranchOrbitABCResidualContribution
import Moore57.BranchOrbitABCAllFibersFinalBridge
import Moore57.D19RepresentationCharacterDataBridge
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

end

end Moore57
