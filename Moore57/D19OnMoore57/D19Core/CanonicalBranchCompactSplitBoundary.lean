import Moore57.D19OnMoore57.D19Core.CanonicalBranchAllFibersBoundary
import Moore57.D19OnMoore57.BranchOrbit.ABCResidualContribution
import Moore57.D19OnMoore57.BranchOrbit.ABCReflectionChoice
import Moore57.D19OnMoore57.Final.RepresentationUpperBound

/-!
# Canonical branch compact-split final boundary

This is the canonical branch/all-fiber boundary in the shape that matches the
natural-language Section 7 residual split.  The residual is not forced into the
old no-fixed form; it is passed to the final criterion as the compact split
`centerNeighborPart ∪ A_fibers`.
-/

namespace Moore57

open Finset

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

namespace D19ActsOnMoore57

/-- The canonical fixed-center A/B/C data before promotion to downstream
`BranchOrbitABCData`. -/
noncomputable def canonicalBranchABCFromCenter
    (h : D19ActsOnMoore57 V Γ) :
    BranchOrbitABCFromCenter h :=
  BranchOrbitABCFromCenter.ofExistsThreeRotationOrbitFinsetNeighbors h

@[simp] theorem canonicalBranchABCFromCenter_toBranchOrbitABCData
    (h : D19ActsOnMoore57 V Γ) :
    h.canonicalBranchABCFromCenter.toBranchOrbitABCData =
      h.canonicalBranchABCData :=
  rfl

end D19ActsOnMoore57

local instance instD19CanonicalBranchCompactSplitBoundaryPFintype
    (h : D19ActsOnMoore57 V Γ) :
    Fintype h.canonicalBranchABCFromCenter.toAFiberCoordinates.P :=
  h.canonicalBranchABCFromCenter.toAFiberCoordinates.P_fintype

local instance instD19CanonicalBranchCompactSplitBoundaryBranchDataPFintype
    (h : D19ActsOnMoore57 V Γ) :
    Fintype
      h.canonicalBranchABCFromCenter.toBranchOrbitABCData.toAFiberCoordinates.P :=
  h.canonicalBranchABCFromCenter.toBranchOrbitABCData.toAFiberCoordinates.P_fintype

local instance instD19CanonicalBranchCompactSplitBoundaryDecidableEq
    (α : Type*) : DecidableEq α :=
  Classical.decEq α

/-- Canonical branch/all-fiber boundary matching the Section 7 compact
residual split. -/
structure D19CanonicalBranchCompactSplitBoundaryInputs
    (h : D19ActsOnMoore57 V Γ) where
  /-- Representation-character data, exposed through the existing component
  boundary. -/
  representationComponents :
    D19ActsOnMoore57.RepresentationCharacterComponentsBoundary h
  /-- Reflected-copy parameter. -/
  k : ZMod 19
  /-- The chosen reflection sends the B-side branch representative to the
  C-side branch representative. -/
  reflection_b0_eq_c0 :
    h.smul (DihedralGroup.sr k) h.canonicalBranchABCFromCenter.b0 =
      h.canonicalBranchABCFromCenter.c0
  /-- The all-A-fiber side has adjacent-moved contribution `38`. -/
  aFiberCardinality :
    AFiberCardinality38Boundary h
      h.canonicalBranchABCFromCenter.toAFiberCoordinates
      (Finset.univ : Finset (ZMod 19))

namespace D19CanonicalBranchCompactSplitBoundaryInputs

variable {h : D19ActsOnMoore57 V Γ}

/-- Constructor from the matching-equation two-solution statement used in the
natural-language proof. -/
noncomputable def ofMatchingEquationCardTwo
    (representationComponents :
      D19ActsOnMoore57.RepresentationCharacterComponentsBoundary h)
    (k : ZMod 19)
    (reflection_b0_eq_c0 :
      h.smul (DihedralGroup.sr k) h.canonicalBranchABCFromCenter.b0 =
        h.canonicalBranchABCFromCenter.c0)
    (matchingEquationCardTwo :
      ∀ d : ZMod 19, ∀ hd : d ≠ 0, ∀ i : ZMod 19,
        ((Finset.univ :
            Finset
              h.canonicalBranchABCFromCenter.toBranchOrbitABCData.toAFiberCoordinates.P).filter fun p =>
          AFiberCoordinates.matchingEquiv h.isMoore
              h.canonicalBranchABCFromCenter.toBranchOrbitABCData.toAFiberCoordinates
              i (i + d) (index_ne_add_of_ne_zero hd) p =
            (h.canonicalBranchABCFromCenter.toBranchOrbitABCData.toAFiberRotationEquivariance).coordPerm
              d i p).card =
          2) :
    D19CanonicalBranchCompactSplitBoundaryInputs h where
  representationComponents := representationComponents
  k := k
  reflection_b0_eq_c0 := reflection_b0_eq_c0
  aFiberCardinality := by
    let centerData := h.canonicalBranchABCFromCenter
    have hboundary :
        AFiberCardinality38Boundary h
          centerData.toBranchOrbitABCData.toAFiberCoordinates
          (Finset.univ : Finset (ZMod 19)) :=
      centerData.toBranchOrbitABCData
        |>.toAllFibersCardinalityFromMatchingEquationTwo matchingEquationCardTwo
    simpa [centerData] using hboundary

/-- Constructor using the weaker orbit-level reflection statement.  The
reflection parameter is adjusted internally so that the reflected B
representative is exactly `c0`. -/
noncomputable def ofReflectionOrbit
    (representationComponents :
      D19ActsOnMoore57.RepresentationCharacterComponentsBoundary h)
    (k : ZMod 19)
    (reflection_b0_mem_c0_orbit :
      h.smul (DihedralGroup.sr k) h.canonicalBranchABCFromCenter.b0 ∈
        h.rotationOrbitFinset h.canonicalBranchABCFromCenter.c0)
    (aFiberCardinality :
      AFiberCardinality38Boundary h
        h.canonicalBranchABCFromCenter.toAFiberCoordinates
        (Finset.univ : Finset (ZMod 19))) :
    D19CanonicalBranchCompactSplitBoundaryInputs h := by
  let centerData := h.canonicalBranchABCFromCenter
  let hexists :=
    centerData
      |>.exists_reflection_smul_b0_eq_c0_of_reflection_smul_b0_mem_c0_orbit
        reflection_b0_mem_c0_orbit
  let k' : ZMod 19 := Classical.choose hexists
  have hk' : h.smul (DihedralGroup.sr k') centerData.b0 = centerData.c0 :=
    Classical.choose_spec hexists
  exact
    { representationComponents := representationComponents
      k := k'
      reflection_b0_eq_c0 := hk'
      aFiberCardinality := aFiberCardinality }

/-- Convert the canonical branch compact-split boundary to the already refuted
final compact-split representation boundary. -/
noncomputable def toD19FinalRepresentationUpperBoundCompactSplitInputs
    (data : D19CanonicalBranchCompactSplitBoundaryInputs h) :
    D19FinalRepresentationUpperBoundCompactSplitInputs h :=
  let centerData := h.canonicalBranchABCFromCenter
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
        data.aFiberCardinality data.reflection_b0_eq_c0 }

/-- The canonical branch compact-split boundary cannot exist. -/
theorem not_nonempty (h : D19ActsOnMoore57 V Γ) :
    ¬ Nonempty (D19CanonicalBranchCompactSplitBoundaryInputs h) := by
  rintro ⟨data⟩
  exact D19FinalRepresentationUpperBoundCompactSplitInputs.not_nonempty h
    ⟨data.toD19FinalRepresentationUpperBoundCompactSplitInputs⟩

end D19CanonicalBranchCompactSplitBoundaryInputs

/-- Public alias for the canonical branch compact-split top-level boundary. -/
theorem no_D19_canonical_branch_compact_split_boundary
    (h : D19ActsOnMoore57 V Γ) :
    ¬ Nonempty (D19CanonicalBranchCompactSplitBoundaryInputs h) :=
  D19CanonicalBranchCompactSplitBoundaryInputs.not_nonempty h

end

end Moore57
