import Moore57.BranchOrbitABCReferenceSolutionFixedBoundary

/-!
# Geometry connectors for reference matching solution fixedness

This file adds thin boundary connectors for the geometric statement that
reference matching-equation solutions lie in the fixed part of the A-fixing
reflection.  The target boundary is
`ReferenceRotationMatchingSolutionVertexFixedBoundary`; the hypotheses here are
more Finset-oriented, or are stated on the underlying reference-fiber vertices.
-/

namespace Moore57

open Finset

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

local instance instReferenceSolutionGeometryBoundaryPFintype
    {h : D19ActsOnMoore57 V Γ}
    (labeling : BranchOrbitABCReflectionLabeling h) :
    Fintype labeling.data.toAFiberCoordinates.P :=
  labeling.data.toAFiberCoordinates.P_fintype

local instance instReferenceSolutionGeometryBoundaryDecidableEq
    (α : Type*) : DecidableEq α :=
  Classical.decEq α

namespace BranchOrbitABCReflectionLabeling

variable {h : D19ActsOnMoore57 V Γ}

/-- The reference matching-equation solution set for the offset `d`. -/
noncomputable def referenceMatchingSolutionSet
    (labeling : BranchOrbitABCReflectionLabeling h)
    (d : ZMod 19) (hd : d ≠ 0) :
    Finset labeling.data.toAFiberCoordinates.P :=
  (Finset.univ : Finset labeling.data.toAFiberCoordinates.P).filter fun p =>
    AFiberCoordinates.matchingEquiv h.isMoore
        labeling.data.toAFiberCoordinates 0 (0 + d)
        (index_ne_add_of_ne_zero hd) p =
      labeling.data.toAFiberRotationEquivariance.coordPerm d 0 p

@[simp] theorem mem_referenceMatchingSolutionSet
    (labeling : BranchOrbitABCReflectionLabeling h)
    (d : ZMod 19) (hd : d ≠ 0)
    (p : labeling.data.toAFiberCoordinates.P) :
    p ∈ labeling.referenceMatchingSolutionSet d hd ↔
      AFiberCoordinates.matchingEquiv h.isMoore
          labeling.data.toAFiberCoordinates 0 (0 + d)
          (index_ne_add_of_ne_zero hd) p =
        labeling.data.toAFiberRotationEquivariance.coordPerm d 0 p := by
  simp [referenceMatchingSolutionSet]

/-- The underlying reference-fiber vertex represented by a coordinate. -/
def referenceFiberVertex
    (labeling : BranchOrbitABCReflectionLabeling h)
    (p : labeling.data.toAFiberCoordinates.P) : V :=
  ((labeling.data.toAFiberCoordinates.coord 0 p :
    {x : V // x ∈
      branchFiber Γ labeling.data.toAFiberCoordinates.u
        (labeling.data.toAFiberCoordinates.a 0)}) : V)

/-- The underlying reference-fiber vertices represented by solutions of the
reference matching equation. -/
noncomputable def referenceMatchingSolutionVertexSet
    (labeling : BranchOrbitABCReflectionLabeling h)
    (d : ZMod 19) (hd : d ≠ 0) : Finset V :=
  (labeling.referenceMatchingSolutionSet d hd).image
    (labeling.referenceFiberVertex)

@[simp] theorem mem_referenceMatchingSolutionVertexSet
    (labeling : BranchOrbitABCReflectionLabeling h)
    (d : ZMod 19) (hd : d ≠ 0) (x : V) :
    x ∈ labeling.referenceMatchingSolutionVertexSet d hd ↔
      ∃ p : labeling.data.toAFiberCoordinates.P,
        p ∈ labeling.referenceMatchingSolutionSet d hd ∧
          labeling.referenceFiberVertex p = x := by
  simp [referenceMatchingSolutionVertexSet]

/-- The fixed vertices in the underlying reference A-fiber for the A-fixing
reflection. -/
noncomputable def aFiberReflectionFixedReferenceVertexSet
    (labeling : BranchOrbitABCReflectionLabeling h) : Finset V :=
  (labeling.data.toAFiberCoordinates.fiber 0).filter fun x =>
    h.smul (DihedralGroup.sr labeling.aFixingReflectionIndex) x = x

@[simp] theorem mem_aFiberReflectionFixedReferenceVertexSet
    (labeling : BranchOrbitABCReflectionLabeling h) (x : V) :
    x ∈ labeling.aFiberReflectionFixedReferenceVertexSet ↔
      x ∈ labeling.data.toAFiberCoordinates.fiber 0 ∧
        h.smul (DihedralGroup.sr labeling.aFixingReflectionIndex) x = x := by
  simp [aFiberReflectionFixedReferenceVertexSet]

/-- The named solution set is the support complement of the reference
matching-rotation permutation. -/
theorem referenceMatchingSolutionSet_eq_matchingRotationPerm_support_compl
    (labeling : BranchOrbitABCReflectionLabeling h)
    (d : ZMod 19) (hd : d ≠ 0) :
    labeling.referenceMatchingSolutionSet d hd =
      (labeling.data.toAFiberRotationEquivariance.matchingRotationPerm
        d 0 hd).supportᶜ := by
  ext p
  rw [mem_referenceMatchingSolutionSet,
    AFiberRotationEquivariance.mem_matchingRotationPerm_support_compl_iff]

/-- Boundary form: the reference matching solution set is contained in the
fixed-coordinate part of the A-fixing reflection. -/
structure ReferenceRotationMatchingSolutionAFixingSupportComplBoundary
    (labeling : BranchOrbitABCReflectionLabeling h) : Prop where
  reference_matching_solution_subset_aFiberReflectionSupport_compl :
    ∀ d : ZMod 19, ∀ hd : d ≠ 0,
      labeling.referenceMatchingSolutionSet d hd ⊆
        labeling.aFiberReflectionSupportᶜ

namespace ReferenceRotationMatchingSolutionVertexFixedBoundary

variable {labeling : BranchOrbitABCReflectionLabeling h}

/-- Constructor from a pointwise Finset-membership version of the geometric
fixedness statement. -/
noncomputable def of_referenceMatchingSolutionSet_vertex_fixed
    (hfixed :
      ∀ d : ZMod 19, ∀ hd : d ≠ 0,
        ∀ p : labeling.data.toAFiberCoordinates.P,
          p ∈ labeling.referenceMatchingSolutionSet d hd →
            h.smul (DihedralGroup.sr labeling.aFixingReflectionIndex)
                (labeling.referenceFiberVertex p) =
              labeling.referenceFiberVertex p) :
    ReferenceRotationMatchingSolutionVertexFixedBoundary labeling where
  reference_solution_vertex_fixed := by
    intro d hd p hmatch
    exact hfixed d hd p ((labeling.mem_referenceMatchingSolutionSet d hd p).2 hmatch)

/-- Constructor from inclusion of each solution vertex set into the underlying
fixed reference-fiber vertex set. -/
noncomputable def of_referenceMatchingSolutionVertexSet_subset_fixedReferenceVertexSet
    (hsubset :
      ∀ d : ZMod 19, ∀ hd : d ≠ 0,
        labeling.referenceMatchingSolutionVertexSet d hd ⊆
          labeling.aFiberReflectionFixedReferenceVertexSet) :
    ReferenceRotationMatchingSolutionVertexFixedBoundary labeling :=
  of_referenceMatchingSolutionSet_vertex_fixed (labeling := labeling) (by
    intro d hd p hp
    have hv :
        labeling.referenceFiberVertex p ∈
          labeling.referenceMatchingSolutionVertexSet d hd := by
      exact (labeling.mem_referenceMatchingSolutionVertexSet d hd
        (labeling.referenceFiberVertex p)).2 ⟨p, hp, rfl⟩
    have hmem :
        labeling.referenceFiberVertex p ∈
          labeling.aFiberReflectionFixedReferenceVertexSet :=
      hsubset d hd hv
    exact (labeling.mem_aFiberReflectionFixedReferenceVertexSet
      (labeling.referenceFiberVertex p)).1 hmem |>.2)

/-- Constructor from containment of reference matching solutions in
`aFiberReflectionSupportᶜ`. -/
noncomputable def of_referenceMatchingSolutionSet_subset_aFiberReflectionSupport_compl
    (hsubset :
      ∀ d : ZMod 19, ∀ hd : d ≠ 0,
        labeling.referenceMatchingSolutionSet d hd ⊆
          labeling.aFiberReflectionSupportᶜ) :
    ReferenceRotationMatchingSolutionVertexFixedBoundary labeling :=
  of_referenceMatchingSolutionSet_vertex_fixed (labeling := labeling) (by
    intro d hd p hp
    have hpFixed : p ∈ labeling.aFiberReflectionSupportᶜ := hsubset d hd hp
    have hpNotSupport : p ∉ labeling.aFiberReflectionSupport :=
      Finset.mem_compl.mp hpFixed
    have hpCoordFixed : labeling.aFiberReflectionCoordPerm p = p := by
      by_contra hmove
      exact hpNotSupport ((labeling.mem_aFiberReflectionSupport p).2 hmove)
    exact (labeling.aFiberReflectionCoordPerm_fixed_iff_vertex_fixed p).1
      hpCoordFixed)

/-- Constructor from containment of the matching-rotation fixed coordinates in
the A-fixing reflection fixed-coordinate part. -/
noncomputable def of_matchingRotationPerm_support_compl_subset_aFiberReflectionSupport_compl
    (hsubset :
      ∀ d : ZMod 19, ∀ hd : d ≠ 0,
        (labeling.data.toAFiberRotationEquivariance.matchingRotationPerm
          d 0 hd).supportᶜ ⊆
          labeling.aFiberReflectionSupportᶜ) :
    ReferenceRotationMatchingSolutionVertexFixedBoundary labeling :=
  of_referenceMatchingSolutionSet_subset_aFiberReflectionSupport_compl
    (labeling := labeling) (by
      intro d hd p hp
      exact hsubset d hd
        (by
          simpa [labeling.referenceMatchingSolutionSet_eq_matchingRotationPerm_support_compl
            d hd] using hp))

end ReferenceRotationMatchingSolutionVertexFixedBoundary

namespace ReferenceRotationMatchingSolutionAFixingSupportComplBoundary

variable {labeling : BranchOrbitABCReflectionLabeling h}

/-- Collapse the support-complement boundary to the geometric vertex-fixed
boundary. -/
noncomputable def toReferenceRotationMatchingSolutionVertexFixedBoundary
    (boundary :
      ReferenceRotationMatchingSolutionAFixingSupportComplBoundary labeling) :
    ReferenceRotationMatchingSolutionVertexFixedBoundary labeling :=
  ReferenceRotationMatchingSolutionVertexFixedBoundary.of_referenceMatchingSolutionSet_subset_aFiberReflectionSupport_compl
      (labeling := labeling)
      boundary.reference_matching_solution_subset_aFiberReflectionSupport_compl

end ReferenceRotationMatchingSolutionAFixingSupportComplBoundary

end BranchOrbitABCReflectionLabeling

end

end Moore57
