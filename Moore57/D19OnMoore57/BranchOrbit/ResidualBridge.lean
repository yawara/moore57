import Moore57.D19OnMoore57.BranchOrbit.ABCData
import Moore57.D19OnMoore57.BranchOrbit.ABCFinalBridge
import Moore57.D19OnMoore57.BranchOrbit.ABCFromCenter
import Moore57.D19OnMoore57.Rotation.OneMovingResidualProperties
import Moore57.D19OnMoore57.AFiber.ResidualSplitBridge

/-!
# Branch-orbit residual classification bridge and geometry

This file unifies two thematic upstream layers of the residual analysis:

* **Residual bridge** (formerly `ABCResidualBridge`): semantic residual
  classification — every non-fixed reflection-copy residual vertex lies in
  the A-fibers — implies the raw moving-residual containment used by the
  no-fixed-boundary constructors.
* **Residual geometry** (formerly `ABCResidualGeometry`): reduces the
  classification assumption to two more geometric facts — non-fixed residual
  vertices are not adjacent to the center, and their unique branch fiber is
  an A-branch orbit.

The downstream "Split"/"Contribution" layer lives in
`BranchOrbit/ResidualSplit.lean`, which depends on `ABCPartition` and is
therefore separated from this file (`ABCPartition` itself depends on the
geometry below).
-/

namespace Moore57

open Finset

noncomputable section

universe u uP

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-! ## A-fiber non-adjacency to the center -/

namespace AFiberCoordinates

variable (coords : AFiberCoordinates.{u, uP} Γ)

/-- A vertex in a selected A-fiber union is not adjacent to the center. -/
theorem not_adj_center_of_mem_fiberUnion
    (hΓ : IsMoore57 Γ) {indices : Finset (ZMod 19)} {y : V}
    (hy : y ∈ coords.fiberUnion indices) :
    ¬ Γ.Adj coords.u y := by
  rcases (coords.mem_fiberUnion_iff indices y).mp hy with
    ⟨i, _hi, hyi⟩
  exact hΓ.not_adj_center_of_mem_branchFiber (coords.hub i) hyi

/-- A vertex in the union of all A-fibers is not adjacent to the center. -/
theorem not_adj_center_of_mem_allFibers
    (hΓ : IsMoore57 Γ) {y : V}
    (hy : y ∈ coords.allFibers) :
    ¬ Γ.Adj coords.u y := by
  exact coords.not_adj_center_of_mem_fiberUnion hΓ
    (indices := Finset.univ) hy

end AFiberCoordinates

/-! ## Bridge: residual classification → moving-residual containment -/

namespace BranchOrbitABCData

variable {h : D19ActsOnMoore57 V Γ}

/-- Semantic residual classification implies the raw moving-residual
containment used by the no-fixed-boundary constructors. -/
theorem rotationOneMovingResidualPart_subset_allFibers_of_nonfixed_residual_subset
    (data : BranchOrbitABCData h) (k : ZMod 19)
    (hnonfixed :
      ∀ y : V,
        y ∈ reflectionCopyResidual h data.toOrbitBaseSelectionInput.base k →
          y ∉ fixedVertexSet (h.rotation 1) →
            y ∈ data.toAFiberCoordinates.allFibers) :
    rotationOneMovingResidualPart h data.toOrbitBaseSelectionInput k ⊆
      data.toAFiberCoordinates.allFibers := by
  intro y hy
  have hymem := mem_rotationOneMovingResidualPart_iff.mp hy
  exact hnonfixed y hymem.1 hymem.2

/-- The same bridge, expressed with `indices = Finset.univ`, for APIs that are
written in terms of `fiberUnion`. -/
theorem rotationOneMovingResidualPart_subset_fiberUnion_univ_of_nonfixed_residual_subset
    (data : BranchOrbitABCData h) (k : ZMod 19)
    (hnonfixed :
      ∀ y : V,
        y ∈ reflectionCopyResidual h data.toOrbitBaseSelectionInput.base k →
          y ∉ fixedVertexSet (h.rotation 1) →
            y ∈ data.toAFiberCoordinates.allFibers) :
    rotationOneMovingResidualPart h data.toOrbitBaseSelectionInput k ⊆
      data.toAFiberCoordinates.fiberUnion Finset.univ := by
  simpa [AFiberCoordinates.allFibers] using
    data.rotationOneMovingResidualPart_subset_allFibers_of_nonfixed_residual_subset
      k hnonfixed

/-- Build the direct-character no-fixed boundary from the semantic residual
classification, selecting all A-fibers. -/
def toCharacterAFiberNoFixedBoundaryInputsFromOrbitBaseResidualClassification
    (data : BranchOrbitABCData h)
    (representation : D19ActsOnMoore57.D19RepresentationCharacterInput h)
    (k : ZMod 19)
    (reflection_not_mem_orbitFamilyUnion :
      ∀ r : Fin 56,
        h.smul (DihedralGroup.sr k) (data.toOrbitBaseSelectionInput.base r) ∉
          data.toOrbitBaseSelectionInput.orbitFamilyUnion)
    (hnonfixed :
      ∀ y : V,
        y ∈ reflectionCopyResidual h data.toOrbitBaseSelectionInput.base k →
          y ∉ fixedVertexSet (h.rotation 1) →
            y ∈ data.toAFiberCoordinates.allFibers)
    (aFiber_subset_residual :
      data.toAFiberCoordinates.fiberUnion Finset.univ ⊆
        reflectionCopyResidual h data.toOrbitBaseSelectionInput.base k)
    (aFiberCardinality :
      AFiberCardinality38Boundary h data.toAFiberCoordinates Finset.univ) :
    D19FinalCharacterAFiberNoFixedBoundaryInputs.{u, u} h :=
  data.toCharacterAFiberNoFixedBoundaryInputsFromOrbitBase
    representation k Finset.univ reflection_not_mem_orbitFamilyUnion
    (data.rotationOneMovingResidualPart_subset_fiberUnion_univ_of_nonfixed_residual_subset
      k hnonfixed)
    aFiber_subset_residual aFiberCardinality

/-- A split-equality helper for callers that also know all A-fibers are
residual. -/
theorem reflectionCopyResidual_eq_fixed_union_allFibers_of_nonfixed_residual_subset
    (data : BranchOrbitABCData h) (k : ZMod 19)
    (hnonfixed :
      ∀ y : V,
        y ∈ reflectionCopyResidual h data.toOrbitBaseSelectionInput.base k →
          y ∉ fixedVertexSet (h.rotation 1) →
            y ∈ data.toAFiberCoordinates.allFibers)
    (hallFibers_subset_residual :
      data.toAFiberCoordinates.allFibers ⊆
        reflectionCopyResidual h data.toOrbitBaseSelectionInput.base k) :
    reflectionCopyResidual h data.toOrbitBaseSelectionInput.base k =
      rotationOneFixedResidualPart h data.toOrbitBaseSelectionInput k ∪
        data.toAFiberCoordinates.allFibers := by
  simpa [AFiberCoordinates.allFibers] using
    (reflectionCopyResidual_eq_fixed_union_fiberUnion_of_nonfixed_residual_subset
      (h := h) (input := data.toOrbitBaseSelectionInput) (k := k)
      (coords := data.toAFiberCoordinates) (indices := Finset.univ)
      hnonfixed
      (by
        simpa [AFiberCoordinates.allFibers] using
          hallFibers_subset_residual))

/-! ## Geometry: residual classification from non-adjacency and branch -/

/-- The center stored in `BranchOrbitABCData` is the canonical rotation-fixed
center. -/
theorem u_eq_rotationFixedCenter
    (data : BranchOrbitABCData h) :
    data.u = h.rotationFixedCenter :=
  h.eq_rotationFixedCenter_of_rotation_one_fixed (data.u_fixed 1)

/-- A vertex outside the rotation-one fixed set is not the stored center. -/
theorem ne_u_of_not_mem_fixedVertexSet
    (data : BranchOrbitABCData h) {y : V}
    (hy : y ∉ fixedVertexSet (h.rotation 1)) :
    data.u ≠ y := by
  intro huy
  exact hy (mem_fixedVertexSet.mpr (by
    rw [← huy]
    exact data.u_fixed 1))

/-- Membership in the A-fibers generated by `BranchOrbitABCData`, expanded to
the corresponding A-branch rotation orbit. -/
theorem mem_toAFiberCoordinates_allFibers_iff
    (data : BranchOrbitABCData h) (y : V) :
    y ∈ data.toAFiberCoordinates.allFibers ↔
      ∃ i : ZMod 19,
        y ∈ branchFiber Γ data.u (h.rotation i data.a0) := by
  simpa [BranchOrbitABCData.toAFiberCoordinates] using
    data.toAFiberCoordinates.mem_allFibers_iff y

/-- If the branch fiber containing a vertex lies over an A-branch orbit, then
the vertex lies in the generated A-fibers. -/
theorem mem_allFibers_of_mem_branchFiber_aOrbit
    (data : BranchOrbitABCData h) {b y : V}
    (hb : b ∈ h.rotationOrbitFinset data.a0)
    (hy : y ∈ branchFiber Γ data.u b) :
    y ∈ data.toAFiberCoordinates.allFibers := by
  rcases (h.mem_rotationOrbitFinset data.a0 b).mp hb with ⟨i, hi⟩
  rw [data.mem_toAFiberCoordinates_allFibers_iff]
  exact ⟨i, by simpa [hi] using hy⟩

/-- A direct residual-classification assumption forces non-fixed residual
vertices to be non-neighbors of the A-fiber center.  This records a necessary
condition for proving the classification from geometry. -/
theorem nonfixed_residual_not_adj_center_of_nonfixed_residual_subset
    (data : BranchOrbitABCData h) (k : ZMod 19)
    (hnonfixed :
      ∀ ⦃y : V⦄,
        y ∈ reflectionCopyResidual h data.toOrbitBaseSelectionInput.base k →
          y ∉ fixedVertexSet (h.rotation 1) →
            y ∈ data.toAFiberCoordinates.allFibers) :
    ∀ ⦃y : V⦄,
      y ∈ reflectionCopyResidual h data.toOrbitBaseSelectionInput.base k →
        y ∉ fixedVertexSet (h.rotation 1) →
          ¬ Γ.Adj data.u y := by
  intro y hyResidual hyNonfixed
  exact data.toAFiberCoordinates.not_adj_center_of_mem_allFibers
    h.isMoore (hnonfixed hyResidual hyNonfixed)

/-- Reduce the residual-classification assumption to two geometric facts:
non-fixed residual vertices are not center-neighbors, and their unique branch
fiber lies over the A-branch orbit. -/
theorem nonfixed_residual_subset_allFibers_of_not_adj_center_and_branch_mem_aOrbit
    (data : BranchOrbitABCData h) (k : ZMod 19)
    (hnotAdjCenter :
      ∀ ⦃y : V⦄,
        y ∈ reflectionCopyResidual h data.toOrbitBaseSelectionInput.base k →
          y ∉ fixedVertexSet (h.rotation 1) →
            ¬ Γ.Adj data.u y)
    (hbranchA :
      ∀ ⦃y b : V⦄,
        y ∈ reflectionCopyResidual h data.toOrbitBaseSelectionInput.base k →
          y ∉ fixedVertexSet (h.rotation 1) →
            Γ.Adj data.u b →
              y ∈ branchFiber Γ data.u b →
                b ∈ h.rotationOrbitFinset data.a0) :
    ∀ ⦃y : V⦄,
      y ∈ reflectionCopyResidual h data.toOrbitBaseSelectionInput.base k →
        y ∉ fixedVertexSet (h.rotation 1) →
          y ∈ data.toAFiberCoordinates.allFibers := by
  intro y hyResidual hyNonfixed
  have hy_ne_u : data.u ≠ y := data.ne_u_of_not_mem_fixedVertexSet hyNonfixed
  rcases h.isMoore.existsUnique_branch_of_not_adj_center
      hy_ne_u (hnotAdjCenter hyResidual hyNonfixed) with
    ⟨b, hb, _huniq⟩
  exact data.mem_allFibers_of_mem_branchFiber_aOrbit
    (hbranchA hyResidual hyNonfixed hb.1 hb.2) hb.2

end BranchOrbitABCData

/-! ## Geometry helpers in `BranchOrbitABCFromCenter` -/

namespace BranchOrbitABCFromCenter

variable {h : D19ActsOnMoore57 V Γ}

/-- Membership in the A-fibers generated from center-neighbor data, expanded
to the corresponding A-branch rotation orbit. -/
theorem mem_toAFiberCoordinates_allFibers_iff
    (data : BranchOrbitABCFromCenter h) (y : V) :
    y ∈ data.toAFiberCoordinates.allFibers ↔
      ∃ i : ZMod 19,
        y ∈ branchFiber Γ data.u (h.rotation i data.a0) := by
  simpa [BranchOrbitABCFromCenter.toAFiberCoordinates] using
    data.toAFiberCoordinates.mem_allFibers_iff y

/-- Center-neighbor data covers every center-neighbor by one of the three
branch rotation orbits. -/
theorem neighbor_mem_a_or_b_or_c_orbit
    (data : BranchOrbitABCFromCenter h) {b : V}
    (hb : Γ.Adj data.u b) :
    b ∈ h.rotationOrbitFinset data.a0 ∨
      b ∈ h.rotationOrbitFinset data.b0 ∨
        b ∈ h.rotationOrbitFinset data.c0 := by
  have hbNeighbor : b ∈ Γ.neighborFinset data.u := by
    simpa [SimpleGraph.mem_neighborFinset] using hb
  have hbUnion : b ∈ h.orbitFamilyUnion data.base := by
    simpa [data.cover_neighbors] using hbNeighbor
  rcases (h.mem_orbitFamilyUnion data.base b).mp hbUnion with
    ⟨q, i, hi⟩
  have hbOrbit : b ∈ h.rotationOrbitFinset (data.base q) :=
    (h.mem_rotationOrbitFinset (data.base q) b).mpr ⟨i, hi⟩
  fin_cases q
  · exact Or.inl (by simpa using hbOrbit)
  · exact Or.inr (Or.inl (by simpa using hbOrbit))
  · exact Or.inr (Or.inr (by simpa using hbOrbit))

/-- If the branch fiber containing a vertex lies over an A-branch orbit, then
the vertex lies in the generated A-fibers. -/
theorem mem_allFibers_of_mem_branchFiber_aOrbit
    (data : BranchOrbitABCFromCenter h) {b y : V}
    (hb : b ∈ h.rotationOrbitFinset data.a0)
    (hy : y ∈ branchFiber Γ data.u b) :
    y ∈ data.toAFiberCoordinates.allFibers := by
  rcases (h.mem_rotationOrbitFinset data.a0 b).mp hb with ⟨i, hi⟩
  rw [data.mem_toAFiberCoordinates_allFibers_iff]
  exact ⟨i, by simpa [hi] using hy⟩

/-- Center-neighbor data proves A-fiber membership once the residual vertex is
known to be non-adjacent to the center and its unique branch is known to be in
the A-branch orbit. -/
theorem mem_allFibers_of_not_adj_center_and_branch_mem_aOrbit
    (data : BranchOrbitABCFromCenter h) {y : V}
    (hy_ne_u : data.u ≠ y)
    (hnotAdjCenter : ¬ Γ.Adj data.u y)
    (hbranchA :
      ∀ ⦃b : V⦄,
        Γ.Adj data.u b →
          y ∈ branchFiber Γ data.u b →
            b ∈ h.rotationOrbitFinset data.a0) :
    y ∈ data.toAFiberCoordinates.allFibers := by
  rcases h.isMoore.existsUnique_branch_of_not_adj_center
      hy_ne_u hnotAdjCenter with
    ⟨b, hb, _huniq⟩
  exact data.mem_allFibers_of_mem_branchFiber_aOrbit
    (hbranchA hb.1 hb.2) hb.2

end BranchOrbitABCFromCenter

end

end Moore57
