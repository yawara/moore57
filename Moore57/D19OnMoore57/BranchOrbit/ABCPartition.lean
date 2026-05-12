import Moore57.D19OnMoore57.BranchOrbit.BCSelectionCover
import Moore57.D19OnMoore57.BranchOrbit.ABCResidualGeometry
import Moore57.D19OnMoore57.BranchFiber.Partition

/-!
# A/B/C branch-leaf partition

This file connects the fixed-center neighbor-orbit decomposition with the
global branch-fiber partition.  The branch fibers split into the A-, B-, and
C-side leaves; the A-side leaf is the same finset as the A-fiber coordinate
union used in the final boundary.
-/

namespace Moore57

open Finset

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

namespace BranchOrbitABCFromCenter

variable {h : D19ActsOnMoore57 V Γ}

/-- The A-side leaf over the rotation orbit of `a0`. -/
noncomputable abbrev aSideLeaf (data : BranchOrbitABCFromCenter h) :
    Finset V :=
  h.branchOrbitLeaf data.u data.a0

/-- The A-side branch leaf is exactly the all-A-fiber union from the A
coordinate system. -/
theorem aSideLeaf_eq_allFibers
    (data : BranchOrbitABCFromCenter h) :
    data.aSideLeaf = data.toAFiberCoordinates.allFibers := by
  ext y
  rw [D19ActsOnMoore57.mem_branchOrbitLeaf_iff]
  exact (data.mem_toAFiberCoordinates_allFibers_iff y).symm

/-- Each of the A/B/C branch leaves is contained in the union of all branch
fibers over center-neighbors. -/
theorem branchOrbitLeaf_subset_allBranchFibers_of_adj
    (data : BranchOrbitABCFromCenter h) {b : V}
    (hb : Γ.Adj data.u b) :
    h.branchOrbitLeaf data.u b ⊆ allBranchFibers Γ data.u := by
  intro y hy
  rcases (D19ActsOnMoore57.mem_branchOrbitLeaf_iff h data.u b y).mp hy with
    ⟨i, hyi⟩
  exact (mem_allBranchFibers_iff (Γ := Γ) data.u y).mpr
    ⟨h.rotation i b,
      h.adj_rotation_of_fixed_center data.u_fixed hb i,
      hyi⟩

/-- The all-branch-fiber union is contained in the union of the A/B/C branch
leaves. -/
theorem allBranchFibers_subset_a_b_c_leaves
    (data : BranchOrbitABCFromCenter h) :
    allBranchFibers Γ data.u ⊆
      data.aSideLeaf ∪ (data.bSideLeaf ∪ data.cSideLeaf) := by
  intro y hy
  rcases (mem_allBranchFibers_iff (Γ := Γ) data.u y).mp hy with
    ⟨b, hbAdj, hyb⟩
  rcases data.neighbor_mem_a_or_b_or_c_orbit hbAdj with hbA | hbB | hbC
  · exact Finset.mem_union.mpr
      (Or.inl
        ((D19ActsOnMoore57.mem_branchOrbitLeaf_iff h data.u data.a0 y).mpr
          (by
            rcases (h.mem_rotationOrbitFinset data.a0 b).mp hbA with
              ⟨i, hi⟩
            exact ⟨i, by simpa [hi] using hyb⟩)))
  · exact Finset.mem_union.mpr
      (Or.inr (Finset.mem_union.mpr
        (Or.inl
          ((D19ActsOnMoore57.mem_branchOrbitLeaf_iff h data.u data.b0 y).mpr
            (by
              rcases (h.mem_rotationOrbitFinset data.b0 b).mp hbB with
                ⟨i, hi⟩
              exact ⟨i, by simpa [hi] using hyb⟩)))))
  · exact Finset.mem_union.mpr
      (Or.inr (Finset.mem_union.mpr
        (Or.inr
          ((D19ActsOnMoore57.mem_branchOrbitLeaf_iff h data.u data.c0 y).mpr
            (by
              rcases (h.mem_rotationOrbitFinset data.c0 b).mp hbC with
                ⟨i, hi⟩
              exact ⟨i, by simpa [hi] using hyb⟩)))))

/-- The union of all branch fibers over center-neighbors is exactly the union
of the A-, B-, and C-side branch leaves. -/
theorem allBranchFibers_eq_a_b_c_leaves
    (data : BranchOrbitABCFromCenter h) :
    allBranchFibers Γ data.u =
      data.aSideLeaf ∪ (data.bSideLeaf ∪ data.cSideLeaf) := by
  apply Finset.Subset.antisymm
  · exact data.allBranchFibers_subset_a_b_c_leaves
  · intro y hy
    rcases Finset.mem_union.mp hy with hyA | hyBC
    · exact data.branchOrbitLeaf_subset_allBranchFibers_of_adj data.a0_adj hyA
    · rcases Finset.mem_union.mp hyBC with hyB | hyC
      · exact data.branchOrbitLeaf_subset_allBranchFibers_of_adj data.b0_adj hyB
      · exact data.branchOrbitLeaf_subset_allBranchFibers_of_adj data.c0_adj hyC

/-- Center-neighbor part plus the A/B/C branch leaves covers all vertices. -/
theorem centerNeighbor_union_a_b_c_leaves_eq_univ
    (data : BranchOrbitABCFromCenter h) :
    centerNeighborPart Γ data.u ∪
        (data.aSideLeaf ∪ (data.bSideLeaf ∪ data.cSideLeaf)) =
      (Finset.univ : Finset V) := by
  rw [← data.allBranchFibers_eq_a_b_c_leaves]
  exact centerNeighborPart_union_allBranchFibers_eq_univ h.isMoore data.u

end BranchOrbitABCFromCenter

end

end Moore57
