import Moore57.D19OnMoore57.BranchOrbit.BranchOrbitABCPartition
import Moore57.D19OnMoore57.BranchOrbit.BranchOrbitBCSelection

/-!
# Residual split for the B/C selected leaf cover

This file connects the B/C selected-base cover to the residual-side partition.
Once the reflection-copy union is the B/C leaf union, its complement is the
center-neighbor zero part together with the A-side leaf fibers.
-/

namespace Moore57

open Finset

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

namespace D19ActsOnMoore57

variable (h : D19ActsOnMoore57 V Γ)

/-- Branch leaves over disjoint center-neighbor rotation orbits are disjoint. -/
theorem branchOrbitLeaf_disjoint_of_rotationOrbitFinset_disjoint
    {u a b : V}
    (hu : ∀ d : ZMod 19, h.rotation d u = u)
    (ha : Γ.Adj u a) (hb : Γ.Adj u b)
    (hdisj : Disjoint (h.rotationOrbitFinset a) (h.rotationOrbitFinset b)) :
    Disjoint (h.branchOrbitLeaf u a) (h.branchOrbitLeaf u b) := by
  rw [Finset.disjoint_left]
  intro y hyA hyB
  rcases (h.mem_branchOrbitLeaf_iff u a y).mp hyA with ⟨i, hyi⟩
  rcases (h.mem_branchOrbitLeaf_iff u b y).mp hyB with ⟨j, hyj⟩
  have hai : Γ.Adj u (h.rotation i a) :=
    h.adj_rotation_of_fixed_center hu ha i
  have hbj : Γ.Adj u (h.rotation j b) :=
    h.adj_rotation_of_fixed_center hu hb j
  have hne : h.rotation i a ≠ h.rotation j b := by
    intro heq
    have hia : h.rotation i a ∈ h.rotationOrbitFinset a :=
      (h.mem_rotationOrbitFinset a (h.rotation i a)).mpr ⟨i, rfl⟩
    have hjb : h.rotation i a ∈ h.rotationOrbitFinset b := by
      rw [heq]
      exact (h.mem_rotationOrbitFinset b (h.rotation j b)).mpr ⟨j, rfl⟩
    exact (Finset.disjoint_left.mp hdisj) hia hjb
  exact (Finset.disjoint_left.mp
    (h.isMoore.branchFiber_disjoint_of_ne hai hbj hne)) hyi hyj

/-- The zero part `{u} ∪ N(u)` is disjoint from every branch leaf over a
center-neighbor rotation orbit. -/
theorem centerNeighborPart_disjoint_branchOrbitLeaf
    {u b : V}
    (hu : ∀ d : ZMod 19, h.rotation d u = u)
    (hb : Γ.Adj u b) :
    Disjoint (centerNeighborPart Γ u) (h.branchOrbitLeaf u b) := by
  rw [Finset.disjoint_left]
  intro y hyZero hyLeaf
  rcases (h.mem_branchOrbitLeaf_iff u b y).mp hyLeaf with ⟨i, hyi⟩
  rcases (mem_centerNeighborPart (Γ := Γ) u y).mp hyZero with hyu | hyAdj
  · exact (mem_branchFiber.mp hyi).1 hyu
  · have hbi : Γ.Adj u (h.rotation i b) :=
      h.adj_rotation_of_fixed_center hu hb i
    exact h.isMoore.no_triangle hbi (mem_branchFiber.mp hyi).2 hyAdj.symm

end D19ActsOnMoore57

namespace BranchOrbitABCFromCenter

variable {h : D19ActsOnMoore57 V Γ}

/-- The zero part is disjoint from the B/C selected leaf union. -/
theorem zeroPart_disjoint_bSideLeaf_union_cSideLeaf
    (data : BranchOrbitABCFromCenter h) :
    Disjoint (centerNeighborPart Γ data.u) (data.bSideLeaf ∪ data.cSideLeaf) := by
  rw [Finset.disjoint_left]
  intro y hyZero hyBC
  rcases Finset.mem_union.mp hyBC with hyB | hyC
  · exact (Finset.disjoint_left.mp
      (h.centerNeighborPart_disjoint_branchOrbitLeaf data.u_fixed data.b0_adj))
      hyZero hyB
  · exact (Finset.disjoint_left.mp
      (h.centerNeighborPart_disjoint_branchOrbitLeaf data.u_fixed data.c0_adj))
      hyZero hyC

/-- The A-side leaf is disjoint from the B-side leaf. -/
theorem aSideLeaf_disjoint_bSideLeaf
    (data : BranchOrbitABCFromCenter h) :
    Disjoint data.aSideLeaf data.bSideLeaf := by
  exact h.branchOrbitLeaf_disjoint_of_rotationOrbitFinset_disjoint
    data.u_fixed data.a0_adj data.b0_adj
    (by simpa using data.pairwise_disjoint 0 1 (by decide))

/-- The A-side leaf is disjoint from the C-side leaf. -/
theorem aSideLeaf_disjoint_cSideLeaf
    (data : BranchOrbitABCFromCenter h) :
    Disjoint data.aSideLeaf data.cSideLeaf := by
  exact h.branchOrbitLeaf_disjoint_of_rotationOrbitFinset_disjoint
    data.u_fixed data.a0_adj data.c0_adj
    (by simpa using data.pairwise_disjoint 0 2 (by decide))

/-- The A-side leaf is disjoint from the B/C selected leaf union. -/
theorem aSideLeaf_disjoint_bSideLeaf_union_cSideLeaf
    (data : BranchOrbitABCFromCenter h) :
    Disjoint data.aSideLeaf (data.bSideLeaf ∪ data.cSideLeaf) := by
  rw [Finset.disjoint_left]
  intro y hyA hyBC
  rcases Finset.mem_union.mp hyBC with hyB | hyC
  · exact (Finset.disjoint_left.mp data.aSideLeaf_disjoint_bSideLeaf) hyA hyB
  · exact (Finset.disjoint_left.mp data.aSideLeaf_disjoint_cSideLeaf) hyA hyC

/-- Complement form of the Section 7 residual split, before substituting a
specific `reflectionCopyUnion`: the complement of the B/C leaf union is the
zero part together with the A-side leaf. -/
theorem compl_bSideLeaf_union_cSideLeaf_eq_zeroPart_union_aSideLeaf
    (data : BranchOrbitABCFromCenter h) :
    (data.bSideLeaf ∪ data.cSideLeaf)ᶜ =
      centerNeighborPart Γ data.u ∪ data.aSideLeaf := by
  ext y
  constructor
  · intro hyCompl
    have hnotBC : y ∉ data.bSideLeaf ∪ data.cSideLeaf := by
      simpa using hyCompl
    rcases mem_centerNeighborPart_or_allBranchFibers h.isMoore data.u y with
      hyZero | hyBranch
    · exact Finset.mem_union.mpr (Or.inl hyZero)
    · have hyABC :
          y ∈ data.aSideLeaf ∪ (data.bSideLeaf ∪ data.cSideLeaf) := by
        simpa [data.allBranchFibers_eq_a_b_c_leaves]
          using hyBranch
      rcases Finset.mem_union.mp hyABC with hyA | hyBC
      · exact Finset.mem_union.mpr (Or.inr hyA)
      · exact False.elim (hnotBC hyBC)
  · intro hy
    have hnotBC : y ∉ data.bSideLeaf ∪ data.cSideLeaf := by
      intro hyBC
      rcases Finset.mem_union.mp hy with hyZero | hyA
      · exact (Finset.disjoint_left.mp
          data.zeroPart_disjoint_bSideLeaf_union_cSideLeaf) hyZero hyBC
      · exact (Finset.disjoint_left.mp
          data.aSideLeaf_disjoint_bSideLeaf_union_cSideLeaf) hyA hyBC
    simpa using hnotBC

/-- Final residual split for a selected base enumerating `L_{b0}`: if the
reflection sends `b0` to `c0`, then the canonical reflection-copy residual is
`zeroPart ∪ A_fiber`. -/
theorem reflectionCopyResidual_b0FiberBase_eq_zeroPart_union_aFibers
    (data : BranchOrbitABCFromCenter h)
    (e : Fin 56 ≃ {x : V // x ∈ branchFiber Γ data.u data.b0})
    {k : ZMod 19}
    (href : h.smul (DihedralGroup.sr k) data.b0 = data.c0) :
    reflectionCopyResidual h (data.b0FiberBase e) k =
      centerNeighborPart Γ data.u ∪ data.toAFiberCoordinates.allFibers := by
  rw [reflectionCopyResidual,
    data.reflectionCopyUnion_b0FiberBase_eq_bSideLeaf_union_cSideLeaf e href,
    data.compl_bSideLeaf_union_cSideLeaf_eq_zeroPart_union_aSideLeaf,
    data.aSideLeaf_eq_allFibers]

/-- Final residual split for the canonical B-fiber selected input.  This is
the Section 7 residual identity in the form consumed by the downstream
`BranchOrbitABCData` bridge. -/
theorem reflectionCopyResidual_toOrbitBaseSelectionInputFromBFibers_eq_zeroPart_union_aFibers
    (data : BranchOrbitABCFromCenter h)
    {k : ZMod 19}
    (href : h.smul (DihedralGroup.sr k) data.b0 = data.c0) :
    reflectionCopyResidual h data.toOrbitBaseSelectionInputFromBFibers.base k =
      centerNeighborPart Γ data.u ∪ data.toAFiberCoordinates.allFibers := by
  rw [data.toOrbitBaseSelectionInputFromBFibers_base_eq_b0FiberBase]
  exact
    data.reflectionCopyResidual_b0FiberBase_eq_zeroPart_union_aFibers
      data.toBFiberCoordinatesBaseFiberEquiv href

end BranchOrbitABCFromCenter

end

end Moore57
