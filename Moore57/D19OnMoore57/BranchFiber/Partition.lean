import Moore57.Moore57Graph.Moore57Definition
import Moore57.D19OnMoore57.Action.D19Action
import Moore57.D19OnMoore57.Rotation.OrbitFinset

/-!
# Partition by the center, its neighbors, and branch fibers

This file records the elementary Moore-graph partition used by the Section 7
residual split: every vertex is either the center, a center-neighbor, or lies
in one of the branch fibers over a center-neighbor.
-/

namespace Moore57

open Finset

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- The zero-contribution part around `u`: the center together with its
neighbors. -/
def centerNeighborPart (Γ : SimpleGraph V) [DecidableRel Γ.Adj] (u : V) :
    Finset V :=
  insert u (Γ.neighborFinset u)

/-- The union of all branch fibers over the neighbors of `u`. -/
def allBranchFibers (Γ : SimpleGraph V) [DecidableRel Γ.Adj] (u : V) :
    Finset V :=
  (Γ.neighborFinset u).biUnion fun b => branchFiber Γ u b

/-- The union of branch fibers over one rotation orbit of center-neighbors. -/
def branchOrbitLeafUnion
    (h : D19ActsOnMoore57 V Γ) (u b : V) : Finset V :=
  (h.rotationOrbitFinset b).biUnion fun c => branchFiber Γ u c

@[simp] theorem mem_centerNeighborPart (u x : V) :
    x ∈ centerNeighborPart Γ u ↔ x = u ∨ Γ.Adj u x := by
  simp [centerNeighborPart, SimpleGraph.mem_neighborFinset]

theorem mem_allBranchFibers_iff (u x : V) :
    x ∈ allBranchFibers Γ u ↔
      ∃ b : V, Γ.Adj u b ∧ x ∈ branchFiber Γ u b := by
  constructor
  · intro hx
    rcases Finset.mem_biUnion.mp hx with ⟨b, hb, hxb⟩
    exact ⟨b, by simpa [SimpleGraph.mem_neighborFinset] using hb, hxb⟩
  · rintro ⟨b, hub, hxb⟩
    exact Finset.mem_biUnion.mpr
      ⟨b, by simpa [SimpleGraph.mem_neighborFinset] using hub, hxb⟩

theorem mem_branchOrbitLeafUnion_iff
    (h : D19ActsOnMoore57 V Γ) (u b x : V) :
    x ∈ branchOrbitLeafUnion h u b ↔
      ∃ c : V, c ∈ h.rotationOrbitFinset b ∧ x ∈ branchFiber Γ u c := by
  classical
  simp [branchOrbitLeafUnion]

/-- Every vertex is either `u`, adjacent to `u`, or in a branch fiber over a
neighbor of `u`. -/
theorem centerNeighborPart_union_allBranchFibers_eq_univ
    (hΓ : IsMoore57 Γ) (u : V) :
    centerNeighborPart Γ u ∪ allBranchFibers Γ u = (Finset.univ : Finset V) := by
  ext x
  constructor
  · intro _hx
    exact Finset.mem_univ x
  · intro _hx
    by_cases hxu : x = u
    · exact Finset.mem_union.mpr
        (Or.inl ((mem_centerNeighborPart (Γ := Γ) u x).mpr (Or.inl hxu)))
    · by_cases hAdj : Γ.Adj u x
      · exact Finset.mem_union.mpr
          (Or.inl ((mem_centerNeighborPart (Γ := Γ) u x).mpr (Or.inr hAdj)))
      · have hux : u ≠ x := by
          intro h
          exact hxu h.symm
        rcases hΓ.existsUnique_branch_of_not_adj_center hux hAdj with
          ⟨b, hb, _huniq⟩
        exact Finset.mem_union.mpr
          (Or.inr ((mem_allBranchFibers_iff (Γ := Γ) u x).mpr
            ⟨b, hb.1, hb.2⟩))

/-- Membership form of `centerNeighborPart_union_allBranchFibers_eq_univ`. -/
theorem mem_centerNeighborPart_or_allBranchFibers
    (hΓ : IsMoore57 Γ) (u x : V) :
  x ∈ centerNeighborPart Γ u ∨ x ∈ allBranchFibers Γ u := by
  have hx : x ∈ centerNeighborPart Γ u ∪ allBranchFibers Γ u := by
    simp [centerNeighborPart_union_allBranchFibers_eq_univ hΓ u]
  exact Finset.mem_union.mp hx

end

end Moore57
