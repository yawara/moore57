import Moore57.D19OnMoore57.BranchFiber.BranchFiberPartition
import Moore57.D19OnMoore57.AFiber.AFiberCoordinateOrbit

/-!
# Zero contribution from the center-neighbor part

The Section 7 residual split leaves the center together with its neighbors as
one residual piece.  This file records the elementary Moore-graph fact that
this piece contributes zero to the adjacent-moved count for any rotation: the
center is fixed, and two distinct center-neighbors cannot be adjacent because
there are no triangles.
-/

namespace Moore57

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

namespace D19ActsOnMoore57

variable (h : D19ActsOnMoore57 V Γ)

/-- A vertex in `{u} ∪ N(u)` is not adjacent to its image under any rotation,
provided `u` is fixed by the rotation subgroup. -/
theorem centerNeighborPart_not_adjacent_rotation
    {u y : V} (hu : ∀ d : ZMod 19, h.rotation d u = u)
    (d : ZMod 19)
    (hy : y ∈ centerNeighborPart Γ u) :
    ¬ Γ.Adj y (h.rotation d y) := by
  intro hyAdjRot
  rcases (mem_centerNeighborPart (Γ := Γ) u y).mp hy with rfl | hyAdj
  · rw [hu d] at hyAdjRot
    exact SimpleGraph.irrefl Γ hyAdjRot
  · have huRot : Γ.Adj u (h.rotation d y) :=
      h.adj_rotation_of_fixed_center hu hyAdj d
    exact h.isMoore.no_triangle hyAdj hyAdjRot huRot.symm

/-- The adjacent-rotation filtered cardinality of `{u} ∪ N(u)` is zero. -/
theorem centerNeighborPart_filter_adjacent_rotation_card_eq_zero
    {u : V} (hu : ∀ d : ZMod 19, h.rotation d u = u)
    (d : ZMod 19) :
    ((centerNeighborPart Γ u).filter fun y =>
      Γ.Adj y (h.rotation d y)).card = 0 := by
  rw [Finset.card_eq_zero]
  ext y
  constructor
  · intro hy
    rcases Finset.mem_filter.mp hy with ⟨hyPart, hyAdj⟩
    exact False.elim
      (h.centerNeighborPart_not_adjacent_rotation hu d hyPart hyAdj)
  · intro hy
    simp at hy

end D19ActsOnMoore57

end Moore57
