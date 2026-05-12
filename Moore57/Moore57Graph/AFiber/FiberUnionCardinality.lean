import Moore57.D19OnMoore57.AdjacentMoved.ReflectionAFiber

/-!
# Cardinality of selected A-fiber unions

This file records the finite-set bookkeeping for unions of selected
`AFiberCoordinates` branch fibers.  Distinct A-side branches over the same
center have disjoint branch fibers, so the selected union has cardinality
`56` times the number of selected indices in a Moore57 graph.
-/

namespace Moore57

open Finset

namespace IsMoore57

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- Branch fibers over distinct neighbors of the same center are disjoint. -/
theorem branchFiber_disjoint_of_ne
    (hΓ : IsMoore57 Γ) {u a b : V}
    (hua : Γ.Adj u a) (hub : Γ.Adj u b) (hab : a ≠ b) :
    Disjoint (branchFiber Γ u a) (branchFiber Γ u b) := by
  rw [Finset.disjoint_left]
  intro x hxa hxb
  exact (hΓ.not_adj_other_branch_of_mem_branchFiber hua hub hab hxa)
    (mem_branchFiber.mp hxb).2.symm

end IsMoore57

namespace AFiberCoordinates

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- The selected branch fibers in an `AFiberCoordinates` system are pairwise
disjoint. -/
theorem fiberUnion_pairwiseDisjoint
    (A : AFiberCoordinates Γ) (hΓ : IsMoore57 Γ)
    (indices : Finset (ZMod 19)) :
    (indices : Set (ZMod 19)).PairwiseDisjoint fun i => A.fiber i := by
  intro i _hi j _hj hij
  exact hΓ.branchFiber_disjoint_of_ne (A.hub i) (A.hub j) (A.a_ne hij)

/-- Cardinality of a selected union of A-side branch fibers. -/
theorem fiberUnion_card
    (A : AFiberCoordinates Γ) (hΓ : IsMoore57 Γ)
    (indices : Finset (ZMod 19)) :
    (A.fiberUnion indices).card = indices.card * 56 := by
  classical
  calc
    (A.fiberUnion indices).card = ∑ i ∈ indices, (A.fiber i).card := by
      simpa [fiberUnion] using
        (Finset.card_biUnion
          (s := indices)
          (t := fun i : ZMod 19 => A.fiber i)
          (A.fiberUnion_pairwiseDisjoint hΓ indices))
    _ = ∑ _i ∈ indices, 56 := by
      refine Finset.sum_congr rfl ?_
      intro i _hi
      simp [fiber, A.fiber_card hΓ i]
    _ = indices.card * 56 := by
      simp [Finset.sum_const]

end AFiberCoordinates

end Moore57
