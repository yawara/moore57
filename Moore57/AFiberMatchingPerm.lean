import Moore57.AFiberCoordinates
import Moore57.BranchFiberMatching

/-!
# Coordinate permutations from A-side fiber matchings

This file transports the Moore57 branch-fiber matching between two distinct
A-side fibers through an `AFiberCoordinates` chart, obtaining a permutation of
the common coordinate set.
-/

namespace Moore57

namespace AFiberCoordinates

variable {V : Type*} [Fintype V] [DecidableEq V]
    {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- The perfect matching from the `i`-th A-side fiber to the `j`-th A-side
fiber, transported to the common coordinate set. -/
noncomputable def matchingEquiv
    (hΓ : IsMoore57 Γ) (coords : AFiberCoordinates Γ)
    (i j : ZMod 19) (hij : i ≠ j) : coords.P ≃ coords.P :=
  ((coords.coord i).trans
      (hΓ.branchFiberMatchingEquiv (coords.hub i) (coords.hub j)
        (coords.a_ne hij))).trans
    (coords.coord j).symm

@[simp] theorem matchingEquiv_apply
    (hΓ : IsMoore57 Γ) (coords : AFiberCoordinates Γ)
    (i j : ZMod 19) (hij : i ≠ j) (p : coords.P) :
    matchingEquiv hΓ coords i j hij p =
      (coords.coord j).symm
        (hΓ.branchFiberMatchingEquiv (coords.hub i) (coords.hub j)
          (coords.a_ne hij) (coords.coord i p)) :=
  rfl

/-- Coordinate form of the branch-fiber matching: two coordinate points in
distinct A-side fibers are adjacent exactly when the transported matching sends
the first coordinate to the second. -/
theorem adj_iff_matchingEquiv_eq
    (hΓ : IsMoore57 Γ) (coords : AFiberCoordinates Γ)
    {i j : ZMod 19} (hij : i ≠ j) (p q : coords.P) :
    Γ.Adj
        (((coords.coord i) p :
          {x : V // x ∈ branchFiber Γ coords.u (coords.a i)}) : V)
        (((coords.coord j) q :
          {x : V // x ∈ branchFiber Γ coords.u (coords.a j)}) : V) ↔
      matchingEquiv hΓ coords i j hij p = q := by
  constructor
  · intro hpq
    have hmatch :
        hΓ.branchFiberMatchingEquiv (coords.hub i) (coords.hub j)
            (coords.a_ne hij) (coords.coord i p) =
          coords.coord j q :=
      hΓ.branchFiberMate_eq_of_adj (coords.hub i) (coords.hub j)
        (coords.a_ne hij) (coords.coord i p) (coords.coord j q) hpq
    simp [hmatch]
  · intro hpq
    have hmate :
        hΓ.branchFiberMate (coords.hub i) (coords.hub j)
            (coords.a_ne hij) (coords.coord i p) =
          coords.coord j q := by
      simpa [matchingEquiv, IsMoore57.branchFiberMatchingEquiv] using
        congrArg (coords.coord j) hpq
    simpa [hmate] using
      hΓ.branchFiberMate_adj (coords.hub i) (coords.hub j)
        (coords.a_ne hij) (coords.coord i p)

/-- If two coordinate representatives in distinct A-side fibers are adjacent,
then the transported matching sends the first coordinate to the second. -/
theorem matchingEquiv_eq_of_adj
    (hΓ : IsMoore57 Γ) (coords : AFiberCoordinates Γ)
    {i j : ZMod 19} (hij : i ≠ j) {p q : coords.P}
    (hpq :
      Γ.Adj
        (((coords.coord i) p :
          {x : V // x ∈ branchFiber Γ coords.u (coords.a i)}) : V)
        (((coords.coord j) q :
          {x : V // x ∈ branchFiber Γ coords.u (coords.a j)}) : V)) :
    matchingEquiv hΓ coords i j hij p = q :=
  (adj_iff_matchingEquiv_eq hΓ coords hij p q).1 hpq

/-- Coordinate vertices in distinct A-side branch fibers are distinct. -/
theorem coord_ne_of_index_ne
    (hΓ : IsMoore57 Γ) (coords : AFiberCoordinates Γ)
    {i j : ZMod 19} (hij : i ≠ j) (p q : coords.P) :
    (((coords.coord i p :
      {x : V // x ∈ branchFiber Γ coords.u (coords.a i)}) : V)) ≠
      (((coords.coord j q :
        {x : V // x ∈ branchFiber Γ coords.u (coords.a j)}) : V)) := by
  intro hcoord
  have hxmem :
      (((coords.coord i p :
        {x : V // x ∈ branchFiber Γ coords.u (coords.a i)}) : V)) ∈
        branchFiber Γ coords.u (coords.a i) :=
    coords.coord_mem i p
  have hyadj :
      Γ.Adj (coords.a j)
        (((coords.coord i p :
          {x : V // x ∈ branchFiber Γ coords.u (coords.a i)}) : V)) := by
    have hymem :
        (((coords.coord i p :
          {x : V // x ∈ branchFiber Γ coords.u (coords.a i)}) : V)) ∈
          branchFiber Γ coords.u (coords.a j) := by
      simp [hcoord, coords.coord_mem j q]
    exact (mem_branchFiber.mp hymem).2
  exact
    (hΓ.not_adj_other_branch_of_mem_branchFiber
      (coords.hub i) (coords.hub j) (coords.a_ne hij) hxmem)
      hyadj.symm

/-- A coordinate point is adjacent to its image under the transported matching
in the target A-side fiber. -/
theorem adj_coord_matchingEquiv
    (hΓ : IsMoore57 Γ) (coords : AFiberCoordinates Γ)
    {i j : ZMod 19} (hij : i ≠ j) (p : coords.P) :
    Γ.Adj
        (((coords.coord i) p :
          {x : V // x ∈ branchFiber Γ coords.u (coords.a i)}) : V)
        (((coords.coord j) (matchingEquiv hΓ coords i j hij p) :
          {x : V // x ∈ branchFiber Γ coords.u (coords.a j)}) : V) :=
  (adj_iff_matchingEquiv_eq hΓ coords hij p
    (matchingEquiv hΓ coords i j hij p)).2 rfl

end AFiberCoordinates

end Moore57
