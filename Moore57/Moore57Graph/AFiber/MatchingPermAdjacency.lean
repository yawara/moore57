import Moore57.Moore57Graph.AFiber.MatchingPerm

/-!
# All-index adjacency criterion for A-fiber matching coordinates

This file adds the same-fiber non-adjacency case to
`AFiberCoordinates.adj_iff_matchingEquiv_eq`, giving a criterion that does not
require the caller to first split on the coordinate indices.
-/

namespace Moore57

namespace AFiberCoordinates

variable {V : Type*} [Fintype V] [DecidableEq V]
    {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- Two coordinate representatives in the same A-side fiber are not adjacent. -/
theorem not_adj_same_coord
    (hΓ : IsMoore57 Γ) (coords : AFiberCoordinates Γ)
    (i : ZMod 19) (p q : coords.P) :
    ¬ Γ.Adj
        (((coords.coord i) p :
          {x : V // x ∈ branchFiber Γ coords.u (coords.a i)}) : V)
        (((coords.coord i) q :
          {x : V // x ∈ branchFiber Γ coords.u (coords.a i)}) : V) := by
  intro hpq
  exact hΓ.no_triangle
    (mem_branchFiber.mp (coords.coord_mem i p)).2
    hpq
    (mem_branchFiber.mp (coords.coord_mem i q)).2.symm

/-- All-index coordinate adjacency criterion: two coordinate representatives
are adjacent iff their indices are distinct and the transported matching sends
the first coordinate to the second. -/
theorem adj_iff_exists_matchingEquiv_eq
    (hΓ : IsMoore57 Γ) (coords : AFiberCoordinates Γ)
    {i j : ZMod 19} (p q : coords.P) :
    Γ.Adj
        (((coords.coord i) p :
          {x : V // x ∈ branchFiber Γ coords.u (coords.a i)}) : V)
        (((coords.coord j) q :
          {x : V // x ∈ branchFiber Γ coords.u (coords.a j)}) : V) ↔
      ∃ hij : i ≠ j, matchingEquiv hΓ coords i j hij p = q := by
  constructor
  · intro hpq
    by_cases hij : i = j
    · subst j
      exact False.elim ((not_adj_same_coord hΓ coords i p q) hpq)
    · exact ⟨hij, (adj_iff_matchingEquiv_eq hΓ coords hij p q).1 hpq⟩
  · rintro ⟨hij, hpq⟩
    exact (adj_iff_matchingEquiv_eq hΓ coords hij p q).2 hpq

/-- A conjunction-shaped variant when a proof of distinct indices is already
available.  The explicit `hij` avoids hiding proof-dependent data in the
statement. -/
theorem adj_iff_ne_and_matchingEquiv_eq
    (hΓ : IsMoore57 Γ) (coords : AFiberCoordinates Γ)
    {i j : ZMod 19} (hij : i ≠ j) (p q : coords.P) :
    Γ.Adj
        (((coords.coord i) p :
          {x : V // x ∈ branchFiber Γ coords.u (coords.a i)}) : V)
        (((coords.coord j) q :
          {x : V // x ∈ branchFiber Γ coords.u (coords.a j)}) : V) ↔
      i ≠ j ∧ matchingEquiv hΓ coords i j hij p = q := by
  constructor
  · intro hpq
    exact ⟨hij, (adj_iff_matchingEquiv_eq hΓ coords hij p q).1 hpq⟩
  · intro hpq
    exact (adj_iff_matchingEquiv_eq hΓ coords hij p q).2 hpq.2

end AFiberCoordinates

end Moore57
