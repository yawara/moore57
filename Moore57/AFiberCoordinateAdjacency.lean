import Moore57.AFiberCoordinateConstruction

/-!
# Adjacency of constructed A-side fiber coordinates

For the coordinate system built from branch-fiber matchings, every non-base
coordinate is adjacent to the corresponding point in the base fiber.
-/

namespace Moore57

namespace AFiberCoordinates

variable {V : Type*} [Fintype V] [DecidableEq V]
    {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- In the coordinate system constructed from branch matchings, the base-fiber
point `p` is adjacent to its coordinate representative in every nonzero target
fiber. -/
theorem ofBranches_base_adj_coord
    (hΓ : IsMoore57 Γ) (u : V) (a : ZMod 19 → V)
    (hub : ∀ i : ZMod 19, Γ.Adj u (a i)) (hinj : Function.Injective a)
    {i : ZMod 19} (hi : i ≠ 0)
    (p : (ofBranches hΓ u a hub hinj).P) :
    Γ.Adj
      (((ofBranches hΓ u a hub hinj).coord 0 p :
          {x : V // x ∈ branchFiber Γ u (a 0)}) : V)
      (((ofBranches hΓ u a hub hinj).coord i p :
          {x : V // x ∈ branchFiber Γ u (a i)}) : V) := by
  classical
  have hai : a 0 ≠ a i := by
    intro h
    exact hi (hinj h.symm)
  simpa [ofBranches, hi] using hΓ.branchFiberMate_adj (hub 0) (hub i) hai p

end AFiberCoordinates

end Moore57
