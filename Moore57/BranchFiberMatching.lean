import Moore57.D19Contradiction

open Finset SimpleGraph

namespace Moore57

namespace IsMoore57

variable {V : Type*} [Fintype V] [DecidableEq V]
    {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- The unique vertex in the branch fiber over `c` adjacent to `x`.

This packages the Section 2 perfect matching between two distinct branch fibers
as a function on subtypes. -/
noncomputable def branchFiberMate (hΓ : IsMoore57 Γ) {u b c : V}
    (hub : Γ.Adj u b) (huc : Γ.Adj u c) (hbc : b ≠ c)
    (x : {x // x ∈ branchFiber Γ u b}) :
    {y // y ∈ branchFiber Γ u c} :=
  let y := Classical.choose
    (hΓ.existsUnique_adjacent_in_branchFiber hub huc hbc x.property)
  ⟨y, (Classical.choose_spec
    (hΓ.existsUnique_adjacent_in_branchFiber hub huc hbc x.property)).1.1⟩

/-- The mate lies in the target branch fiber and is adjacent to the source point. -/
theorem branchFiberMate_spec (hΓ : IsMoore57 Γ) {u b c : V}
    (hub : Γ.Adj u b) (huc : Γ.Adj u c) (hbc : b ≠ c)
    (x : {x // x ∈ branchFiber Γ u b}) :
    (hΓ.branchFiberMate hub huc hbc x : V) ∈ branchFiber Γ u c ∧
      Γ.Adj (x : V) (hΓ.branchFiberMate hub huc hbc x : V) := by
  classical
  exact Classical.choose_spec
    (hΓ.existsUnique_adjacent_in_branchFiber hub huc hbc x.property) |>.1

/-- The defining adjacency property of `branchFiberMate`. -/
theorem branchFiberMate_adj (hΓ : IsMoore57 Γ) {u b c : V}
    (hub : Γ.Adj u b) (huc : Γ.Adj u c) (hbc : b ≠ c)
    (x : {x // x ∈ branchFiber Γ u b}) :
    Γ.Adj (x : V) (hΓ.branchFiberMate hub huc hbc x : V) :=
  (hΓ.branchFiberMate_spec hub huc hbc x).2

/-- Any target-fiber vertex adjacent to `x` is the mate of `x`. -/
theorem branchFiberMate_eq_of_adj (hΓ : IsMoore57 Γ) {u b c : V}
    (hub : Γ.Adj u b) (huc : Γ.Adj u c) (hbc : b ≠ c)
    (x : {x // x ∈ branchFiber Γ u b}) (y : {y // y ∈ branchFiber Γ u c})
    (hxy : Γ.Adj (x : V) (y : V)) :
    hΓ.branchFiberMate hub huc hbc x = y := by
  classical
  apply Subtype.ext
  have huniq :=
    (Classical.choose_spec
      (hΓ.existsUnique_adjacent_in_branchFiber hub huc hbc x.property)).2
  exact (huniq y ⟨y.property, hxy⟩).symm

/-- The perfect matching between two distinct branch fibers, packaged as an equivalence. -/
noncomputable def branchFiberMatchingEquiv (hΓ : IsMoore57 Γ) {u b c : V}
    (hub : Γ.Adj u b) (huc : Γ.Adj u c) (hbc : b ≠ c) :
    {x // x ∈ branchFiber Γ u b} ≃ {y // y ∈ branchFiber Γ u c} where
  toFun := hΓ.branchFiberMate hub huc hbc
  invFun := hΓ.branchFiberMate huc hub hbc.symm
  left_inv := by
    intro x
    apply hΓ.branchFiberMate_eq_of_adj huc hub hbc.symm
    exact (hΓ.branchFiberMate_adj hub huc hbc x).symm
  right_inv := by
    intro y
    apply hΓ.branchFiberMate_eq_of_adj hub huc hbc
    exact (hΓ.branchFiberMate_adj huc hub hbc.symm y).symm

end IsMoore57

end Moore57
