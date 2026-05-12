import Moore57.Moore57Graph.AFiber.MatchingPermAdjacency

/-!
# Symmetry algebra for A-side fiber matching permutations

This file records inverse and fixed-equation rewrites for the coordinate
permutations coming from A-side fiber matchings.
-/

namespace Moore57

namespace AFiberCoordinates

variable {V : Type*} [Fintype V] [DecidableEq V]
    {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- Applying the matching from `j` back to `i` cancels the matching from `i`
to `j`. -/
@[simp] theorem matchingEquiv_swap_apply_apply
    (hΓ : IsMoore57 Γ) (coords : AFiberCoordinates Γ)
    {i j : ZMod 19} (hij : i ≠ j) (p : coords.P) :
    matchingEquiv hΓ coords j i hij.symm
        (matchingEquiv hΓ coords i j hij p) = p := by
  apply matchingEquiv_eq_of_adj hΓ coords hij.symm
  exact (adj_coord_matchingEquiv hΓ coords hij p).symm

/-- Applying the matching from `i` to `j` cancels the matching from `j` back
to `i`. -/
@[simp] theorem matchingEquiv_apply_swap_apply
    (hΓ : IsMoore57 Γ) (coords : AFiberCoordinates Γ)
    {i j : ZMod 19} (hij : i ≠ j) (p : coords.P) :
    matchingEquiv hΓ coords i j hij
        (matchingEquiv hΓ coords j i hij.symm p) = p := by
  simpa using matchingEquiv_swap_apply_apply
    (hΓ := hΓ) (coords := coords) (hij := hij.symm) p

/-- Reversing the indices gives the inverse coordinate matching. -/
theorem matchingEquiv_symm
    (hΓ : IsMoore57 Γ) (coords : AFiberCoordinates Γ)
    {i j : ZMod 19} (hij : i ≠ j) :
    (matchingEquiv hΓ coords i j hij).symm =
      matchingEquiv hΓ coords j i hij.symm := by
  ext p
  simpa using matchingEquiv_swap_apply_apply
    (hΓ := hΓ) (coords := coords) (hij := hij)
      ((matchingEquiv hΓ coords i j hij).symm p)

/-- Pointwise form of `matchingEquiv_symm`. -/
@[simp] theorem matchingEquiv_symm_apply
    (hΓ : IsMoore57 Γ) (coords : AFiberCoordinates Γ)
    {i j : ZMod 19} (hij : i ≠ j) (p : coords.P) :
    (matchingEquiv hΓ coords i j hij).symm p =
      matchingEquiv hΓ coords j i hij.symm p := by
  rw [matchingEquiv_symm]

/-- A swapped-index spelling of `matchingEquiv_symm`. -/
theorem matchingEquiv_swap_eq_symm
    (hΓ : IsMoore57 Γ) (coords : AFiberCoordinates Γ)
    {i j : ZMod 19} (hij : i ≠ j) :
    matchingEquiv hΓ coords j i hij.symm =
      (matchingEquiv hΓ coords i j hij).symm :=
  (matchingEquiv_symm hΓ coords hij).symm

/-- Move a matching equation across the inverse matching. -/
theorem matchingEquiv_eq_iff_eq_swap
    (hΓ : IsMoore57 Γ) (coords : AFiberCoordinates Γ)
    {i j : ZMod 19} (hij : i ≠ j) (p q : coords.P) :
    matchingEquiv hΓ coords i j hij p = q ↔
      p = matchingEquiv hΓ coords j i hij.symm q := by
  constructor
  · intro hpq
    rw [← hpq]
    exact (matchingEquiv_swap_apply_apply hΓ coords hij p).symm
  · intro hpq
    rw [hpq]
    exact matchingEquiv_apply_swap_apply hΓ coords hij q

/-- Move a matching equation across the inverse matching, with the equality
oriented toward the swapped matching. -/
theorem matchingEquiv_eq_iff_swap_eq
    (hΓ : IsMoore57 Γ) (coords : AFiberCoordinates Γ)
    {i j : ZMod 19} (hij : i ≠ j) (p q : coords.P) :
    matchingEquiv hΓ coords i j hij p = q ↔
      matchingEquiv hΓ coords j i hij.symm q = p := by
  rw [matchingEquiv_eq_iff_eq_swap]
  exact eq_comm

/-- A right-hand matching equation can be moved across the inverse matching. -/
theorem eq_matchingEquiv_iff_swap_eq
    (hΓ : IsMoore57 Γ) (coords : AFiberCoordinates Γ)
    {i j : ZMod 19} (hij : i ≠ j) (p q : coords.P) :
    q = matchingEquiv hΓ coords i j hij p ↔
      matchingEquiv hΓ coords j i hij.symm q = p := by
  rw [eq_comm, matchingEquiv_eq_iff_swap_eq]

/-- A right-hand matching equation can be moved across the inverse matching,
with the inverse equation oriented the other way. -/
theorem eq_matchingEquiv_iff_eq_swap
    (hΓ : IsMoore57 Γ) (coords : AFiberCoordinates Γ)
    {i j : ZMod 19} (hij : i ≠ j) (p q : coords.P) :
    q = matchingEquiv hΓ coords i j hij p ↔
      p = matchingEquiv hΓ coords j i hij.symm q := by
  rw [eq_comm, matchingEquiv_eq_iff_eq_swap]

/-- Rewrite `matchingEquiv p = σ p` as a fixed point of
`matchingEquiv.trans σ.symm`. -/
theorem matchingEquiv_eq_perm_apply_iff_trans_symm_fixed
    (hΓ : IsMoore57 Γ) (coords : AFiberCoordinates Γ)
    {i j : ZMod 19} (hij : i ≠ j)
    (σ : Equiv.Perm coords.P) (p : coords.P) :
    matchingEquiv hΓ coords i j hij p = σ p ↔
      ((matchingEquiv hΓ coords i j hij).trans σ.symm) p = p := by
  change matchingEquiv hΓ coords i j hij p = σ p ↔
    σ.symm (matchingEquiv hΓ coords i j hij p) = p
  exact (Equiv.symm_apply_eq σ).symm

/-- Rewrite `σ p = matchingEquiv p` as a fixed point of
`σ.trans (matchingEquiv).symm`. -/
theorem perm_apply_eq_matchingEquiv_iff_trans_symm_fixed
    (hΓ : IsMoore57 Γ) (coords : AFiberCoordinates Γ)
    {i j : ZMod 19} (hij : i ≠ j)
    (σ : Equiv.Perm coords.P) (p : coords.P) :
    σ p = matchingEquiv hΓ coords i j hij p ↔
      (σ.trans (matchingEquiv hΓ coords i j hij).symm) p = p := by
  change σ p = matchingEquiv hΓ coords i j hij p ↔
    (matchingEquiv hΓ coords i j hij).symm (σ p) = p
  exact (Equiv.symm_apply_eq (matchingEquiv hΓ coords i j hij)).symm

/-- Rewrite `matchingEquiv p = σ p` as a fixed point of
`σ` followed by the swapped matching. -/
theorem matchingEquiv_eq_perm_apply_iff_perm_trans_swap_fixed
    (hΓ : IsMoore57 Γ) (coords : AFiberCoordinates Γ)
    {i j : ZMod 19} (hij : i ≠ j)
    (σ : Equiv.Perm coords.P) (p : coords.P) :
    matchingEquiv hΓ coords i j hij p = σ p ↔
      (σ.trans (matchingEquiv hΓ coords j i hij.symm)) p = p := by
  rw [matchingEquiv_eq_iff_swap_eq]
  rfl

/-- The two natural fixed-point rewrites of `matchingEquiv p = σ p` agree. -/
theorem matchingEquiv_trans_symm_fixed_iff_perm_trans_swap_fixed
    (hΓ : IsMoore57 Γ) (coords : AFiberCoordinates Γ)
    {i j : ZMod 19} (hij : i ≠ j)
    (σ : Equiv.Perm coords.P) (p : coords.P) :
    ((matchingEquiv hΓ coords i j hij).trans σ.symm) p = p ↔
      (σ.trans (matchingEquiv hΓ coords j i hij.symm)) p = p := by
  rw [← matchingEquiv_eq_perm_apply_iff_trans_symm_fixed
      (hΓ := hΓ) (coords := coords) (hij := hij) (σ := σ) (p := p)]
  rw [← matchingEquiv_eq_perm_apply_iff_perm_trans_swap_fixed
      (hΓ := hΓ) (coords := coords) (hij := hij) (σ := σ) (p := p)]

end AFiberCoordinates

end Moore57
