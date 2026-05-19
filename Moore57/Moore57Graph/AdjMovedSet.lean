import Moore57.Moore57Graph.E7Matrix.MoharBound
import Moore57.Moore57Graph.Moore57Definition
import Mathlib.Tactic.Linarith

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Adjacency-moved set of an automorphism of a Moore57 graph

For an automorphism `x` of a Moore57 graph `Γ`, the *adjacency-moved set*
`S = {v ∈ V(Γ) : v ~ x v}` satisfies the trace bound
`inducedTrace Γ S ≤ 2`.

The key step (Mačaj–Širáň 2010, proof of Corollary 1) uses the
no-quadrangle property of Moore57 (combined `λ = 0`, `μ = 1` argument):
for `v, w ∈ S` with `v ~ w`, the four vertices `v, x v, x w, w` form a
4-cycle (using automorphism preservation), and hence cannot be all
distinct.  Identifying the collapse forces `w = x v` or `w = x⁻¹ v`.

Combining with the Mohar lower bound `-8 + |S|/50 ≤ Tr(S)` from
`MoharBound.lean` gives the classical corollary
`a₁(x) = |S| ≤ 500`.
-/

namespace Moore57

variable {V : Type*} [Fintype V] [DecidableEq V]
  {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- The adjacency-moved set `{v ∈ V : v ~ x v}` for a permutation `x`. -/
def adjMovedSet (Γ : SimpleGraph V) [DecidableRel Γ.Adj]
    (x : Equiv.Perm V) : Finset V :=
  (Finset.univ : Finset V).filter (fun v => Γ.Adj v (x v))

@[simp] theorem mem_adjMovedSet {x : Equiv.Perm V} {v : V} :
    v ∈ adjMovedSet Γ x ↔ Γ.Adj v (x v) := by
  unfold adjMovedSet; simp

/-- `|adjMovedSet Γ x| = adjacentMovedCount Γ x`. -/
theorem adjMovedSet_card (x : Equiv.Perm V) :
    (adjMovedSet Γ x).card = adjacentMovedCount Γ x := rfl

/-- **Key no-quadrangle step.**

For `v, w` in the adjacency-moved set of an automorphism `x` of a Moore57
graph, `v ~ w` forces `w ∈ {x v, x⁻¹ v}`.

Argument: from `v ~ x v`, `w ~ x w`, `v ~ w` (given) and `x v ~ x w`
(automorphism), the four vertices `v, x v, x w, w` would form a
4-cycle if they were distinct, contradicting `μ = 1`. The collapse
identifies `w = x v` or `x w = v` (i.e., `w = x⁻¹ v`). -/
theorem neighbor_in_adjMovedSet_eq
    (hΓ : IsMoore57 Γ) {x : Equiv.Perm V}
    (hx : ∀ a b : V, Γ.Adj a b ↔ Γ.Adj (x a) (x b))
    {v w : V} (hv : v ∈ adjMovedSet Γ x) (hw : w ∈ adjMovedSet Γ x)
    (hvw : Γ.Adj v w) :
    w = x v ∨ w = x⁻¹ v := by
  rw [mem_adjMovedSet] at hv hw
  by_contra h
  push Not at h
  obtain ⟨h_w_ne_xv, h_w_ne_xinvv⟩ := h
  -- `x w ≠ v`: indeed `x w = v ⟹ w = x⁻¹ v` via `x⁻¹ (x w) = w`.
  have h_xw_ne_v : x w ≠ v := by
    intro h_eq
    apply h_w_ne_xinvv
    rw [← h_eq]; simp
  -- Automorphism: `v ~ w ⟹ x v ~ x w`.
  have h_xv_xw : Γ.Adj (x v) (x w) := (hx v w).mp hvw
  -- Distinctness of `v, x v, x w, w`.
  have h_v_ne_xv : v ≠ x v := hv.ne
  have h_v_ne_w : v ≠ w := hvw.ne
  have h_w_ne_xw : w ≠ x w := hw.ne
  have h_xv_ne_xw : x v ≠ x w := fun h_eq => h_v_ne_w (x.injective h_eq)
  -- Apply `no_four_cycle` with `(x0, x1, x2, x3) = (v, x v, x w, w)`.
  exact hΓ.no_four_cycle h_v_ne_xv h_xw_ne_v.symm h_v_ne_w
        h_xv_ne_xw h_w_ne_xv.symm h_w_ne_xw.symm
        hv h_xv_xw hw.symm hvw.symm

/-- The number of in-`adjMovedSet` neighbors of any `v` is at most 2,
since they all lie in `{x v, x⁻¹ v}`. -/
theorem adjMovedSet_filter_card_le_two
    (hΓ : IsMoore57 Γ) {x : Equiv.Perm V}
    (hx : ∀ a b : V, Γ.Adj a b ↔ Γ.Adj (x a) (x b))
    {v : V} (hv : v ∈ adjMovedSet Γ x) :
    ((adjMovedSet Γ x).filter (fun w => Γ.Adj v w)).card ≤ 2 := by
  classical
  have h_subset : (adjMovedSet Γ x).filter (fun w => Γ.Adj v w) ⊆
      ({x v, x⁻¹ v} : Finset V) := by
    intro w hw
    rw [Finset.mem_filter] at hw
    rcases neighbor_in_adjMovedSet_eq hΓ hx hv hw.1 hw.2 with h1 | h2
    · rw [h1]; simp
    · rw [h2]; simp
  refine (Finset.card_le_card h_subset).trans ?_
  -- `|{x v, x⁻¹ v}| ≤ 2`.
  have hins : ({x v, x⁻¹ v} : Finset V).card ≤
      ({x⁻¹ v} : Finset V).card + 1 := Finset.card_insert_le _ _
  simpa using hins

/-- `inducedDegreeSum Γ (adjMovedSet Γ x) ≤ 2 · |S|`. -/
theorem adjMovedSet_inducedDegreeSum_le
    (hΓ : IsMoore57 Γ) {x : Equiv.Perm V}
    (hx : ∀ a b : V, Γ.Adj a b ↔ Γ.Adj (x a) (x b)) :
    inducedDegreeSum Γ (adjMovedSet Γ x) ≤ 2 * (adjMovedSet Γ x).card := by
  unfold inducedDegreeSum
  calc ∑ v ∈ adjMovedSet Γ x,
          ((adjMovedSet Γ x).filter (fun w => Γ.Adj v w)).card
      ≤ ∑ _v ∈ adjMovedSet Γ x, 2 := by
        apply Finset.sum_le_sum
        intro v hv
        exact adjMovedSet_filter_card_le_two hΓ hx hv
    _ = 2 * (adjMovedSet Γ x).card := by
        rw [Finset.sum_const, smul_eq_mul, Nat.mul_comm]

/-- **`Tr(S) ≤ 2`** for the adjacency-moved set of an automorphism
of a Moore57 graph. -/
theorem adjMovedSet_inducedTrace_le_two
    (hΓ : IsMoore57 Γ) {x : Equiv.Perm V}
    (hx : ∀ a b : V, Γ.Adj a b ↔ Γ.Adj (x a) (x b))
    (hS : (adjMovedSet Γ x).Nonempty) :
    inducedTrace Γ (adjMovedSet Γ x) ≤ 2 := by
  unfold inducedTrace
  have h_card_pos : (0 : ℚ) < ((adjMovedSet Γ x).card : ℚ) := by
    exact_mod_cast Finset.card_pos.mpr hS
  rw [div_le_iff₀ h_card_pos]
  have h_nat := adjMovedSet_inducedDegreeSum_le hΓ hx
  have h_rat : (inducedDegreeSum Γ (adjMovedSet Γ x) : ℚ) ≤
      2 * ((adjMovedSet Γ x).card : ℚ) := by exact_mod_cast h_nat
  linarith

/-- **Generalisation of `Tr(S) ≤ 2`** to any subset of the adjacency-moved
set.

For `O ⊆ adjMovedSet Γ x`, the induced trace `Tr(Γ[O]) ≤ 2`.  The argument
is the same no-quadrangle bound: each `v ∈ O ⊆ S` has at most 2 in-`S`
neighbors, and in-`O` neighbors form a subset, hence at most 2.

This generalisation is used for Mačaj–Širáň §3 Lemma 6 (3) (central
element ⇒ `Tr(O) ≤ 2`), where `O` is an `X`-orbit contained in the
adjacency-moved set of a central element `x ∈ X`. -/
theorem subset_adjMovedSet_inducedTrace_le_two
    (hΓ : IsMoore57 Γ) {x : Equiv.Perm V}
    (hx : ∀ a b : V, Γ.Adj a b ↔ Γ.Adj (x a) (x b))
    {O : Finset V} (hO_subset : O ⊆ adjMovedSet Γ x)
    (hO_nonempty : O.Nonempty) :
    inducedTrace Γ O ≤ 2 := by
  classical
  unfold inducedTrace
  have h_card_pos : (0 : ℚ) < (O.card : ℚ) := by
    exact_mod_cast Finset.card_pos.mpr hO_nonempty
  rw [div_le_iff₀ h_card_pos]
  -- Show `inducedDegreeSum Γ O ≤ 2 * |O|` in ℕ.
  have h_nat : inducedDegreeSum Γ O ≤ 2 * O.card := by
    unfold inducedDegreeSum
    calc ∑ v ∈ O, (O.filter (fun w => Γ.Adj v w)).card
        ≤ ∑ _v ∈ O, 2 := by
          apply Finset.sum_le_sum
          intro v hv
          calc (O.filter (fun w => Γ.Adj v w)).card
              ≤ ((adjMovedSet Γ x).filter (fun w => Γ.Adj v w)).card := by
                apply Finset.card_le_card
                intro w hw
                rw [Finset.mem_filter] at hw ⊢
                exact ⟨hO_subset hw.1, hw.2⟩
            _ ≤ 2 := adjMovedSet_filter_card_le_two hΓ hx (hO_subset hv)
      _ = 2 * O.card := by rw [Finset.sum_const, smul_eq_mul, Nat.mul_comm]
  have h_rat : (inducedDegreeSum Γ O : ℚ) ≤ 2 * (O.card : ℚ) := by
    exact_mod_cast h_nat
  linarith

/-- **Mačaj–Širáň Corollary 1**: `a₁(x) ≤ 500` for every automorphism
`x` of a Moore57 graph.

Combines the Mohar lower bound `Tr(S) ≥ -8 + |S|/50` from
`mohar_trace_bounds` with the no-quadrangle bound `Tr(S) ≤ 2` from
`adjMovedSet_inducedTrace_le_two`, where `S = {v : v ~ x v}` has
cardinality `adjacentMovedCount Γ x`. -/
theorem adjacentMovedCount_le_500
    (hΓ : IsMoore57 Γ) {x : Equiv.Perm V}
    (hx : ∀ a b : V, Γ.Adj a b ↔ Γ.Adj (x a) (x b)) :
    adjacentMovedCount Γ x ≤ 500 := by
  by_cases hS : (adjMovedSet Γ x).Nonempty
  · -- Nonempty: Mohar lower + trace upper.
    have h_tr_le : inducedTrace Γ (adjMovedSet Γ x) ≤ 2 :=
      adjMovedSet_inducedTrace_le_two hΓ hx hS
    obtain ⟨h_lower, _⟩ := mohar_trace_bounds hΓ hS
    have h_combined : -8 + ((adjMovedSet Γ x).card : ℚ) / 50 ≤ 2 :=
      h_lower.trans h_tr_le
    have h_q : ((adjMovedSet Γ x).card : ℚ) ≤ 500 := by linarith
    have h_nat : (adjMovedSet Γ x).card ≤ 500 := by exact_mod_cast h_q
    rwa [adjMovedSet_card] at h_nat
  · -- Empty: a₁(x) = 0 ≤ 500.
    rw [Finset.not_nonempty_iff_eq_empty] at hS
    have hcard0 : adjacentMovedCount Γ x = 0 := by
      rw [← adjMovedSet_card, hS]; rfl
    omega

end Moore57
