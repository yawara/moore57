import Moore57.Papers.MacajSiran2010.Section03_EquitablePartitions.Definition
import Moore57.Foundations.GraphTheory.InducedTrace
import Moore57.Moore57Graph.AdjMovedSet

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Mačaj–Širáň 2010, §3, Lemma 6

> Let `O` be an orbit of `X` and let `x ∈ X` contribute to `O` (i.e., for
> some `v ∈ O`, `vˣ ∼ v`). Then
>
> (1) `x⁻¹` contributes to `O`;
>
> (2) if `|X|` is odd, then `Tr(X)` is even;
>
> (3) if `x` is central in `X`, then `Tr(O) ≤ 2`;
>
> (4) `Tr(O)² < |O|`.

`Tr(O)` is the average degree of the subgraph induced by `O`.

Status:
* (1) **proven** — abstract counting argument (graph symmetry +
  orbit invariance).
* (2)–(4) [deferred-heavy] — require formalising `Tr(O)` and `Tr(X)`
  as concrete numerical quantities, plus pairing / centraliser arguments.
-/

open Moore57

namespace Moore57.Papers.MacajSiran2010.S3

variable {V : Type*} [Fintype V] [DecidableEq V]
  {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- **Lemma 6 (1) (inverse also contributes).**

If `x` is an automorphism of `Γ`, `O ⊆ V` is invariant under `x`
(i.e. `x · v ∈ O` for `v ∈ O`), and there exists `v ∈ O` with
`Γ.Adj v (x v)`, then there also exists `w ∈ O` with `Γ.Adj w (x⁻¹ w)`.

Proof: take `w := x v`. By orbit invariance, `w ∈ O`; and
`x⁻¹ w = v`. Since `Γ.Adj v (x v) ↔ Γ.Adj (x v) v` (graph symmetry),
we have `Γ.Adj w (x⁻¹ w)`. -/
theorem lem6_inverse_contributes
    (x : Equiv.Perm V) (O : Set V)
    (hO_inv : ∀ v ∈ O, x v ∈ O)
    (hcontrib : ∃ v ∈ O, Γ.Adj v (x v)) :
    ∃ w ∈ O, Γ.Adj w (x⁻¹ w) := by
  obtain ⟨v, hv, hadj⟩ := hcontrib
  refine ⟨x v, hO_inv v hv, ?_⟩
  -- Goal: Γ.Adj (x v) (x⁻¹ (x v)) = Γ.Adj (x v) v
  have hxinv : x⁻¹ (x v) = v := by simp
  rw [hxinv]
  exact hadj.symm

/-- **Lemma 6 (2) (odd `|X|` ⇒ `Σ_{x ∈ X} a₁(x)` even).**

Pairing argument: for `X` a subgroup of `Equiv.Perm V` with odd order,
the involution `x ↦ x⁻¹` is fixed-point-free except at `x = 1`
(odd-order groups have no order-2 elements: `orderOf x ∣ |X|` is
odd, so `orderOf x` is odd, hence `≠ 2`).  Each non-trivial pair
`{x, x⁻¹}` contributes `a₁(x) + a₁(x⁻¹) = 2 · a₁(x)` via
`adjacentMovedCount_inv`.  The fixed point `x = 1` contributes
`a₁(1) = 0`.

This is the paper's "Tr(X) even" claim with the equivalent ℕ-form
`Σ_{x ∈ X} a₁(x) is even` (since `|X| · Tr(X) = Σ a₁(x)` by Lem 9 (2)).

No Moore57 hypothesis is needed; this is a pure consequence of the
adjacency-symmetry pairing structure. -/
theorem lem6_trace_even_of_odd_order
    (X : Subgroup (Equiv.Perm V)) [Fintype X]
    (hX_odd : Odd (Fintype.card X)) :
    Even (∑ x : X, adjacentMovedCount Γ (x : Equiv.Perm V)) :=
  Moore57.sum_adjacentMovedCount_even_of_subgroup_odd_card X hX_odd

/-- **Lemma 6 (3) (central ⇒ `Tr(O) ≤ 2`).** [done]

Paper-faithful proper signature: if `O ⊆ adjMovedSet Γ x` (geometric
content of `x` being central + contributing to `O`), then `Tr(O) ≤ 2`.

Re-export of `lem6_central_inducedTrace_le_two`. -/
theorem lem6_central_trace_le_two
    (hΓ : IsMoore57 Γ) {x : Equiv.Perm V}
    (hx : ∀ a b : V, Γ.Adj a b ↔ Γ.Adj (x a) (x b))
    {O : Finset V} (hO_subset : O ⊆ Moore57.adjMovedSet Γ x)
    (hO_nonempty : O.Nonempty) :
    inducedTrace Γ O ≤ 2 :=
  Moore57.subset_adjMovedSet_inducedTrace_le_two hΓ hx hO_subset hO_nonempty

/-- **Lemma 6 (3) (proper signature: central element ⇒ `Tr(O) ≤ 2`).**

If `O ⊆ adjMovedSet Γ x` (every vertex of `O` is adjacency-moved by `x`),
then the induced trace of `O` is at most `2`.

In the paper context, this hypothesis comes from `x` being central
in the group `X` and contributing to the `X`-orbit `O`: by centrality
`x` commutes with all `y ∈ X`, so the contribution `v ~ x v` propagates
along the orbit `O = X · v` to give `w ~ x w` for every `w ∈ O`, i.e.,
`O ⊆ adjMovedSet Γ x`.  The bound `Tr(O) ≤ 2` then follows from the
Moore57 no-quadrangle argument (`μ = 1`, `λ = 0`).

See `Moore57.subset_adjMovedSet_inducedTrace_le_two`. -/
theorem lem6_central_inducedTrace_le_two
    (hΓ : IsMoore57 Γ) {x : Equiv.Perm V}
    (hx : ∀ a b : V, Γ.Adj a b ↔ Γ.Adj (x a) (x b))
    {O : Finset V} (hO_subset : O ⊆ Moore57.adjMovedSet Γ x)
    (hO_nonempty : O.Nonempty) :
    inducedTrace Γ O ≤ 2 :=
  Moore57.subset_adjMovedSet_inducedTrace_le_two hΓ hx hO_subset hO_nonempty

/-- **Lemma 6 (4) (`Tr(O)² < |O|`).** [deferred-heavy]

Paper-stub kept for backwards compatibility; the proper-signature
form for `|O| ≥ 64` is `lem6_inducedTrace_sq_lt_card_of_card_ge_64`.
The corner case `|O| = 1` is `lem6_inducedTrace_sq_lt_card_of_card_eq_one`.
The dispatcher `lem6_inducedTrace_sq_lt_card_dispatch` (below) handles all
currently-proven cases (`|O| ∈ {1, 2, 3, 4}` or `|O| ≥ 64`). -/
theorem lem6_trace_sq_lt_size (hΓ : IsMoore57 Γ) : True := by trivial

/-- **Singleton induced trace is zero.** [done]

For any simple graph `Γ` (loopless) and any vertex `v`,
`inducedTrace Γ {v} = 0`.  The induced subgraph on a singleton has
no edges (irreflexivity of `Γ.Adj`), so the degree sum is `0`. -/
theorem inducedTrace_singleton_eq_zero (v : V) :
    inducedTrace Γ ({v} : Finset V) = 0 := by
  unfold inducedTrace inducedDegreeSum
  rw [Finset.sum_singleton, Finset.filter_singleton]
  simp

/-- **Lemma 6 (4) corner case: `|O| = 1`.** [done]

For a singleton `O = {v}`, `(inducedTrace Γ O)² = 0 < 1 = |O|`. -/
theorem lem6_inducedTrace_sq_lt_card_of_card_eq_one
    {O : Finset V} (hO : O.card = 1) :
    (inducedTrace Γ O) ^ 2 < (O.card : ℚ) := by
  obtain ⟨v, hv⟩ := Finset.card_eq_one.mp hO
  subst hv
  rw [inducedTrace_singleton_eq_zero, Finset.card_singleton, Nat.cast_one]
  norm_num

/-- **Induced trace of a pair.** [done]

For two distinct vertices `v ≠ w`, `inducedTrace Γ {v, w}` equals `1`
if `v ~ w` and `0` otherwise.  This is the doubleton analogue of
`inducedTrace_singleton_eq_zero`. -/
theorem inducedTrace_pair_eq
    {v w : V} (hvw : v ≠ w) :
    inducedTrace Γ ({v, w} : Finset V) =
      if Γ.Adj v w then 1 else 0 := by
  classical
  unfold inducedTrace inducedDegreeSum
  rw [Finset.sum_pair hvw,
      Finset.card_insert_of_notMem (by simp [hvw]), Finset.card_singleton]
  by_cases h : Γ.Adj v w
  · -- Adj v w: each filter has card 1, total = 2, 2/2 = 1.
    have hv : (({v, w} : Finset V).filter (Γ.Adj v)).card = 1 := by
      rw [Finset.filter_insert, Finset.filter_singleton,
          if_neg (Γ.irrefl), if_pos h]
      rfl
    have hw : (({v, w} : Finset V).filter (Γ.Adj w)).card = 1 := by
      rw [Finset.filter_insert, Finset.filter_singleton,
          if_pos (Γ.symm h), if_neg (Γ.irrefl)]
      simp
    rw [hv, hw, if_pos h]
    norm_num
  · -- not Adj: each filter has card 0, total = 0, 0/2 = 0.
    have hv : (({v, w} : Finset V).filter (Γ.Adj v)).card = 0 := by
      rw [Finset.filter_insert, Finset.filter_singleton,
          if_neg (Γ.irrefl), if_neg h]
      rfl
    have hw : (({v, w} : Finset V).filter (Γ.Adj w)).card = 0 := by
      rw [Finset.filter_insert, Finset.filter_singleton,
          if_neg (fun hh => h hh.symm), if_neg (Γ.irrefl)]
      rfl
    rw [hv, hw, if_neg h]
    norm_num

/-- **Lemma 6 (4) corner case: `|O| = 2`.** [done]

For a pair `O = {v, w}` (v ≠ w), `(inducedTrace Γ O)² ≤ 1 < 2 = |O|`. -/
theorem lem6_inducedTrace_sq_lt_card_of_card_eq_two
    {O : Finset V} (hO : O.card = 2) :
    (inducedTrace Γ O) ^ 2 < (O.card : ℚ) := by
  classical
  obtain ⟨v, w, hvw, rfl⟩ := Finset.card_eq_two.mp hO
  rw [inducedTrace_pair_eq hvw,
      Finset.card_insert_of_notMem (by simp [hvw]), Finset.card_singleton]
  by_cases h : Γ.Adj v w
  · rw [if_pos h]; norm_num
  · rw [if_neg h]; norm_num

/-- **Lemma 6 (4) corner case: `|O| = 3`.** [done]

For three distinct vertices `{a, b, c}`, the induced subgraph in
Moore57 has at most 2 edges (no triangle), so the induced degree
sum is at most 4, giving `Tr(O) ≤ 4/3` and `Tr(O)² ≤ 16/9 < 3`. -/
theorem lem6_inducedTrace_sq_lt_card_of_card_eq_three
    (hΓ : IsMoore57 Γ) {O : Finset V} (hO : O.card = 3) :
    (inducedTrace Γ O) ^ 2 < (O.card : ℚ) := by
  classical
  obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := Finset.card_eq_three.mp hO
  have hcard : ({a, b, c} : Finset V).card = 3 := by
    rw [Finset.card_insert_of_notMem (by simp [hab, hac]),
        Finset.card_insert_of_notMem (by simp [hbc]),
        Finset.card_singleton]
  -- Compute each filter card via Finset.card_filter.
  have hf : ∀ (x : V), (({a, b, c} : Finset V).filter (Γ.Adj x)).card =
        (if Γ.Adj x a then 1 else 0) +
        ((if Γ.Adj x b then 1 else 0) +
         (if Γ.Adj x c then 1 else 0)) := by
    intro x
    rw [Finset.card_filter,
        show ({a, b, c} : Finset V) = insert a (insert b {c}) from rfl,
        Finset.sum_insert (by simp [hab, hac]),
        Finset.sum_insert (by simp [hbc]),
        Finset.sum_singleton]
  -- inducedDegreeSum = (filter a) + (filter b) + (filter c)
  -- = [aa=0] + [ab] + [ac] + [ba] + [bb=0] + [bc] + [ca] + [cb] + [cc=0]
  -- = 2 ([ab] + [ac] + [bc])  by symmetry
  have h_sum_le : inducedDegreeSum Γ ({a, b, c} : Finset V) ≤ 4 := by
    unfold inducedDegreeSum
    rw [show ({a, b, c} : Finset V) = insert a (insert b {c}) from rfl]
    rw [Finset.sum_insert (by simp [hab, hac])]
    rw [Finset.sum_insert (by simp [hbc])]
    rw [Finset.sum_singleton]
    rw [show ({a, b, c} : Finset V) = insert a (insert b {c}) from rfl] at hf
    rw [hf a, hf b, hf c]
    have e_aa : (if Γ.Adj a a then (1 : ℕ) else 0) = 0 := if_neg (Γ.irrefl)
    have e_bb : (if Γ.Adj b b then (1 : ℕ) else 0) = 0 := if_neg (Γ.irrefl)
    have e_cc : (if Γ.Adj c c then (1 : ℕ) else 0) = 0 := if_neg (Γ.irrefl)
    have e_ba : (if Γ.Adj b a then (1 : ℕ) else 0) =
        (if Γ.Adj a b then (1 : ℕ) else 0) := by
      by_cases h : Γ.Adj a b
      · rw [if_pos h, if_pos h.symm]
      · rw [if_neg h, if_neg (fun hh => h hh.symm)]
    have e_ca : (if Γ.Adj c a then (1 : ℕ) else 0) =
        (if Γ.Adj a c then (1 : ℕ) else 0) := by
      by_cases h : Γ.Adj a c
      · rw [if_pos h, if_pos h.symm]
      · rw [if_neg h, if_neg (fun hh => h hh.symm)]
    have e_cb : (if Γ.Adj c b then (1 : ℕ) else 0) =
        (if Γ.Adj b c then (1 : ℕ) else 0) := by
      by_cases h : Γ.Adj b c
      · rw [if_pos h, if_pos h.symm]
      · rw [if_neg h, if_neg (fun hh => h hh.symm)]
    rw [e_aa, e_bb, e_cc, e_ba, e_ca, e_cb]
    -- Goal: now 2·([ab] + [ac] + [bc]) ≤ 4
    -- By no-triangle, NOT (Adj a b ∧ Adj a c ∧ Adj b c)
    have h_no_3 : ¬ (Γ.Adj a b ∧ Γ.Adj a c ∧ Γ.Adj b c) := fun ⟨h1, h2, h3⟩ =>
      hΓ.no_triangle h1 h3 h2.symm
    by_cases h1 : Γ.Adj a b <;>
    by_cases h2 : Γ.Adj a c <;>
    by_cases h3 : Γ.Adj b c <;>
    simp_all
  -- Now derive Tr² < 3 from inducedDegreeSum ≤ 4.
  have h_sum_nn : 0 ≤ (inducedDegreeSum Γ ({a, b, c} : Finset V) : ℚ) :=
    Nat.cast_nonneg _
  have h_sum_q : (inducedDegreeSum Γ ({a, b, c} : Finset V) : ℚ) ≤ 4 := by
    exact_mod_cast h_sum_le
  rw [show (({a, b, c} : Finset V).card : ℚ) = 3 by rw [hcard]; norm_num]
  unfold inducedTrace
  rw [show (({a, b, c} : Finset V).card : ℚ) = 3 by rw [hcard]; norm_num]
  set s := (inducedDegreeSum Γ ({a, b, c} : Finset V) : ℚ)
  -- Goal: (s / 3)² < 3. With 0 ≤ s ≤ 4: s² ≤ 16 < 27, so (s/3)² = s²/9 ≤ 16/9 < 3.
  nlinarith [sq_nonneg s, sq_nonneg (s - 4), h_sum_nn, h_sum_q]

/-- **Lemma 6 (4) corner case: `|O| = 4`.** [done]

For four distinct vertices `{a, b, c, d}`, the induced subgraph in
Moore57 has at most 3 edges (no triangle + no 4-cycle ⟹ induced
subgraph on 4 vertices is a forest, hence ≤ 3 edges), so the induced
degree sum is at most 6, giving `Tr(O) ≤ 6/4 = 3/2` and
`Tr(O)² ≤ 9/4 < 4`. -/
theorem lem6_inducedTrace_sq_lt_card_of_card_eq_four
    (hΓ : IsMoore57 Γ) {O : Finset V} (hO : O.card = 4) :
    (inducedTrace Γ O) ^ 2 < (O.card : ℚ) := by
  classical
  obtain ⟨a, b, c, d, hab, hac, had, hbc, hbd, hcd, rfl⟩ :=
    Finset.card_eq_four.mp hO
  have hcard : ({a, b, c, d} : Finset V).card = 4 := by
    rw [Finset.card_insert_of_notMem (by simp [hab, hac, had]),
        Finset.card_insert_of_notMem (by simp [hbc, hbd]),
        Finset.card_insert_of_notMem (by simp [hcd]),
        Finset.card_singleton]
  -- Compute each filter card via Finset.card_filter.
  have hf : ∀ (x : V), (({a, b, c, d} : Finset V).filter (Γ.Adj x)).card =
        (if Γ.Adj x a then 1 else 0) +
        ((if Γ.Adj x b then 1 else 0) +
         ((if Γ.Adj x c then 1 else 0) +
          (if Γ.Adj x d then 1 else 0))) := by
    intro x
    rw [Finset.card_filter,
        show ({a, b, c, d} : Finset V) = insert a (insert b (insert c {d})) from rfl,
        Finset.sum_insert (by simp [hab, hac, had]),
        Finset.sum_insert (by simp [hbc, hbd]),
        Finset.sum_insert (by simp [hcd]),
        Finset.sum_singleton]
  -- Set up the no-triangle and no-4-cycle constraints
  have h_no_3_abc : ¬ (Γ.Adj a b ∧ Γ.Adj a c ∧ Γ.Adj b c) :=
    fun ⟨h1, h2, h3⟩ => hΓ.no_triangle h1 h3 h2.symm
  have h_no_3_abd : ¬ (Γ.Adj a b ∧ Γ.Adj a d ∧ Γ.Adj b d) :=
    fun ⟨h1, h2, h3⟩ => hΓ.no_triangle h1 h3 h2.symm
  have h_no_3_acd : ¬ (Γ.Adj a c ∧ Γ.Adj a d ∧ Γ.Adj c d) :=
    fun ⟨h1, h2, h3⟩ => hΓ.no_triangle h1 h3 h2.symm
  have h_no_3_bcd : ¬ (Γ.Adj b c ∧ Γ.Adj b d ∧ Γ.Adj c d) :=
    fun ⟨h1, h2, h3⟩ => hΓ.no_triangle h1 h3 h2.symm
  have h_no_C4_1 : ¬ (Γ.Adj a b ∧ Γ.Adj b c ∧ Γ.Adj c d ∧ Γ.Adj a d) :=
    fun ⟨h1, h2, h3, h4⟩ =>
      hΓ.no_four_cycle hab hac had hbc hbd hcd h1 h2 h3 h4.symm
  have h_no_C4_2 : ¬ (Γ.Adj a b ∧ Γ.Adj b d ∧ Γ.Adj c d ∧ Γ.Adj a c) :=
    fun ⟨h1, h2, h3, h4⟩ =>
      hΓ.no_four_cycle hab had hac hbd hbc hcd.symm h1 h2 h3.symm h4.symm
  have h_no_C4_3 : ¬ (Γ.Adj a c ∧ Γ.Adj b c ∧ Γ.Adj b d ∧ Γ.Adj a d) :=
    fun ⟨h1, h2, h3, h4⟩ =>
      hΓ.no_four_cycle hac hab had hbc.symm hcd hbd h1 h2.symm h3 h4.symm
  -- inducedDegreeSum bound via case analysis on the 6 booleans
  have h_sum_le : inducedDegreeSum Γ ({a, b, c, d} : Finset V) ≤ 6 := by
    unfold inducedDegreeSum
    rw [show ({a, b, c, d} : Finset V) = insert a (insert b (insert c {d})) from rfl]
    rw [Finset.sum_insert (by simp [hab, hac, had])]
    rw [Finset.sum_insert (by simp [hbc, hbd])]
    rw [Finset.sum_insert (by simp [hcd])]
    rw [Finset.sum_singleton]
    rw [show ({a, b, c, d} : Finset V) = insert a (insert b (insert c {d})) from rfl] at hf
    rw [hf a, hf b, hf c, hf d]
    -- Reflexivity cases = 0
    have e_aa : (if Γ.Adj a a then (1 : ℕ) else 0) = 0 := if_neg (Γ.irrefl)
    have e_bb : (if Γ.Adj b b then (1 : ℕ) else 0) = 0 := if_neg (Γ.irrefl)
    have e_cc : (if Γ.Adj c c then (1 : ℕ) else 0) = 0 := if_neg (Γ.irrefl)
    have e_dd : (if Γ.Adj d d then (1 : ℕ) else 0) = 0 := if_neg (Γ.irrefl)
    -- Symmetry of adjacency
    have e_ba : (if Γ.Adj b a then (1 : ℕ) else 0) =
        (if Γ.Adj a b then (1 : ℕ) else 0) := by
      by_cases h : Γ.Adj a b
      · rw [if_pos h, if_pos h.symm]
      · rw [if_neg h, if_neg (fun hh => h hh.symm)]
    have e_ca : (if Γ.Adj c a then (1 : ℕ) else 0) =
        (if Γ.Adj a c then (1 : ℕ) else 0) := by
      by_cases h : Γ.Adj a c
      · rw [if_pos h, if_pos h.symm]
      · rw [if_neg h, if_neg (fun hh => h hh.symm)]
    have e_cb : (if Γ.Adj c b then (1 : ℕ) else 0) =
        (if Γ.Adj b c then (1 : ℕ) else 0) := by
      by_cases h : Γ.Adj b c
      · rw [if_pos h, if_pos h.symm]
      · rw [if_neg h, if_neg (fun hh => h hh.symm)]
    have e_da : (if Γ.Adj d a then (1 : ℕ) else 0) =
        (if Γ.Adj a d then (1 : ℕ) else 0) := by
      by_cases h : Γ.Adj a d
      · rw [if_pos h, if_pos h.symm]
      · rw [if_neg h, if_neg (fun hh => h hh.symm)]
    have e_db : (if Γ.Adj d b then (1 : ℕ) else 0) =
        (if Γ.Adj b d then (1 : ℕ) else 0) := by
      by_cases h : Γ.Adj b d
      · rw [if_pos h, if_pos h.symm]
      · rw [if_neg h, if_neg (fun hh => h hh.symm)]
    have e_dc : (if Γ.Adj d c then (1 : ℕ) else 0) =
        (if Γ.Adj c d then (1 : ℕ) else 0) := by
      by_cases h : Γ.Adj c d
      · rw [if_pos h, if_pos h.symm]
      · rw [if_neg h, if_neg (fun hh => h hh.symm)]
    rw [e_aa, e_bb, e_cc, e_dd, e_ba, e_ca, e_cb, e_da, e_db, e_dc]
    -- Goal: now 2·([ab] + [ac] + [ad] + [bc] + [bd] + [cd]) ≤ 6
    by_cases h1 : Γ.Adj a b <;>
    by_cases h2 : Γ.Adj a c <;>
    by_cases h3 : Γ.Adj a d <;>
    by_cases h4 : Γ.Adj b c <;>
    by_cases h5 : Γ.Adj b d <;>
    by_cases h6 : Γ.Adj c d <;>
    simp_all
  -- Convert to Tr bound
  have h_sum_nn : 0 ≤ (inducedDegreeSum Γ ({a, b, c, d} : Finset V) : ℚ) :=
    Nat.cast_nonneg _
  have h_sum_q : (inducedDegreeSum Γ ({a, b, c, d} : Finset V) : ℚ) ≤ 6 := by
    exact_mod_cast h_sum_le
  rw [show (({a, b, c, d} : Finset V).card : ℚ) = 4 by rw [hcard]; norm_num]
  unfold inducedTrace
  rw [show (({a, b, c, d} : Finset V).card : ℚ) = 4 by rw [hcard]; norm_num]
  set s := (inducedDegreeSum Γ ({a, b, c, d} : Finset V) : ℚ)
  -- Goal: (s / 4)² < 4. With 0 ≤ s ≤ 6: (s/4)² ≤ 36/16 = 9/4 < 4.
  nlinarith [sq_nonneg s, sq_nonneg (s - 6), h_sum_nn, h_sum_q]

/-- **Lemma 6 (4) (proper signature: `Tr(O)² < |O|` for `|O| ≥ 64`).**

For any nonempty `O ⊆ V` of cardinality at least 64,
`(inducedTrace Γ O)² < |O|`.

This follows from the Mohar upper bound `Tr(O) ≤ 7 + |O|/65` (Lemma 10)
plus the algebraic fact `(7 + n/65)² < n` for `n ∈ [64, 3250]` (using
`|O| ≤ |V| = 3250` from Moore57).  For small orbits `|O| < 64`,
parity (`d·|O|` even from sum-of-degrees) and the no-triangle /
no-quadrangle structural constraints of Moore57 are needed; these
are left as `[deferred-heavy]` since they require case analysis.

See `Moore57.inducedTrace_sq_lt_card_of_card_ge_64`. -/
theorem lem6_inducedTrace_sq_lt_card_of_card_ge_64
    (hΓ : IsMoore57 Γ) {O : Finset V}
    (hO_nonempty : O.Nonempty) (hO_large : 64 ≤ O.card) :
    (inducedTrace Γ O) ^ 2 < (O.card : ℚ) :=
  Moore57.inducedTrace_sq_lt_card_of_card_ge_64 hΓ hO_nonempty hO_large

/-- **Lemma 6 (4) (dispatcher: `Tr(O)² < |O|` for known cases).** [done]

Paper-faithful proper-signature dispatcher: combines the four corner
cases (`|O| ∈ {1, 2, 3, 4}`) and the Mohar bound `|O| ≥ 64` into one
proper-signature wrapper.  Small orbits `5 ≤ |O| ≤ 63` are deferred. -/
theorem lem6_inducedTrace_sq_lt_card_dispatch
    (hΓ : IsMoore57 Γ) {O : Finset V}
    (hO_size : O.card = 1 ∨ O.card = 2 ∨ O.card = 3 ∨
               O.card = 4 ∨ 64 ≤ O.card)
    (hO_nonempty : O.Nonempty) :
    (inducedTrace Γ O) ^ 2 < (O.card : ℚ) := by
  rcases hO_size with h1 | h2 | h3 | h4 | hge
  · exact lem6_inducedTrace_sq_lt_card_of_card_eq_one (Γ := Γ) h1
  · exact lem6_inducedTrace_sq_lt_card_of_card_eq_two (Γ := Γ) h2
  · exact lem6_inducedTrace_sq_lt_card_of_card_eq_three hΓ h3
  · exact lem6_inducedTrace_sq_lt_card_of_card_eq_four hΓ h4
  · exact lem6_inducedTrace_sq_lt_card_of_card_ge_64 hΓ hO_nonempty hge

end Moore57.Papers.MacajSiran2010.S3
