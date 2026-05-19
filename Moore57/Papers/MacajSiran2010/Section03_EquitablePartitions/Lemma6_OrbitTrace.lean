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

/-- **Lemma 6 (3) (central ⇒ `Tr(O) ≤ 2`).** [deferred-heavy]

Paper-stub kept for backwards compatibility; see
`lem6_central_inducedTrace_le_two` for the proper-signature version. -/
theorem lem6_central_trace_le_two (hΓ : IsMoore57 Γ) : True := by trivial

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
The corner case `|O| = 1` is `lem6_inducedTrace_sq_lt_card_of_card_eq_one`. -/
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

end Moore57.Papers.MacajSiran2010.S3
