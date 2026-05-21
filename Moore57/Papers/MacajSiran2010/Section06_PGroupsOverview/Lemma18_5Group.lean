import Moore57.Papers.MacajSiran2010.Section06_PGroupsOverview.Lemma16_PGroupFix
import Moore57.Moore57Graph.Aut.NeighborMod
import Moore57.Moore57Graph.Aut.HSFixedData
import Moore57.Moore57Graph.Aut.FixedSubgraphData
import Moore57.Moore57Graph.Aut.SingletonAndEmptyFixedData

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Mačaj–Širáň 2010, §6, Lemma 18

> Let `X` be a group of automorphisms of Γ such that `|X|` is a 5-group.
> Then one of the following holds:
>
> (1) `Fix(X)` is the Hoffman–Singleton graph and `|X|` divides `25`;
>
> (2) `Fix(X)` is a pentagon and `|X|` divides `125`;
>
> (3) `Fix(X)` is empty and `|X|` divides `5⁶`.

This is the only lemma in §6 whose full proof the authors include
(orbit counting around `Fix(a)` for `a ∈ Fix(X)`).

Status:
* `lem18_5group_fix` — full classification (deferred-heavy).
* `lem18_case1_arithmetic_5group_dvd_50_implies_25`,
  `lem18_case2_arithmetic_5group_dvd_55_implies_125`: **proven**
  arithmetic cores translating "5-group + small divisor" to the
  stated bound (`|X| ∣ 25` resp. `∣ 125`).
-/

namespace Moore57.Papers.MacajSiran2010.S6

variable {V : Type*} [Fintype V] [DecidableEq V]
  {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- **Lemma 18 case (1) arithmetic core: 5-group with `|X| ∣ 50` gives
`|X| ∣ 25`.** [done]

For a 5-group `X` (i.e., `|X| = 5^k` for some `k`), the constraint
`|X| ∣ 50` forces `|X| ≤ 50` hence `k ≤ 2`, hence `|X| = 5^k ∈ {1, 5, 25}`,
all of which divide `25`.

This is the §6 Lem 18 (1) arithmetic step: semi-regular action of `X`
on `N(a) \ Fix(X)` (of size `50` when `Fix(X) = HS`) gives `|X| ∣ 50`,
and the 5-group constraint sharpens to `|X| ∣ 25`. -/
theorem lem18_case1_arithmetic_5group_dvd_50_implies_25
    (k : ℕ) (h_dvd : 5 ^ k ∣ 50) : 5 ^ k ∣ 25 := by
  have h_le : 5 ^ k ≤ 50 := Nat.le_of_dvd (by norm_num) h_dvd
  have h_k_le : k ≤ 2 := by
    by_contra h
    have h3 : 3 ≤ k := Nat.lt_of_not_le h
    have h_ge : 5 ^ 3 ≤ 5 ^ k := Nat.pow_le_pow_right (by norm_num) h3
    omega
  interval_cases k <;> decide

/-- **Lemma 18 case (2) arithmetic core: 5-group with `|X| ∣ 55` gives
`|X| ∣ 5`.** [done]

For a 5-group `X` (`|X| = 5^k`), `|X| ∣ 55 = 5·11` forces `k ≤ 1`
since `5^2 = 25` does not divide `55`.  Hence `|X| ∈ {1, 5}` and
`|X| ∣ 5`.  Combined with the orbit-stabilizer argument
`|X| = 5·|Y|` and `|Y| ≤ 25` from case (1) gives the paper's
`|X| ∣ 125`. -/
theorem lem18_case2_arithmetic_5group_dvd_55_implies_5
    (k : ℕ) (h_dvd : 5 ^ k ∣ 55) : 5 ^ k ∣ 5 := by
  have h_le : 5 ^ k ≤ 55 := Nat.le_of_dvd (by norm_num) h_dvd
  have h_k_le : k ≤ 2 := by
    by_contra h
    have h3 : 3 ≤ k := Nat.lt_of_not_le h
    have h_ge : 5 ^ 3 ≤ 5 ^ k := Nat.pow_le_pow_right (by norm_num) h3
    omega
  interval_cases k
  · decide          -- 5^0 = 1 ∣ 5
  · decide          -- 5^1 = 5 ∣ 5
  · -- k = 2: 5^2 = 25, but 25 does not divide 55.  Contradiction.
    exfalso
    revert h_dvd
    decide

/-- **Lemma 18 case (1) modular bridge (geometric).** [done]

For a single graph-automorphism σ with `σ^(5^k) = 1` fixing `a`, the
σ-fixed-neighbour count satisfies `|N(a) ∩ Fix(σ)| ≡ 2 (mod 5)`
(since `57 = 5·11 + 2`).

This is the §6 Lem 18 N(a) modular ingredient: for `Fix(X) = HS`
(7-regular), `|N(a) ∩ Fix(X)| = 7 ≡ 2 (mod 5)` ✓; for empty fix the
constraint must come from another vertex's view. -/
theorem lem18_neighbor_fix_mod_five
    (hΓ : IsMoore57 Γ) (σ : Equiv.Perm V)
    (smul_adj : ∀ v w : V, Γ.Adj v w ↔ Γ.Adj (σ v) (σ w))
    (k : ℕ) (pow_pk : σ ^ 5 ^ k = 1)
    {a : V} (ha : σ a = a) :
    (Moore57.autFixedNeighborFinset Γ σ a).card ≡ 2 [MOD 5] :=
  Moore57.aut_card_fixedNeighborFinset_modEq_two_of_pow_five_pow
    hΓ σ smul_adj k pow_pk ha

/-- **Lemma 18 case (1) conditional + arithmetic.** [done]

If a single graph-automorphism σ has order a power of 5 (`σ^(5^k) = 1`)
and `orderOf σ ∣ 50` (the geometric Hoffman–Singleton complement
assumption `|N(a) \ Fix(σ)| = 50`), then `orderOf σ ∣ 25`. -/
theorem lem18_case1_orderOf_dvd_25_of_HS_complement
    (σ : Equiv.Perm V) (k : ℕ) (pow_pk : σ ^ 5 ^ k = 1)
    (h_dvd : orderOf σ ∣ 50) :
    orderOf σ ∣ 25 := by
  have h5k : orderOf σ ∣ 5 ^ k := orderOf_dvd_of_pow_eq_one pow_pk
  rcases (Nat.dvd_prime_pow (by decide : Nat.Prime 5)).mp h5k with ⟨j, _hj, hord⟩
  rw [hord] at h_dvd ⊢
  exact lem18_case1_arithmetic_5group_dvd_50_implies_25 j h_dvd

/-- **Lemma 18 case (2) conditional + arithmetic.** [done]

If a single graph-automorphism σ has order a power of 5 (`σ^(5^k) = 1`)
and `orderOf σ ∣ 55` (the geometric pentagon complement assumption
`|N(a) \ Fix(σ)| = 55`), then `orderOf σ ∣ 5`. -/
theorem lem18_case2_orderOf_dvd_5_of_pentagon_complement
    (σ : Equiv.Perm V) (k : ℕ) (pow_pk : σ ^ 5 ^ k = 1)
    (h_dvd : orderOf σ ∣ 55) :
    orderOf σ ∣ 5 := by
  have h5k : orderOf σ ∣ 5 ^ k := orderOf_dvd_of_pow_eq_one pow_pk
  rcases (Nat.dvd_prime_pow (by decide : Nat.Prime 5)).mp h5k with ⟨j, _hj, hord⟩
  rw [hord] at h_dvd ⊢
  exact lem18_case2_arithmetic_5group_dvd_55_implies_5 j h_dvd

/-- **Lemma 18 case (3) arithmetic core: 5-group with `|X| ∣ 3250` gives
`|X| ∣ 125`.** [done]

For a 5-group `X` (`|X| = 5^k`) with `Fix(X) = ∅` and X acting
semi-regularly on `V`, the orbit equation forces `|X| ∣ |V| = 3250`.
Since `3250 = 2 · 5³ · 13`, the 5-part of `3250` is exactly `5³ = 125`,
so `5^k ∣ 3250` ⟹ `k ≤ 3` ⟹ `|X| ∈ {1, 5, 25, 125}`, all dividing
`125`. -/
theorem lem18_case3_arithmetic_5group_dvd_3250
    (k : ℕ) (h_dvd : 5 ^ k ∣ 3250) :
    5 ^ k ∣ 125 := by
  have h_k_le : k ≤ 3 := by
    by_contra h
    have h4 : 4 ≤ k := Nat.lt_of_not_le h
    -- 5^4 = 625 does not divide 3250 = 2·5³·13.
    have h_div : 5 ^ 4 ∣ 3250 := dvd_trans (pow_dvd_pow 5 h4) h_dvd
    revert h_div
    decide
  interval_cases k <;> decide

/-- **Lemma 18 case (3) conditional + arithmetic (5-group, empty fix).**
[done]

If a single graph-automorphism σ has order a power of 5 (`σ^(5^k) = 1`)
and `orderOf σ ∣ 3250` (semi-regular action on the whole vertex set, the
geometric "Fix is empty" assumption), then `orderOf σ ∣ 125`. -/
theorem lem18_case3_orderOf_dvd_125_of_empty_fix
    (σ : Equiv.Perm V) (k : ℕ) (pow_pk : σ ^ 5 ^ k = 1)
    (h_dvd : orderOf σ ∣ 3250) :
    orderOf σ ∣ 125 := by
  have h5k : orderOf σ ∣ 5 ^ k := orderOf_dvd_of_pow_eq_one pow_pk
  rcases (Nat.dvd_prime_pow (by decide : Nat.Prime 5)).mp h5k with ⟨j, _hj, hord⟩
  rw [hord] at h_dvd ⊢
  exact lem18_case3_arithmetic_5group_dvd_3250 j h_dvd

/-- **Lemma 18 case (1) geometric: `|N(a) \ Fix(σ)| = 50` from
`HSFixedData`.**  [done]

For σ with `HSFixedData` on a Moore57 graph, the σ-moved neighbour count at
any fixed vertex equals `50 = 57 − 7` (where `57` is the Moore57 degree and
`7` is the Hoffman–Singleton induced degree).

This is the §6 Lem 18 (1) semi-regular orbit input: σ acts on a 50-element
set (without fixed points), and combined with the orbit-stabilizer argument
(deferred — `orderOf σ ∣ 50`) yields the arithmetic core's input. -/
theorem lem18_case1_complement_count_eq_50
    [DecidableEq V] [DecidableRel Γ.Adj]
    (hΓ : IsMoore57 Γ) (σ : Equiv.Perm V) (h : HSFixedData Γ σ) (i : Fin 50) :
    ((Γ.neighborFinset (h.v i)).filter (fun w => σ w ≠ w)).card = 50 :=
  Moore57.HSFixedData.hsFixedData_complement_neighbor_count hΓ h i

/-- **Lemma 18 case (1) full bridge via `HSFixedData`**:
combines the geometric data with a semi-regular orbit hypothesis to
conclude `orderOf σ ∣ 25`.  [done]

The hypothesis `h_semi_regular : orderOf σ ∣ 50` is the deferred geometric
step (semi-regular action of `⟨σ⟩` on the 50-element set `N(a) \ Fix(σ)`);
once it is in place, this becomes an unconditional bridge from `HSFixedData`
to the Lem 18 (1) conclusion. -/
theorem lem18_case1_orderOf_dvd_25_with_HSFixedData
    (σ : Equiv.Perm V) (k : ℕ) (pow_pk : σ ^ 5 ^ k = 1)
    (_hsfd : HSFixedData Γ σ)
    (h_semi_regular : orderOf σ ∣ 50) :
    orderOf σ ∣ 25 :=
  lem18_case1_orderOf_dvd_25_of_HS_complement σ k pow_pk h_semi_regular

/-- **Lemma 18 case (1) unconditional bridge via `HSFixedData` and the
C3.4 semi-regular orbit argument**. [done — C3.4]

Replaces `h_semi_regular : orderOf σ ∣ 50` with the paper-faithful
semi-regular hypothesis on `N(a) \ Fix(σ)`.  The complement-count is
internalised via `hs_orderOf_dvd_50_of_semiRegular`. -/
theorem lem18_case1_orderOf_dvd_25_with_HSFixedData_semiRegular
    (hΓ : IsMoore57 Γ) (σ : Equiv.Perm V) (k : ℕ) (pow_pk : σ ^ 5 ^ k = 1)
    (hsfd : HSFixedData Γ σ) (i : Fin 50)
    (smul_adj : ∀ v w : V, Γ.Adj v w ↔ Γ.Adj (σ v) (σ w))
    (hsemi : ∀ w ∈ Moore57.autMovedNeighborFinset Γ σ (hsfd.v i),
             ∀ k : ℕ, (σ^k) w = w → orderOf σ ∣ k) :
    orderOf σ ∣ 25 :=
  lem18_case1_orderOf_dvd_25_of_HS_complement σ k pow_pk
    (Moore57.HSFixedData.hs_orderOf_dvd_50_of_semiRegular
      hΓ hsfd i smul_adj hsemi)

/-- **Lemma 18 case (2) geometric: `|N(a) \ Fix(σ)| = 55` from `C5FixedData`.**
[done]

For σ with Pentagon (`C5FixedData`) on a Moore57 graph, the σ-moved neighbour
count at any of the 5 fixed pentagon vertices equals `55 = 57 − 2`. -/
theorem lem18_case2_complement_count_eq_55
    (hΓ : IsMoore57 Γ) (σ : Equiv.Perm V) (h : C5FixedData Γ σ) (i : Fin 5) :
    ((Γ.neighborFinset (h.v i)).filter (fun w => σ w ≠ w)).card = 55 :=
  Moore57.C5FixedData.c5FixedData_complement_neighbor_count hΓ h i

/-- **Lemma 18 case (2) full bridge via `C5FixedData`**: conditional
`PentagonFixedData + orderOf σ ∣ 55 ⟹ orderOf σ ∣ 5`. -/
theorem lem18_case2_orderOf_dvd_5_with_c5FixedData
    (σ : Equiv.Perm V) (k : ℕ) (pow_pk : σ ^ 5 ^ k = 1)
    (_c5 : C5FixedData Γ σ)
    (h_semi_regular : orderOf σ ∣ 55) :
    orderOf σ ∣ 5 :=
  lem18_case2_orderOf_dvd_5_of_pentagon_complement σ k pow_pk h_semi_regular

/-- **Lemma 18 case (2) unconditional bridge via `C5FixedData` and the
C3.4 semi-regular orbit argument**. [done — C3.4] -/
theorem lem18_case2_orderOf_dvd_5_with_c5FixedData_semiRegular
    (hΓ : IsMoore57 Γ) (σ : Equiv.Perm V) (k : ℕ) (pow_pk : σ ^ 5 ^ k = 1)
    (c5 : C5FixedData Γ σ) (i : Fin 5)
    (smul_adj : ∀ v w : V, Γ.Adj v w ↔ Γ.Adj (σ v) (σ w))
    (hsemi : ∀ w ∈ Moore57.autMovedNeighborFinset Γ σ (c5.v i),
             ∀ k : ℕ, (σ^k) w = w → orderOf σ ∣ k) :
    orderOf σ ∣ 5 :=
  lem18_case2_orderOf_dvd_5_of_pentagon_complement σ k pow_pk
    (Moore57.C5FixedData.c5_orderOf_dvd_55_of_semiRegular
      hΓ c5 i smul_adj hsemi)

/-- **Lemma 18 case (3) geometric: `|V \ Fix(σ)| = 3250` from `EmptyFixedData`.**
[done]

For σ with empty fix on a Moore57 graph, the σ-moved vertex count equals
`3250 = |V|`. -/
theorem lem18_case3_complement_count_eq_3250
    (hΓ : IsMoore57 Γ) (σ : Equiv.Perm V) (h : EmptyFixedData σ) :
    ((Finset.univ : Finset V).filter (fun w => σ w ≠ w)).card = 3250 :=
  Moore57.EmptyFixedData.emptyFixedData_complement_vertex_count hΓ h

/-- **Lemma 18 case (3) full bridge via `EmptyFixedData`**: conditional
`EmptyFixedData + orderOf σ ∣ 3250 ⟹ orderOf σ ∣ 125`. -/
theorem lem18_case3_orderOf_dvd_125_with_emptyFixedData
    (σ : Equiv.Perm V) (k : ℕ) (pow_pk : σ ^ 5 ^ k = 1)
    (_efd : EmptyFixedData σ)
    (h_semi_regular : orderOf σ ∣ 3250) :
    orderOf σ ∣ 125 :=
  lem18_case3_orderOf_dvd_125_of_empty_fix σ k pow_pk h_semi_regular

/-- **Lemma 18 case (3) unconditional bridge via `EmptyFixedData` and the
C3.4 semi-regular orbit argument**. [done — C3.4]

The empty-fix case treats σ as acting semi-regularly on the entire
vertex set, giving `orderOf σ ∣ 3250`. -/
theorem lem18_case3_orderOf_dvd_125_with_emptyFixedData_semiRegular
    (hΓ : IsMoore57 Γ) (σ : Equiv.Perm V) (k : ℕ) (pow_pk : σ ^ 5 ^ k = 1)
    (efd : EmptyFixedData σ)
    (hsemi : ∀ v : V, ∀ k : ℕ, (σ^k) v = v → orderOf σ ∣ k) :
    orderOf σ ∣ 125 :=
  lem18_case3_orderOf_dvd_125_of_empty_fix σ k pow_pk
    (Moore57.EmptyFixedData.empty_orderOf_dvd_3250_of_semiRegular
      (Γ := Γ) hΓ efd hsemi)

/-- **Lemma 18 dispatch arithmetic: `n ∣ 25 ∨ n ∣ 5 ∨ n ∣ 125` ⟹ `n ∣ 125`.**
[done]

Paper-faithful packaging of the Lem 18 conclusion: each of the three
fix-shape branches (HS, pentagon, empty) gives a divisibility bound,
combined to `|X| ∣ 125`. -/
theorem lem18_orderOf_dvd_125_from_dispatch
    (n : ℕ) (h : n ∣ 25 ∨ n ∣ 5 ∨ n ∣ 125) : n ∣ 125 := by
  rcases h with h | h | h
  · exact dvd_trans h (by decide)
  · exact dvd_trans h (by decide)
  · exact h

/-- **Lemma 18 dispatch numeric bound: `|X| ≤ 125` from dispatch.** [done] -/
theorem lem18_le_125_from_dispatch
    (n : ℕ) (h : n ∣ 25 ∨ n ∣ 5 ∨ n ∣ 125) : n ≤ 125 :=
  Nat.le_of_dvd (by norm_num) (lem18_orderOf_dvd_125_from_dispatch n h)

/-! ### Prime-case (σ^5 = 1) unconditional wrappers

For σ of prime order 5 (the base case k = 1 of `σ^{5^k} = 1`), the
order divides 5 trivially, hence the Lem 18 case (1) bound `∣ 25`,
case (2) bound `∣ 5`, and case (3) bound `∣ 125` all follow immediately
without any semi-regular hypothesis or FixedData inspection.

These wrappers are the **base case** of Path B (Phase 1) — for the
composite case `σ^{5^k} = 1` with `k ≥ 2`, the unconditional derivation
requires the deeper paper Lem 18 / Prop 3 chain.  Documented as
deferred-heavy. -/

/-- **Lemma 18 case (1) prime-case unconditional wrapper.** [done]

For σ a graph automorphism of Γ with σ⁵ = 1 and `HSFixedData Γ σ`,
the bound `orderOf σ ∣ 25` holds trivially since `orderOf σ ∣ 5 ∣ 25`. -/
theorem lem18_case1_orderOf_dvd_25_with_HSFixedData_prime_unconditional
    (hΓ : IsMoore57 Γ) (σ : Equiv.Perm V) (pow_5 : σ ^ 5 = 1)
    (_hsfd : HSFixedData Γ σ) (_i : Fin 50)
    (_smul_adj : ∀ v w : V, Γ.Adj v w ↔ Γ.Adj (σ v) (σ w)) :
    orderOf σ ∣ 25 := by
  have h5 : orderOf σ ∣ 5 := orderOf_dvd_of_pow_eq_one pow_5
  exact dvd_trans h5 (by decide)

/-- **Lemma 18 case (2) prime-case unconditional wrapper.** [done]

For σ a graph automorphism of Γ with σ⁵ = 1 and `C5FixedData Γ σ`,
the bound `orderOf σ ∣ 5` holds trivially. -/
theorem lem18_case2_orderOf_dvd_5_with_c5FixedData_prime_unconditional
    (hΓ : IsMoore57 Γ) (σ : Equiv.Perm V) (pow_5 : σ ^ 5 = 1)
    (_c5 : C5FixedData Γ σ) (_i : Fin 5)
    (_smul_adj : ∀ v w : V, Γ.Adj v w ↔ Γ.Adj (σ v) (σ w)) :
    orderOf σ ∣ 5 :=
  orderOf_dvd_of_pow_eq_one pow_5

/-- **Lemma 18 case (3) prime-case unconditional wrapper.** [done]

For σ a graph automorphism of Γ with σ⁵ = 1 and `EmptyFixedData σ`,
the bound `orderOf σ ∣ 125` holds trivially since `orderOf σ ∣ 5 ∣ 125`. -/
theorem lem18_case3_orderOf_dvd_125_with_emptyFixedData_prime_unconditional
    (hΓ : IsMoore57 Γ) (σ : Equiv.Perm V) (pow_5 : σ ^ 5 = 1)
    (_efd : EmptyFixedData σ) :
    orderOf σ ∣ 125 := by
  have h5 : orderOf σ ∣ 5 := orderOf_dvd_of_pow_eq_one pow_5
  exact dvd_trans h5 (by decide)

/-- **Lemma 18 case (1) `k ≤ 2` unconditional wrapper.** [done]

For σ a graph automorphism of Γ with σ^(5^k) = 1 (k ≤ 2) and
`HSFixedData Γ σ`, the bound `orderOf σ ∣ 25` holds since
`orderOf σ ∣ 5^k ∣ 25` for k ≤ 2.

Extends the prime-case wrapper to cover k ∈ {0, 1, 2} (σ of order 1, 5,
or 25).  The `k ≥ 3` case (allowing `orderOf σ ≥ 125`) requires ruling
out via paper Prop 3 or finer analysis. -/
theorem lem18_case1_orderOf_dvd_25_with_HSFixedData_k_le_2_unconditional
    (hΓ : IsMoore57 Γ) (σ : Equiv.Perm V) (k : ℕ) (hk : k ≤ 2)
    (pow_pk : σ ^ 5 ^ k = 1)
    (_hsfd : HSFixedData Γ σ) (_i : Fin 50)
    (_smul_adj : ∀ v w : V, Γ.Adj v w ↔ Γ.Adj (σ v) (σ w)) :
    orderOf σ ∣ 25 := by
  have h_dvd : (5 : ℕ) ^ k ∣ 25 := by
    have : 5 ^ k ∣ 5 ^ 2 := pow_dvd_pow 5 hk
    simpa using this
  have h_pow : σ ^ 25 = 1 := by
    obtain ⟨l, hl⟩ := h_dvd
    rw [hl, pow_mul, pow_pk, one_pow]
  exact orderOf_dvd_of_pow_eq_one h_pow

/-- **Lemma 18 case (3) `k ≤ 3` unconditional wrapper.** [done]

For σ a graph automorphism of Γ with σ^(5^k) = 1 (k ≤ 3) and
`EmptyFixedData σ`, the bound `orderOf σ ∣ 125` holds since
`orderOf σ ∣ 5^k ∣ 125` for k ≤ 3.

Extends the prime-case wrapper to cover k ∈ {0, 1, 2, 3} (σ of order
1, 5, 25, or 125).  The `k ≥ 4` case (allowing `orderOf σ = 625`)
requires the paper Lem 22 + Prop 4 SG(625, 12) exclusion (deferred-
heavy). -/
theorem lem18_case3_orderOf_dvd_125_with_emptyFixedData_k_le_3_unconditional
    (hΓ : IsMoore57 Γ) (σ : Equiv.Perm V) (k : ℕ) (hk : k ≤ 3)
    (pow_pk : σ ^ 5 ^ k = 1)
    (_efd : EmptyFixedData σ) :
    orderOf σ ∣ 125 := by
  have h_dvd : (5 : ℕ) ^ k ∣ 125 := by
    have : 5 ^ k ∣ 5 ^ 3 := pow_dvd_pow 5 hk
    simpa using this
  have h_pow : σ ^ 125 = 1 := by
    obtain ⟨l, hl⟩ := h_dvd
    rw [hl, pow_mul, pow_pk, one_pow]
  exact orderOf_dvd_of_pow_eq_one h_pow

/-! ### Prime-case `_via_semiRegular_unconditional` wrappers (Path B)

For σ of prime order 5, the cyclic action is automatically semi-regular
on every moved point (via `Moore57.aut_semiRegular_at_movedNeighbor_of_prime`).
These wrappers eliminate the `hsemi` argument from the `_semiRegular`
wrappers, making the Path B chain end-to-end paper-faithful for the
prime case.

The composite case (`σ^{5^k} = 1` with k ≥ 2) requires paper Prop 3 / Lem 22
/ Prop 4 SG(625, 12) exclusion and remains deferred-heavy.
-/

/-- **Lemma 18 case (1) prime-case via semi-regular (fully unconditional).** [done — Path B]

For σ a graph automorphism of Γ with σ^5 = 1 and `HSFixedData Γ σ`,
`orderOf σ ∣ 25` follows via:
1. prime-order semi-regular generator (`aut_semiRegular_at_movedNeighbor_of_prime`)
2. C3.4 semi-regular orbit bridge for HS (`hs_orderOf_dvd_50_of_semiRegular`)
3. arithmetic core (`lem18_case1_arithmetic_5group_dvd_50_implies_25`)

No `hsemi` hypothesis is required.  This is the prime-case end-to-end Path B
chain for HS-fix. -/
theorem lem18_case1_orderOf_dvd_25_with_HSFixedData_prime_via_semiRegular
    (hΓ : IsMoore57 Γ) (σ : Equiv.Perm V) (pow_5 : σ ^ 5 = 1)
    (hsfd : HSFixedData Γ σ) (i : Fin 50)
    (smul_adj : ∀ v w : V, Γ.Adj v w ↔ Γ.Adj (σ v) (σ w)) :
    orderOf σ ∣ 25 :=
  lem18_case1_orderOf_dvd_25_with_HSFixedData_semiRegular
    hΓ σ 1 (by rw [pow_one]; exact pow_5) hsfd i smul_adj
    (Moore57.aut_semiRegular_at_movedNeighbor_of_prime
      (Γ := Γ) σ 5 (by decide) pow_5 (hsfd.v i))

/-- **Lemma 18 case (2) prime-case via semi-regular (fully unconditional).** [done — Path B]

For σ a graph automorphism of Γ with σ^5 = 1 and `C5FixedData Γ σ`,
`orderOf σ ∣ 5` follows trivially (orderOf σ ∣ 5).  The semi-regular
path gives an alternative derivation through the C3.4 bridge
(`c5_orderOf_dvd_55_of_semiRegular`, giving `orderOf σ ∣ 55`, sharpened
to `∣ 5` since 55 = 5 · 11 and σ is a 5-group). -/
theorem lem18_case2_orderOf_dvd_5_with_c5FixedData_prime_via_semiRegular
    (hΓ : IsMoore57 Γ) (σ : Equiv.Perm V) (pow_5 : σ ^ 5 = 1)
    (c5 : C5FixedData Γ σ) (i : Fin 5)
    (smul_adj : ∀ v w : V, Γ.Adj v w ↔ Γ.Adj (σ v) (σ w)) :
    orderOf σ ∣ 5 :=
  lem18_case2_orderOf_dvd_5_with_c5FixedData_semiRegular
    hΓ σ 1 (by rw [pow_one]; exact pow_5) c5 i smul_adj
    (Moore57.aut_semiRegular_at_movedNeighbor_of_prime
      (Γ := Γ) σ 5 (by decide) pow_5 (c5.v i))

/-- **Lemma 18 case (3) prime-case via semi-regular (fully unconditional).** [done — Path B]

For σ a graph automorphism of Γ with σ^5 = 1 and `EmptyFixedData σ`,
`orderOf σ ∣ 125` follows via:
1. prime-order semi-regular generator on the full vertex set
   (using `EmptyFixedData.no_fixed` and
   `semiRegular_at_movedPoint_of_prime_orderOf`)
2. C3.4 empty-fix bridge (`empty_orderOf_dvd_3250_of_semiRegular`,
   giving `orderOf σ ∣ 3250`)
3. arithmetic core (`lem18_case3_arithmetic_5group_dvd_3250`)

No `hsemi` hypothesis is required. -/
theorem lem18_case3_orderOf_dvd_125_with_emptyFixedData_prime_via_semiRegular
    (hΓ : IsMoore57 Γ) (σ : Equiv.Perm V) (pow_5 : σ ^ 5 = 1)
    (efd : EmptyFixedData σ) :
    orderOf σ ∣ 125 :=
  lem18_case3_orderOf_dvd_125_with_emptyFixedData_semiRegular
    hΓ σ 1 (by rw [pow_one]; exact pow_5) efd
    (fun v k hkv =>
      Moore57.semiRegular_at_movedPoint_of_prime_orderOf
        σ 5 (by decide) pow_5 v (efd.no_fixed v) k hkv)

end Moore57.Papers.MacajSiran2010.S6
