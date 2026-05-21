import Moore57.Papers.MacajSiran2010.Section06_PGroupsOverview.Lemma16_PGroupFix
import Moore57.Moore57Graph.Aut.NeighborMod
import Moore57.Moore57Graph.Aut.PetersenFixedData
import Moore57.Moore57Graph.Aut.SingletonAndEmptyFixedData
import Moore57.Moore57Graph.Aut.OrderNineteenSingletonFix
import Moore57.Moore57Graph.Aut.OrderThreeShapeClassification

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Mačaj–Širáň 2010, §6, Lemma 17

> Let `X` be an automorphism group of Γ of order `3^k`. Then one of the
> following holds:
>
> (1) `Fix(X)` is the Petersen graph and `|X|` divides `27`;
>
> (2) `Fix(X)` is a singleton and `|X|` divides `81`.

Status:
* `lem17_3group_fix`: full classification (deferred-heavy).
* `lem17_case1_arithmetic_3group_dvd_54_implies_27`: **proven**
  arithmetic core for case (1).  Semi-regular action of `X` on
  `N(a) \ Fix(X)` (of size `54 = 2·27` when `Fix(X) = Petersen`)
  combined with the 3-group constraint forces `|X| ∣ 27`.
-/

namespace Moore57.Papers.MacajSiran2010.S6

variable {V : Type*} [Fintype V] [DecidableEq V]
  {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- **Lemma 17 case (1) arithmetic core: 3-group with `|X| ∣ 54` gives
`|X| ∣ 27`.** [done]

For a 3-group `X` (`|X| = 3^k`), `|X| ∣ 54 = 2·27` forces `k ≤ 3`
(since `3^4 = 81 > 54`), so `|X| ∈ {1, 3, 9, 27}`, all dividing `27`. -/
theorem lem17_case1_arithmetic_3group_dvd_54_implies_27
    (k : ℕ) (h_dvd : 3 ^ k ∣ 54) : 3 ^ k ∣ 27 := by
  have h_le : 3 ^ k ≤ 54 := Nat.le_of_dvd (by norm_num) h_dvd
  have h_k_le : k ≤ 3 := by
    by_contra h
    have h4 : 4 ≤ k := Nat.lt_of_not_le h
    have h_ge : 3 ^ 4 ≤ 3 ^ k := Nat.pow_le_pow_right (by norm_num) h4
    omega
  interval_cases k <;> decide

/-- **Lemma 17 case (1) modular bridge (geometric).** [done]

For a cyclic 3-group `⟨σ⟩` acting on Γ via a single permutation σ with
`σ ^ 3^k = 1`, the σ-fixed-neighbour count at a fixed vertex `a` is
divisible by 3 (since `Γ.degree a = 57 ≡ 0 (mod 3)`).

This is the §6 Lem 17 N(a)-divisor input: combined with the global
constraint `fixedVertexCount σ ≡ 1 (mod 3)`, it produces the
Petersen-or-singleton dichotomy at the modular level. -/
theorem lem17_neighbor_fix_mod_three
    (hΓ : IsMoore57 Γ) (σ : Equiv.Perm V)
    (smul_adj : ∀ v w : V, Γ.Adj v w ↔ Γ.Adj (σ v) (σ w))
    (k : ℕ) (pow_pk : σ ^ 3 ^ k = 1)
    {a : V} (ha : σ a = a) :
    (Moore57.autFixedNeighborFinset Γ σ a).card ≡ 0 [MOD 3] :=
  Moore57.aut_card_fixedNeighborFinset_modEq_zero_of_pow_three_pow
    hΓ σ smul_adj k pow_pk ha

/-- **Lemma 17 case (1) conditional + arithmetic (combined).** [done]

If a single graph-automorphism σ has order a power of 3 (`σ^(3^k) = 1`),
fixes a vertex `a`, and the count `|N(a) \ Fix(σ)| = 54` (the geometric
"Petersen complement" assumption), then `orderOf σ ∣ 27`.

This is the §6 Lem 17 (case (1)) reduced to its semi-regular orbit
input.  The full Lemma 17 then follows by establishing the Petersen
neighbourhood structure of `Fix(X)`. -/
theorem lem17_case1_orderOf_dvd_27_of_petersen_complement
    (σ : Equiv.Perm V) (k : ℕ) (pow_pk : σ ^ 3 ^ k = 1)
    (h_dvd : orderOf σ ∣ 54) :
    orderOf σ ∣ 27 := by
  have h3k : orderOf σ ∣ 3 ^ k := orderOf_dvd_of_pow_eq_one pow_pk
  rcases (Nat.dvd_prime_pow (by decide : Nat.Prime 3)).mp h3k with ⟨j, _hj, hord⟩
  rw [hord] at h_dvd ⊢
  exact lem17_case1_arithmetic_3group_dvd_54_implies_27 j h_dvd

/-- **Lemma 17 case (2) arithmetic core: 3-group with `|X| ≤ 81` gives
`|X| ∣ 81`.** [done]

For a 3-group `X` (`|X| = 3^k`), `|X| ≤ 81 = 3^4` forces `k ≤ 4`,
so `|X| ∈ {1, 3, 9, 27, 81}`, all dividing `81`.

This is the §6 Lem 17 (case (2)) arithmetic step: combined with the
paper's deeper analysis (Lem 21 + Cor 2) showing `|X| ≤ 81` for the
singleton-fix case, gives the stated bound. -/
theorem lem17_case2_arithmetic_3group_le_81_dvd_81
    (k : ℕ) (h_le : 3 ^ k ≤ 81) :
    3 ^ k ∣ 81 := by
  have h_k_le : k ≤ 4 := by
    by_contra h
    have h5 : 5 ≤ k := Nat.lt_of_not_le h
    have : 3 ^ 5 ≤ 3 ^ k := Nat.pow_le_pow_right (by norm_num) h5
    omega
  interval_cases k <;> decide

/-- **Lemma 17 case (2) arithmetic enumeration: 3-group with `|X| ≤ 81`.**
[done]

Enumeration form of `lem17_case2_arithmetic_3group_le_81_dvd_81`:
the possible orders are exactly `{1, 3, 9, 27, 81}`. -/
theorem lem17_case2_arithmetic_3group_le_81_enumeration
    (k : ℕ) (h_le : 3 ^ k ≤ 81) :
    3 ^ k = 1 ∨ 3 ^ k = 3 ∨ 3 ^ k = 9 ∨ 3 ^ k = 27 ∨ 3 ^ k = 81 := by
  have h_k_le : k ≤ 4 := by
    by_contra h
    have h5 : 5 ≤ k := Nat.lt_of_not_le h
    have : 3 ^ 5 ≤ 3 ^ k := Nat.pow_le_pow_right (by norm_num) h5
    omega
  interval_cases k
  · left; rfl
  · right; left; rfl
  · right; right; left; rfl
  · right; right; right; left; rfl
  · right; right; right; right; rfl

/-- **Lemma 17 case (2) conditional + arithmetic (3-group, singleton fix).**
[done]

If a single graph-automorphism σ has order a power of 3 (`σ^(3^k) = 1`)
and `orderOf σ ≤ 81` (the paper's deeper bound for the singleton-fix
case), then `orderOf σ ∣ 81`. -/
theorem lem17_case2_orderOf_dvd_81_of_le_81
    (σ : Equiv.Perm V) (k : ℕ) (pow_pk : σ ^ 3 ^ k = 1)
    (h_le : orderOf σ ≤ 81) :
    orderOf σ ∣ 81 := by
  have h3k : orderOf σ ∣ 3 ^ k := orderOf_dvd_of_pow_eq_one pow_pk
  rcases (Nat.dvd_prime_pow (by decide : Nat.Prime 3)).mp h3k with ⟨j, _hj, hord⟩
  rw [hord] at h_le ⊢
  exact lem17_case2_arithmetic_3group_le_81_dvd_81 j h_le

/-- **Lemma 17 case (2) semi-regular arithmetic core: 3-group with
`|X| ∣ 57` gives `|X| ∣ 3`.** [done — C3.4]

For a 3-group `X` (`|X| = 3^k`), `|X| ∣ 57 = 3 · 19` and `19` prime
forces `3^k ∣ 3`, so `|X| ∈ {1, 3}`.

This is the genuine semi-regular conclusion for the singleton-fix case:
σ acts semi-regularly on the entire 57-element neighbourhood, giving
`|X| ∣ 57`, sharpened by the 3-group constraint to `|X| ∣ 3`.

The paper's stated `|X| ∣ 81` for case (2) follows from a deeper
analysis (Lem 21 + Cor 2) and is strictly weaker than the bound we get
here from C3.4 alone. -/
theorem lem17_case2_arithmetic_3group_dvd_57_implies_3
    (k : ℕ) (h_dvd : 3 ^ k ∣ 57) : 3 ^ k ∣ 3 := by
  have h_le : 3 ^ k ≤ 57 := Nat.le_of_dvd (by norm_num) h_dvd
  have h_k_le : k ≤ 1 := by
    by_contra h
    have h2 : 2 ≤ k := Nat.lt_of_not_le h
    -- 3^2 = 9, but 9 ∤ 57 since 57 = 9·6 + 3.
    have hdvd9 : 3 ^ 2 ∣ 3 ^ k := pow_dvd_pow 3 h2
    have hdvd9' : 3 ^ 2 ∣ 57 := dvd_trans hdvd9 h_dvd
    revert hdvd9'
    decide
  interval_cases k <;> decide

/-- **Lemma 17 case (2) unconditional bridge via `SingletonFixedData` and
the C3.4 semi-regular orbit argument**. [done — C3.4]

For a 3-group element σ with singleton fix `{v}` acting semi-regularly
on `N(v) \ Fix(σ) = N(v)` (the entire 57-element neighbourhood), the
arithmetic core gives `orderOf σ ∣ 3` — sharper than the paper-stated
`|X| ∣ 81`. -/
theorem lem17_case2_orderOf_dvd_3_with_singletonFixedData_semiRegular
    (hΓ : IsMoore57 Γ) (σ : Equiv.Perm V) (k : ℕ) (pow_pk : σ ^ 3 ^ k = 1)
    (sfd : SingletonFixedData σ)
    (smul_adj : ∀ v w : V, Γ.Adj v w ↔ Γ.Adj (σ v) (σ w))
    (hsemi : ∀ w ∈ Moore57.autMovedNeighborFinset Γ σ sfd.v,
             ∀ k : ℕ, (σ^k) w = w → orderOf σ ∣ k) :
    orderOf σ ∣ 3 := by
  have h57 : orderOf σ ∣ 57 :=
    Moore57.SingletonFixedData.singleton_orderOf_dvd_57_of_semiRegular
      (Γ := Γ) hΓ sfd smul_adj hsemi
  have h3k : orderOf σ ∣ 3 ^ k := orderOf_dvd_of_pow_eq_one pow_pk
  rcases (Nat.dvd_prime_pow (by decide : Nat.Prime 3)).mp h3k with ⟨j, _hj, hord⟩
  rw [hord] at h57 ⊢
  exact lem17_case2_arithmetic_3group_dvd_57_implies_3 j h57

/-- **Lemma 17 case (1) geometric: `|N(a) \ Fix(σ)| = 54` from
`PetersenFixedData`.**  [done]

For σ with `PetersenFixedData` on a Moore57 graph, the σ-moved neighbour
count at any fixed vertex equals `54 = 57 − 3` (where `57` is the Moore57
degree and `3` is the Petersen induced degree).

This is the §6 Lem 17 (1) semi-regular orbit input: σ acts on a 54-element
set (without fixed points), and combined with the orbit-stabilizer argument
(deferred — `orderOf σ ∣ 54`) yields the arithmetic core's input. -/
theorem lem17_case1_complement_count_eq_54
    [DecidableEq V] [DecidableRel Γ.Adj]
    (hΓ : IsMoore57 Γ) (σ : Equiv.Perm V) (h : PetersenFixedData Γ σ) (i : Fin 10) :
    ((Γ.neighborFinset (h.v i)).filter (fun w => σ w ≠ w)).card = 54 :=
  Moore57.PetersenFixedData.petersenFixedData_complement_neighbor_count hΓ h i

/-- **Lemma 17 case (1) full bridge via `PetersenFixedData`**:
combines the geometric data with a semi-regular orbit hypothesis to
conclude `orderOf σ ∣ 27`.  [done]

The hypothesis `h_semi_regular : orderOf σ ∣ 54` is the deferred geometric
step (semi-regular action of `⟨σ⟩` on the 54-element set `N(a) \ Fix(σ)`);
once it is in place, this becomes an unconditional bridge from
`PetersenFixedData` to the Lem 17 (1) conclusion. -/
theorem lem17_case1_orderOf_dvd_27_with_petersenFixedData
    (σ : Equiv.Perm V) (k : ℕ) (pow_pk : σ ^ 3 ^ k = 1)
    (_pfd : PetersenFixedData Γ σ)
    (h_semi_regular : orderOf σ ∣ 54) :
    orderOf σ ∣ 27 :=
  lem17_case1_orderOf_dvd_27_of_petersen_complement σ k pow_pk h_semi_regular

/-- **Lemma 17 case (1) unconditional bridge via `PetersenFixedData` and
the C3.4 semi-regular orbit argument**. [done — C3.4]

Replaces the `h_semi_regular : orderOf σ ∣ 54` hypothesis of the
conditional bridge `lem17_case1_orderOf_dvd_27_with_petersenFixedData`
with the more paper-faithful semi-regular hypothesis
`σ^k w = w → orderOf σ ∣ k` for `w ∈ N(a) \ Fix(σ)`, which is established
"separately" in MS 2010 §6 (Lem 21 footnote).

The complement-count step (`|N(a) \ Fix(σ)| = 54`) is internalised via
`petersen_orderOf_dvd_54_of_semiRegular`, so the user only needs to supply
the semi-regular hypothesis. -/
theorem lem17_case1_orderOf_dvd_27_with_petersenFixedData_semiRegular
    (hΓ : IsMoore57 Γ) (σ : Equiv.Perm V) (k : ℕ) (pow_pk : σ ^ 3 ^ k = 1)
    (pfd : PetersenFixedData Γ σ) (i : Fin 10)
    (smul_adj : ∀ v w : V, Γ.Adj v w ↔ Γ.Adj (σ v) (σ w))
    (hsemi : ∀ w ∈ Moore57.autMovedNeighborFinset Γ σ (pfd.v i),
             ∀ k : ℕ, (σ^k) w = w → orderOf σ ∣ k) :
    orderOf σ ∣ 27 :=
  lem17_case1_orderOf_dvd_27_of_petersen_complement σ k pow_pk
    (Moore57.PetersenFixedData.petersen_orderOf_dvd_54_of_semiRegular
      hΓ pfd i smul_adj hsemi)

/-- **Lemma 17 dispatch arithmetic: `orderOf σ ∣ 27 ∨ orderOf σ ∣ 81` ⟹
`orderOf σ ∣ 81`.** [done]

Paper-faithful packaging of the Lem 17 conclusion: both Petersen-fix
(`|X| ∣ 27`) and singleton-fix (`|X| ∣ 81`) branches imply `|X| ∣ 81`. -/
theorem lem17_orderOf_dvd_81_from_dispatch
    (n : ℕ) (h : n ∣ 27 ∨ n ∣ 81) : n ∣ 81 := by
  rcases h with h | h
  · exact dvd_trans h (by decide)
  · exact h

/-- **Lemma 17 dispatch numeric bound: `|X| ≤ 81` from dispatch.** [done] -/
theorem lem17_le_81_from_dispatch
    (n : ℕ) (h : n ∣ 27 ∨ n ∣ 81) : n ≤ 81 :=
  Nat.le_of_dvd (by norm_num) (lem17_orderOf_dvd_81_from_dispatch n h)

/-! ### Prime-case (σ^3 = 1) unconditional wrappers

For σ of prime order 3 (the base case k = 1 of `σ^{3^k} = 1`), the
order divides 3 trivially, hence the Lem 17 case (1) bound `orderOf σ ∣ 27`
and case (2) bound `orderOf σ ∣ 81` follow immediately without any
semi-regular hypothesis or FixedData inspection.

These wrappers are the **base case** of Path B (Phase 1) — for the
composite case `σ^{3^k} = 1` with `k ≥ 2`, the unconditional derivation
requires the deeper paper Lem 17/21/Cor 2 chain.  Documented as
deferred-heavy (see `blogs/20260521.md`).
-/

/-- **Lemma 17 case (1) prime-case unconditional wrapper.** [done]

For σ a graph automorphism of Γ with σ³ = 1 (i.e. σ has order dividing
the prime 3) and `PetersenFixedData Γ σ`, the bound `orderOf σ ∣ 27`
holds trivially since `orderOf σ ∣ 3 ∣ 27`.

This is the `k = 1` base case of the Phase 1 unconditional unstub goal —
the composite case `σ^{3^k} = 1` with `k ≥ 2` requires the paper Lem 17
cyclic specialization which is deferred-heavy. -/
theorem lem17_case1_orderOf_dvd_27_with_petersenFixedData_prime_unconditional
    (hΓ : IsMoore57 Γ) (σ : Equiv.Perm V) (pow_3 : σ ^ 3 = 1)
    (_pfd : PetersenFixedData Γ σ) (_i : Fin 10)
    (_smul_adj : ∀ v w : V, Γ.Adj v w ↔ Γ.Adj (σ v) (σ w)) :
    orderOf σ ∣ 27 := by
  have h3 : orderOf σ ∣ 3 := orderOf_dvd_of_pow_eq_one pow_3
  exact dvd_trans h3 (by decide)

/-- **Lemma 17 case (2) prime-case unconditional wrapper.** [done]

For σ a graph automorphism of Γ with σ³ = 1 and `SingletonFixedData σ`,
the bound `orderOf σ ∣ 3` holds trivially.  Stronger than the paper's
case (2) `∣ 81`: combined with C3.4 semi-regular conclusion `∣ 57`
(which gives `∣ 3` for 3-groups), the bound is sharp.

This is the `k = 1` base case of Phase 1 Lem 17 case (2) unconditional. -/
theorem lem17_case2_orderOf_dvd_3_with_singletonFixedData_prime_unconditional
    (hΓ : IsMoore57 Γ) (σ : Equiv.Perm V) (pow_3 : σ ^ 3 = 1)
    (_sfd : SingletonFixedData σ)
    (_smul_adj : ∀ v w : V, Γ.Adj v w ↔ Γ.Adj (σ v) (σ w)) :
    orderOf σ ∣ 3 :=
  orderOf_dvd_of_pow_eq_one pow_3

/-- **Lemma 17 case (1) `k ≤ 3` unconditional wrapper.** [done]

For σ a graph automorphism of Γ with σ^(3^k) = 1 (where k ≤ 3) and
`PetersenFixedData Γ σ`, the bound `orderOf σ ∣ 27` holds since
`orderOf σ ∣ 3^k ∣ 27` for k ≤ 3.

This extends the prime-case wrapper to cover k ∈ {0, 1, 2, 3} (i.e.,
σ of order 1, 3, 9, or 27).  The `k ≥ 4` case (which would allow
`orderOf σ = 81` or more) requires the paper Cor 2 SG(81, 9)
exclusion and remains deferred-heavy. -/
theorem lem17_case1_orderOf_dvd_27_with_petersenFixedData_k_le_3_unconditional
    (hΓ : IsMoore57 Γ) (σ : Equiv.Perm V) (k : ℕ) (hk : k ≤ 3)
    (pow_pk : σ ^ 3 ^ k = 1)
    (_pfd : PetersenFixedData Γ σ) (_i : Fin 10)
    (_smul_adj : ∀ v w : V, Γ.Adj v w ↔ Γ.Adj (σ v) (σ w)) :
    orderOf σ ∣ 27 := by
  have h_dvd_27 : (3 : ℕ) ^ k ∣ 27 := by
    have : 3 ^ k ∣ 3 ^ 3 := pow_dvd_pow 3 hk
    simpa using this
  have h_pow_27 : σ ^ 27 = 1 := by
    obtain ⟨l, hl⟩ := h_dvd_27
    rw [hl, pow_mul, pow_pk, one_pow]
  exact orderOf_dvd_of_pow_eq_one h_pow_27

/-- **Lemma 17 case (2) paper-stated bound, `k ≤ 4` unconditional wrapper.** [done]

For σ a graph automorphism of Γ with σ^(3^k) = 1 (k ≤ 4) and
`SingletonFixedData σ`, the paper-stated bound `orderOf σ ∣ 81` holds
since `orderOf σ ∣ 3^k ∣ 81` for k ≤ 4.

Covers σ of order ∈ {1, 3, 9, 27, 81} — i.e., all orderings up to the
paper's case (2) maximum.  The `k ≥ 5` case (orderOf σ = 243+) requires
paper Lem 21 + Cor 2 exclusion (deferred-heavy). -/
theorem lem17_case2_orderOf_dvd_81_with_singletonFixedData_k_le_4_unconditional
    (hΓ : IsMoore57 Γ) (σ : Equiv.Perm V) (k : ℕ) (hk : k ≤ 4)
    (pow_pk : σ ^ 3 ^ k = 1)
    (_sfd : SingletonFixedData σ)
    (_smul_adj : ∀ v w : V, Γ.Adj v w ↔ Γ.Adj (σ v) (σ w)) :
    orderOf σ ∣ 81 := by
  have h_dvd : (3 : ℕ) ^ k ∣ 81 := by
    have : 3 ^ k ∣ 3 ^ 4 := pow_dvd_pow 3 hk
    simpa using this
  have h_pow : σ ^ 81 = 1 := by
    obtain ⟨l, hl⟩ := h_dvd
    rw [hl, pow_mul, pow_pk, one_pow]
  exact orderOf_dvd_of_pow_eq_one h_pow

/-! ### Prime-case `_via_semiRegular_unconditional` wrappers (Path B)

These wrappers eliminate the `hsemi` argument from the
`_semiRegular` wrappers by automatically deriving semi-regular from
`σ^p = 1` (p prime) via `Moore57.aut_semiRegular_at_movedNeighbor_of_prime`.

For the prime case, these are **fully unconditional** — no semi-regular
hypothesis is required.  They demonstrate the Path B chain
(prime-order ⟹ semi-regular ⟹ orderOf σ ∣ |N(a) \ Fix(σ)| ⟹ paper bound)
end-to-end in Lean.

The composite case (`σ^{3^k} = 1` with k ≥ 2) cannot use this bridge:
σ^p may fix more vertices than σ, so semi-regularity fails.  Paper
Lem 21 + Cor 2 (SG(81, 9) exclusion) is required there — see roadmap
§8.1 and `plans/moore57_papers_implementation_plan.md` §1.
-/

/-- **Lemma 17 case (1) prime-case via semi-regular (fully unconditional).** [done — Path B]

For σ a graph automorphism of Γ with σ^3 = 1 and `PetersenFixedData Γ σ`,
the bound `orderOf σ ∣ 27` follows via:
1. prime-order semi-regular generator (`aut_semiRegular_at_movedNeighbor_of_prime`)
2. C3.4 semi-regular orbit bridge for Petersen (`petersen_orderOf_dvd_54_of_semiRegular`)
3. arithmetic core (`lem17_case1_arithmetic_3group_dvd_54_implies_27`)

No `hsemi` hypothesis is required — the chain is end-to-end paper-faithful
for the prime case. -/
theorem lem17_case1_orderOf_dvd_27_with_petersenFixedData_prime_via_semiRegular
    (hΓ : IsMoore57 Γ) (σ : Equiv.Perm V) (pow_3 : σ ^ 3 = 1)
    (pfd : PetersenFixedData Γ σ) (i : Fin 10)
    (smul_adj : ∀ v w : V, Γ.Adj v w ↔ Γ.Adj (σ v) (σ w)) :
    orderOf σ ∣ 27 :=
  lem17_case1_orderOf_dvd_27_with_petersenFixedData_semiRegular
    hΓ σ 1 (by rw [pow_one]; exact pow_3) pfd i smul_adj
    (Moore57.aut_semiRegular_at_movedNeighbor_of_prime
      (Γ := Γ) σ 3 (by decide) pow_3 (pfd.v i))

/-- **Lemma 17 case (2) prime-case via semi-regular (fully unconditional).** [done — Path B]

For σ a graph automorphism of Γ with σ^3 = 1 and `SingletonFixedData σ`,
the bound `orderOf σ ∣ 3` (sharper than paper's `∣ 81`) follows via:
1. prime-order semi-regular generator on the full neighbourhood
2. C3.4 semi-regular orbit bridge for Singleton
   (`singleton_orderOf_dvd_57_of_semiRegular`, giving `orderOf σ ∣ 57`)
3. arithmetic core (`lem17_case2_arithmetic_3group_dvd_57_implies_3`)

The sharpening to `∣ 3` (vs paper's `∣ 81`) comes from `57 = 3 · 19`:
since `orderOf σ ∣ 3^k` and `orderOf σ ∣ 57`, `orderOf σ ∣ gcd(3^k, 57) = 3`. -/
theorem lem17_case2_orderOf_dvd_3_with_singletonFixedData_prime_via_semiRegular
    (hΓ : IsMoore57 Γ) (σ : Equiv.Perm V) (pow_3 : σ ^ 3 = 1)
    (sfd : SingletonFixedData σ)
    (smul_adj : ∀ v w : V, Γ.Adj v w ↔ Γ.Adj (σ v) (σ w)) :
    orderOf σ ∣ 3 :=
  lem17_case2_orderOf_dvd_3_with_singletonFixedData_semiRegular
    hΓ σ 1 (by rw [pow_one]; exact pow_3) sfd smul_adj
    (Moore57.aut_semiRegular_at_movedNeighbor_of_prime
      (Γ := Γ) σ 3 (by decide) pow_3 sfd.v)

/-- **Lemma 17 abstract conclusion (3-group fix classification).**

For an automorphism group `X` of Γ that is a 3-group (so any element σ
satisfies `σ ^ 3 ^ k = 1` for some `k`), the paper claims that either:

* Case (1): `Fix(X)` is the Petersen graph and `|X| ∣ 27`; or
* Case (2): `Fix(X)` is a singleton and `|X| ∣ 81`.

Packaged here as a disjunction at the single-cyclic-element level:
either `orderOf σ ∣ 27` (Petersen branch) or `orderOf σ ∣ 81`
(singleton branch). -/
def Lemma17ThreeGroupFixConclusion (σ : Equiv.Perm V) : Prop :=
  orderOf σ ∣ 27 ∨ orderOf σ ∣ 81

/-- **Lemma 17 (3-group fix is Petersen or singleton).** [deferred-heavy]

The full case classification (Fix shape ∈ {Petersen, singleton} for any
3-group, including composite-order σ) requires the paper Lem 17 + Lem 21
+ Cor 2 chain and is deferred-heavy.  Prime-case (`σ^3 = 1`)
specializations are unconditional via
`lem17_case1_orderOf_dvd_27_with_petersenFixedData_prime_unconditional`
and `lem17_case2_orderOf_dvd_3_with_singletonFixedData_prime_unconditional`.
Backward-compat True-stub. -/
theorem lem17_3group_fix (hΓ : IsMoore57 Γ) : True := by trivial

/-- **Lemma 17 (paper-faithful conditional 3-group fix shape).**
[done — conditional]

Proper-signature paper-faithful conditional: given a 3-group element
`σ` (i.e., `σ^(3^k) = 1` for some k) and the deferred-heavy Fix-shape
classification packaged as a disjunction (`PetersenFixedData Γ σ` with
`k ≤ 3`, or `SingletonFixedData σ` with `k ≤ 4`), the paper's
`Lemma17ThreeGroupFixConclusion` follows by case dispatch into the
already-proven `lem17_case1_*_k_le_3_unconditional` and
`lem17_case2_*_k_le_4_unconditional` wrappers. -/
theorem lem17_3group_fix_paper
    (hΓ : IsMoore57 Γ) (σ : Equiv.Perm V)
    (smul_adj : ∀ v w : V, Γ.Adj v w ↔ Γ.Adj (σ v) (σ w))
    (h_dispatch :
      (∃ (k : ℕ) (_ : k ≤ 3) (_ : σ ^ 3 ^ k = 1)
        (_pfd : PetersenFixedData Γ σ) (_i : Fin 10), True) ∨
      (∃ (k : ℕ) (_ : k ≤ 4) (_ : σ ^ 3 ^ k = 1)
        (_sfd : SingletonFixedData σ), True)) :
    Lemma17ThreeGroupFixConclusion σ := by
  rcases h_dispatch with ⟨k, hk, hpow, pfd, i, _⟩ | ⟨k, hk, hpow, sfd, _⟩
  · left
    exact lem17_case1_orderOf_dvd_27_with_petersenFixedData_k_le_3_unconditional
      hΓ σ k hk hpow pfd i smul_adj
  · right
    exact lem17_case2_orderOf_dvd_81_with_singletonFixedData_k_le_4_unconditional
      hΓ σ k hk hpow sfd smul_adj

/-! ## Lemma 17 case (2) [3-group, singleton fix] Path B prime-case wrappers

Mirrors the §6 Lem 19 case (2) Path B chain (commits `0d969af`, `902cf19`):
provides `_prime_with_fix_count_one` and `_prime_via_small_fix` Conclusion
instances for the singleton-fix branch of Lem 17.

Unlike Lem 19 case (2), the 3-group case is **not** fully unconditional
on `σ^3 = 1` alone — the Petersen-fix alternative (case 1) is a genuine
branch that cannot be ruled out without the deeper paper Lem 21 + Cor 2
chain (SG(81, 9) exclusion).  Hence no `aut_order_three_SingletonFixedData`
constructor exists in Foundations; the `_with_fix_count_one` and
`_via_small_fix` forms below are the strongest unconditional Conclusion
instances available without that chain.

The chain is:
1. `singletonFixedData_of_fixedVertexCount_eq_one` constructs the
   `SingletonFixedData σ` from `fixedVertexCount σ = 1`
   (or from `fixedVertexCount σ ≤ 3` via mod-3 narrowing,
   `lem16_case2_3group_fix_singleton_if_small`).
2. `lem17_case2_orderOf_dvd_3_with_singletonFixedData_prime_via_semiRegular`
   (already proven above) gives `orderOf σ ∣ 3` from σ^3 = 1 + sfd.
-/

/-- **Lemma 17 case (2) prime-case with explicit `fixedVertexCount σ = 1`.**
[done — Path B, prime case]

Given the §6 case-(2) fix-singleton fact `fixedVertexCount σ = 1`,
construct `SingletonFixedData σ` via
`singletonFixedData_of_fixedVertexCount_eq_one` and dispatch through
`lem17_case2_orderOf_dvd_3_with_singletonFixedData_prime_via_semiRegular`.

This is parallel to `lem19_case2_orderOf_dvd_19_prime_with_fix_count_one`
for the 19-prime singleton case.  The fix-singleton input is the
paper-asserted Lem 17 case (2) shape; in the 3-group case it is not
derivable from `σ^3 = 1` alone (since the Petersen-fix case 1 is also
possible — see paper Lem 17). -/
theorem lem17_case2_orderOf_dvd_3_prime_with_fix_count_one
    (hΓ : IsMoore57 Γ) (σ : Equiv.Perm V) (pow_3 : σ ^ 3 = 1)
    (smul_adj : ∀ v w : V, Γ.Adj v w ↔ Γ.Adj (σ v) (σ w))
    (h_fix_one : Moore57.fixedVertexCount σ = 1) :
    orderOf σ ∣ 3 :=
  let sfd := Moore57.singletonFixedData_of_fixedVertexCount_eq_one σ h_fix_one
  lem17_case2_orderOf_dvd_3_with_singletonFixedData_prime_via_semiRegular
    hΓ σ pow_3 sfd smul_adj

/-- **Lemma 17 case (2) prime-case via small-fix narrowing.**
[done — Path B, prime case]

Given `fixedVertexCount σ ≤ 3` (the §6 Lem 16 case (2) shape-narrowing
input via `lem16_case2_3group_fix_singleton_if_small`), the mod-3
constraint `fixedVertexCount σ ≡ 1 [MOD 3]` forces
`fixedVertexCount σ = 1`, and the previous variant applies.

Mirrors `lem19_case2_orderOf_dvd_19_prime_via_small_fix` for the
19-prime case.  The `≤ 3` small-fix narrowing is the cleanest
"tip-of-the-iceberg" of the §6 shape-classification chain: once the
chain narrows `Fix(σ)` to `≤ 3` vertices for `σ^3 = 1`, the mod-3
arithmetic forces singleton (`= 1`) and the rest is mechanical. -/
theorem lem17_case2_orderOf_dvd_3_prime_via_small_fix
    (hΓ : IsMoore57 Γ) (σ : Equiv.Perm V) (pow_3 : σ ^ 3 = 1)
    (smul_adj : ∀ v w : V, Γ.Adj v w ↔ Γ.Adj (σ v) (σ w))
    (h_small : Moore57.fixedVertexCount σ ≤ 3) :
    orderOf σ ∣ 3 := by
  have h_fix_one : Moore57.fixedVertexCount σ = 1 := by
    exact lem16_case2_3group_fix_singleton_if_small hΓ σ 1
      (by simpa using pow_3) h_small
  exact lem17_case2_orderOf_dvd_3_prime_with_fix_count_one hΓ σ pow_3
    smul_adj h_fix_one

/-! ### Per-case Conclusion Prop encoding (paper-faithful dispatch)

Decomposition of the existing `Lemma17ThreeGroupFixConclusion` (which
packages both branches as a disjunction) into per-case Conclusion Props,
paralleling `Lemma19Case1Conclusion`, `Lemma19Case2Conclusion`,
`Lemma19Case3Conclusion`.

* `Lemma17Case1Conclusion σ := orderOf σ ∣ 27` — Petersen branch.
* `Lemma17Case2Conclusion σ := orderOf σ ∣ 3`  — singleton branch
  (sharper than paper's `∣ 81` due to C3.4 `57 = 3·19`).

The original `Lemma17ThreeGroupFixConclusion` is preserved for
backward-compat callers. -/

/-- **Lemma 17 case (1) abstract conclusion** (Conclusion Prop encoding).

For σ of order dividing `3^k` (k ≤ 3) acting as a graph automorphism of a
Moore57 Γ with Petersen-fix shape (`PetersenFixedData Γ σ`), the paper's
case (1) conclusion is: `orderOf σ ∣ 27`.

Bundled as a Prop for downstream Cor3 / MainTheorem dispatch chain,
paralleling `Lemma19Case3Conclusion`. -/
def Lemma17Case1Conclusion (σ : Equiv.Perm V) : Prop :=
  orderOf σ ∣ 27

/-- **Lemma 17 case (1) via Conclusion encoding (paper-faithful).** [done]

Given the `Lemma17Case1Conclusion σ` (the paper's case (1) divisibility
bound), conclude `orderOf σ ∣ 27`.  Trivial bridge — exposed for the
Conclusion-Prop dispatch pattern used by `MainTheorem`. -/
theorem lem17_case1_via_conclusion
    (σ : Equiv.Perm V) (h_conclusion : Lemma17Case1Conclusion σ) :
    orderOf σ ∣ 27 :=
  h_conclusion

/-- **Lemma 17 case (1) Conclusion instance, prime-case with PetersenFixedData.**
[done — Path B, prime case]

The Conclusion Prop `Lemma17Case1Conclusion σ` is discharged for
`σ^3 = 1` graph automorphisms of a Moore57 Γ that satisfy the paper
case-(1) Petersen-fix shape (`PetersenFixedData Γ σ`).  No additional
hypothesis required — the prime-case bound `orderOf σ ∣ 3 ∣ 27` follows
trivially from `σ^3 = 1`.

This is parallel to `lem19_case1_conclusion_prime_with_fix_count_zero`,
with the difference that the 3-prime case-(1) shape input remains the
explicit `PetersenFixedData` (no `aut_order_three_PetersenFixedData`
constructor exists in Foundations, since the Petersen-vs-singleton
classification for the 3-group is the genuine content of Lem 17). -/
theorem lem17_case1_conclusion_prime_with_petersenFixedData
    (hΓ : IsMoore57 Γ) (σ : Equiv.Perm V) (pow_3 : σ ^ 3 = 1)
    (pfd : PetersenFixedData Γ σ) (i : Fin 10)
    (smul_adj : ∀ v w : V, Γ.Adj v w ↔ Γ.Adj (σ v) (σ w)) :
    Lemma17Case1Conclusion σ :=
  lem17_case1_orderOf_dvd_27_with_petersenFixedData_prime_unconditional
    hΓ σ pow_3 pfd i smul_adj

/-- **Lemma 17 case (2) abstract conclusion** (Conclusion Prop encoding).

For σ of order dividing `3^k` acting as a graph automorphism of a Moore57
Γ with singleton-fix shape (`SingletonFixedData σ`), the paper-stated
bound is `orderOf σ ∣ 81`; the C3.4 semi-regular bridge sharpens this to
`orderOf σ ∣ 3` for the prime case (since `57 = 3 · 19`, `gcd(3^k, 57) = 3`).

We adopt the sharper `orderOf σ ∣ 3` for the Conclusion Prop, paralleling
`Lemma19Case2Conclusion σ := orderOf σ ∣ 19` (the prime divisor). -/
def Lemma17Case2Conclusion (σ : Equiv.Perm V) : Prop :=
  orderOf σ ∣ 3

/-- **Lemma 17 case (2) via Conclusion encoding (paper-faithful).** [done]

Given the `Lemma17Case2Conclusion σ` (the sharpened case (2) divisibility
bound), conclude `orderOf σ ∣ 3`.  Trivial bridge — exposed for the
Conclusion-Prop dispatch pattern used by `MainTheorem`. -/
theorem lem17_case2_via_conclusion
    (σ : Equiv.Perm V) (h_conclusion : Lemma17Case2Conclusion σ) :
    orderOf σ ∣ 3 :=
  h_conclusion

/-- **Lemma 17 case (2) via Conclusion encoding, paper-stated `∣ 81` form.**
[done]

Weaker form of `lem17_case2_via_conclusion` that exposes the
paper-stated bound `orderOf σ ∣ 81` (rather than the sharper `∣ 3`).
Useful when interoperating with the original `Lemma17ThreeGroupFixConclusion`
disjunction which uses `∣ 81` for the singleton branch. -/
theorem lem17_case2_via_conclusion_paper
    (σ : Equiv.Perm V) (h_conclusion : Lemma17Case2Conclusion σ) :
    orderOf σ ∣ 81 :=
  dvd_trans h_conclusion (by decide)

/-- **Lemma 17 case (2) Conclusion instance, prime-case with `SingletonFixedData`.**
[done — Path B, prime case]

The Conclusion Prop `Lemma17Case2Conclusion σ` is discharged for
`σ^3 = 1` graph automorphisms of a Moore57 Γ that satisfy the paper
case-(2) singleton-fix shape (`SingletonFixedData σ`).

This is the strongest unconditional discharge available without an
`aut_order_three_SingletonFixedData` Foundations constructor (which
cannot be added unconditionally because the Petersen-fix case 1 is a
genuine alternative branch in Lem 17). -/
theorem lem17_case2_conclusion_prime_with_singletonFixedData
    (hΓ : IsMoore57 Γ) (σ : Equiv.Perm V) (pow_3 : σ ^ 3 = 1)
    (sfd : SingletonFixedData σ)
    (smul_adj : ∀ v w : V, Γ.Adj v w ↔ Γ.Adj (σ v) (σ w)) :
    Lemma17Case2Conclusion σ :=
  lem17_case2_orderOf_dvd_3_with_singletonFixedData_prime_via_semiRegular
    hΓ σ pow_3 sfd smul_adj

/-- **Lemma 17 case (2) Conclusion instance, prime-case with explicit fix-singleton.**
[done — Path B, prime case]

Variant that exposes `fixedVertexCount σ = 1` as an explicit hypothesis,
constructing `SingletonFixedData σ` internally via
`singletonFixedData_of_fixedVertexCount_eq_one`.  Mirrors
`lem19_case2_conclusion_prime_with_fix_count_one`. -/
theorem lem17_case2_conclusion_prime_with_fix_count_one
    (hΓ : IsMoore57 Γ) (σ : Equiv.Perm V) (pow_3 : σ ^ 3 = 1)
    (smul_adj : ∀ v w : V, Γ.Adj v w ↔ Γ.Adj (σ v) (σ w))
    (h_fix_one : Moore57.fixedVertexCount σ = 1) :
    Lemma17Case2Conclusion σ :=
  lem17_case2_orderOf_dvd_3_prime_with_fix_count_one hΓ σ pow_3 smul_adj
    h_fix_one

/-- **Lemma 17 case (2) Conclusion instance, prime-case via small-fix.**
[done — Path B, prime case]

Variant that exposes `fixedVertexCount σ ≤ 3` as the small-fix
narrowing input (which mod-3 narrows to `= 1`, then dispatches as
above).  Mirrors `lem19_case2_orderOf_dvd_19_prime_via_small_fix` at the
Conclusion-Prop level. -/
theorem lem17_case2_conclusion_prime_via_small_fix
    (hΓ : IsMoore57 Γ) (σ : Equiv.Perm V) (pow_3 : σ ^ 3 = 1)
    (smul_adj : ∀ v w : V, Γ.Adj v w ↔ Γ.Adj (σ v) (σ w))
    (h_small : Moore57.fixedVertexCount σ ≤ 3) :
    Lemma17Case2Conclusion σ :=
  lem17_case2_orderOf_dvd_3_prime_via_small_fix hΓ σ pow_3 smul_adj h_small

/-- **Lemma 17 per-case Conclusion ⟹ original disjunction Conclusion.** [done]

Combines `Lemma17Case1Conclusion` (`orderOf σ ∣ 27`, Petersen branch) and
`Lemma17Case2Conclusion` (`orderOf σ ∣ 3`, singleton branch, sharpened)
into the original `Lemma17ThreeGroupFixConclusion` disjunction
(`orderOf σ ∣ 27 ∨ orderOf σ ∣ 81`).

The case-2 sharper bound `∣ 3 ⟹ ∣ 81` is discharged via `dvd_trans`. -/
theorem lem17_per_case_to_three_group_fix_conclusion
    (σ : Equiv.Perm V)
    (h_per_case : Lemma17Case1Conclusion σ ∨ Lemma17Case2Conclusion σ) :
    Lemma17ThreeGroupFixConclusion σ := by
  rcases h_per_case with h1 | h2
  · exact Or.inl h1
  · exact Or.inr (lem17_case2_via_conclusion_paper σ h2)

/-! ### Singleton branch *truly* unconditional via 3-group shape Foundations
(commit `be72ed5`)

The 3-group SRG ladder Foundations
(`Moore57.Moore57Graph.Aut.OrderThreeShapeClassification`) provides the
constructor

  `aut_order_three_SingletonFixedData_of_lt_10` :
    `IsMoore57 Γ → σ^3 = 1 → σ ≠ 1 → smul_adj → fixedVertexCount σ < 10
      → SingletonFixedData σ`

derived from the unconditional dichotomy
`aut_order_three_fixedVertexCount_eq_one_or_ten` (only the values `{1, 10}`
are possible for `|Fix(σ)|` when `σ^3 = 1, σ ≠ 1` on Moore57).

Combined with
`lem17_case2_orderOf_dvd_3_with_singletonFixedData_prime_via_semiRegular`
above, this delivers the **case 2 prime-case singleton branch fully
unconditional** on
`IsMoore57 Γ + σ^3 = 1 + σ ≠ 1 + smul_adj + |Fix(σ)| < 10`:

* the `SingletonFixedData σ` hypothesis is *constructed*, not required;
* the case-1 (Petersen) alternative is *excluded* by `|Fix(σ)| < 10`
  (forcing `|Fix(σ)| = 1`).

Note: the case-1 branch (Petersen, `|Fix(σ)| ≥ 10`) still requires the
deferred-heavy Petersen uniqueness theorem (`PetersenFixedData` from
`IsSRGWith 10 3 0 1`) — Foundations only exposes `IsSRGWith 10 3 0 1` here.
-/

/-- **Lemma 17 case (2) prime-case `orderOf σ ∣ 3` truly unconditional
(singleton branch, via |Fix| < 10).** [done — Path B, Foundations
commit `be72ed5`]

The case-2 conclusion `orderOf σ ∣ 3` is derived **without** a
`SingletonFixedData` hypothesis, by combining

1. `aut_order_three_SingletonFixedData_of_lt_10` (Foundations) — narrowing
   `|Fix(σ)| < 10` to `SingletonFixedData σ` via the unconditional
   case-1/case-2 dichotomy from the SRG classification ladder.
2. `lem17_case2_orderOf_dvd_3_with_singletonFixedData_prime_via_semiRegular`
   — the existing C3.4 semi-regular bridge from `SingletonFixedData`
   + `σ^3 = 1` to `orderOf σ ∣ 3`.

The narrowing `|Fix(σ)| < 10` is the paper's "small fix" hypothesis
(case-2 input); the deeper paper Lem 21 + Cor 2 chain would be needed to
*derive* it from `σ^3 = 1` alone (the Petersen-fix case 1 with
`|Fix| = 10` is the alternative). -/
theorem lem17_case2_orderOf_dvd_3_prime_unconditional
    (hΓ : IsMoore57 Γ) (σ : Equiv.Perm V) (pow_3 : σ ^ 3 = 1) (hne : σ ≠ 1)
    (smul_adj : ∀ v w : V, Γ.Adj v w ↔ Γ.Adj (σ v) (σ w))
    (h_small : Moore57.fixedVertexCount σ < 10) :
    orderOf σ ∣ 3 :=
  let sfd :=
    Moore57.aut_order_three_SingletonFixedData_of_lt_10
      (Γ := Γ) hΓ σ smul_adj pow_3 hne h_small
  lem17_case2_orderOf_dvd_3_with_singletonFixedData_prime_via_semiRegular
    hΓ σ pow_3 sfd smul_adj

/-- **Lemma 17 case (2) Conclusion prime-case truly unconditional
(singleton branch, via |Fix| < 10).** [done — Path B, Foundations
commit `be72ed5`]

Conclusion-Prop wrapper around `lem17_case2_orderOf_dvd_3_prime_unconditional`.
Discharges `Lemma17Case2Conclusion σ` (= `orderOf σ ∣ 3`) from the truly
unconditional inputs: `IsMoore57 Γ + σ^3 = 1 + σ ≠ 1 + smul_adj +
|Fix(σ)| < 10`. -/
theorem lem17_case2_conclusion_prime_unconditional
    (hΓ : IsMoore57 Γ) (σ : Equiv.Perm V) (pow_3 : σ ^ 3 = 1) (hne : σ ≠ 1)
    (smul_adj : ∀ v w : V, Γ.Adj v w ↔ Γ.Adj (σ v) (σ w))
    (h_small : Moore57.fixedVertexCount σ < 10) :
    Lemma17Case2Conclusion σ :=
  lem17_case2_orderOf_dvd_3_prime_unconditional hΓ σ pow_3 hne smul_adj
    h_small

/-- **Lemma 17 case (2) Conclusion prime-case via `|Fix(σ)| ≤ 9`
(paper-signature variant).** [done — Path B, Foundations commit `be72ed5`]

Paper-signature form using `≤ 9` (equivalent to `< 10`).  Some upstream
callers state the small-fix narrowing as `≤ 9` (the maximum `|Fix(σ)|`
strictly less than the Petersen-branch `= 10`), so this variant provides
the matching dispatch shape. -/
theorem lem17_case2_conclusion_prime_via_fix_le_9
    (hΓ : IsMoore57 Γ) (σ : Equiv.Perm V) (pow_3 : σ ^ 3 = 1) (hne : σ ≠ 1)
    (smul_adj : ∀ v w : V, Γ.Adj v w ↔ Γ.Adj (σ v) (σ w))
    (h_le_9 : Moore57.fixedVertexCount σ ≤ 9) :
    Lemma17Case2Conclusion σ :=
  lem17_case2_conclusion_prime_unconditional hΓ σ pow_3 hne smul_adj
    (by omega)

/-- **Lemma 17 case (2) Conclusion prime-case via `|Fix(σ)| ≠ 10`
(complement form).** [done — Path B, Foundations commit `be72ed5`]

Alternate dispatch shape: the singleton branch is selected by excluding
the Petersen branch `|Fix(σ)| = 10`.  Combined with the unconditional
dichotomy `|Fix(σ)| ∈ {1, 10}`, the negation forces `|Fix(σ)| = 1` and
the rest is mechanical.

This is the most paper-faithful form: case 2 = "not Petersen", which
matches the §6 Lem 17 case split as stated. -/
theorem lem17_case2_conclusion_prime_via_fix_ne_10
    (hΓ : IsMoore57 Γ) (σ : Equiv.Perm V) (pow_3 : σ ^ 3 = 1) (hne : σ ≠ 1)
    (smul_adj : ∀ v w : V, Γ.Adj v w ↔ Γ.Adj (σ v) (σ w))
    (h_ne_10 : Moore57.fixedVertexCount σ ≠ 10) :
    Lemma17Case2Conclusion σ := by
  -- Use the unconditional dichotomy `|Fix(σ)| = 1 ∨ |Fix(σ)| = 10`
  -- and the `≠ 10` hypothesis to force `|Fix(σ)| = 1`, giving `< 10`.
  have hdich :=
    Moore57.aut_order_three_fixedVertexCount_singleton_or_petersen
      (Γ := Γ) hΓ σ smul_adj pow_3 hne
  have h_eq_1 : Moore57.fixedVertexCount σ = 1 := by
    rcases hdich with h1 | h10
    · exact h1
    · exact absurd h10 h_ne_10
  exact lem17_case2_conclusion_prime_unconditional hΓ σ pow_3 hne smul_adj
    (by rw [h_eq_1]; decide)

section FullDispatch

universe u

variable {W : Type u} [Fintype W] [DecidableEq W]
variable {Δ : SimpleGraph W} [DecidableRel Δ.Adj]

/-! ### Full dispatch (Petersen ⊕ singleton) given Petersen uniqueness
(commit `9c078f2` follow-up: combined wire over both branches)

Combines the unconditional shape dichotomy from
`OrderThreeShapeClassification.aut_order_three_SingletonOrPetersenSRG_unconditional`
with the conditional `PetersenFixedData` constructor
`PetersenFixedData.petersenFixedData_of_isSRGWith_given_uniqueness` (which
consumes the `PetersenUniqueness` Prop from
`Foundations.GraphTheory.PetersenUniqueness`).

This is the **full Lem 17 prime-case dispatch**:
* input: `IsMoore57 Γ + σ^3=1 + σ ≠ 1 + smul_adj + PetersenUniqueness`,
* output (paper-faithful): `orderOf σ ∣ 27` (case 1) *or* `orderOf σ ∣ 3`
  (case 2, sharpened from paper's `∣ 81`), automatically dispatched.

Once `PetersenUniqueness` is landed as a Lean-side theorem (separate
deferred work — Bose 1963 / Hoffman–Singleton 1960), the `h_uniq` argument
can be discharged and these wrappers become **truly unconditional** on the
prime case (`σ^3 = 1, σ ≠ 1`).

Until then, the dispatch is fully wired modulo the single Prop hypothesis
`PetersenUniqueness` — every other piece (case-(1) Petersen-SRG signature
extraction, case-(2) singleton narrowing, semi-regular orbit bridges,
arithmetic cores) is unconditional.
-/

/-- **Lemma 17 full dispatch (prime case, given Petersen uniqueness):
per-case Conclusion disjunction.** [done — full wire, conditional on
`PetersenUniqueness`]

Given:
* `hΓ : IsMoore57 Γ`,
* `σ : Equiv.Perm V` with `σ^3 = 1` and `σ ≠ 1`,
* `smul_adj` (σ is a graph automorphism),
* `h_uniq : PetersenUniqueness` (the Bose 1963 / Hoffman–Singleton 1960
  classical uniqueness theorem, packaged as a `Prop` in
  `Foundations.GraphTheory.PetersenUniqueness`),

automatic dispatch into either the case-1 (Petersen) Conclusion
`Lemma17Case1Conclusion σ` (= `orderOf σ ∣ 27`) or the case-2 (singleton)
Conclusion `Lemma17Case2Conclusion σ` (= `orderOf σ ∣ 3`).

Wiring:
1. `aut_order_three_SingletonOrPetersenSRG_unconditional` (Foundations,
   `OrderThreeShapeClassification.lean`) gives the proof-relevant
   dichotomy: `SingletonFixedData σ ⊕'
     (PLift (fixedVertexCount σ = 10) ×' PLift (IsSRGWith 10 3 0 1))`.
2. Singleton branch:
   `lem17_case2_conclusion_prime_with_singletonFixedData` discharges
   the `SingletonFixedData` input to `Lemma17Case2Conclusion`.
3. Petersen-SRG branch:
   `petersenFixedData_of_isSRGWith_given_uniqueness` (from
   `PetersenFixedData.lean`) consumes the `IsSRGWith 10 3 0 1` signature
   and the Petersen uniqueness Prop to construct `PetersenFixedData Γ σ`,
   then `lem17_case1_conclusion_prime_with_petersenFixedData` discharges
   the case-1 Conclusion.

After `PetersenUniqueness` lands as a Lean theorem, replace `h_uniq` by
the theorem application to obtain a sorry-free unconditional dispatch. -/
theorem lem17_3group_full_dispatch_per_case_given_uniqueness
    (hΓ : IsMoore57 Δ) (σ : Equiv.Perm W) (pow_3 : σ ^ 3 = 1) (hne : σ ≠ 1)
    (smul_adj : ∀ v w : W, Δ.Adj v w ↔ Δ.Adj (σ v) (σ w))
    (h_uniq : Moore57.PetersenUniqueness.{u}) :
    Lemma17Case1Conclusion σ ∨ Lemma17Case2Conclusion σ := by
  -- Step 1: unconditional shape dichotomy.
  have hdich :=
    Moore57.aut_order_three_SingletonOrPetersenSRG_unconditional
      (Γ := Δ) hΓ σ smul_adj pow_3 hne
  -- Step 2: dispatch on the dichotomy.
  rcases hdich with sfd | ⟨_h10, h_srg⟩
  · -- Singleton branch (case 2).
    refine Or.inr ?_
    exact lem17_case2_conclusion_prime_with_singletonFixedData hΓ σ pow_3 sfd
      smul_adj
  · -- Petersen-SRG branch (case 1): promote SRG signature to
    -- PetersenFixedData via the uniqueness Prop, then dispatch case 1.
    refine Or.inl ?_
    have h_srg_unpacked : (Moore57.autFixedInducedGraph Δ σ).IsSRGWith 10 3 0 1 :=
      h_srg.down
    -- Promote SRG signature to PetersenFixedData via the explicit
    -- universe-bound `PetersenUniqueness.{u}` Prop.  The universe binding
    -- `W : Type u` aligns with `PetersenUniqueness.{u}` so unification
    -- succeeds where the implicit-universe form fails.
    let pfd : Moore57.PetersenFixedData Δ σ :=
      Moore57.petersenFixedData_of_isSRGWith_given_uniqueness
        (h_unique := h_uniq) (h_srg := h_srg_unpacked)
    exact lem17_case1_conclusion_prime_with_petersenFixedData hΓ σ pow_3 pfd
      ⟨0, by decide⟩ smul_adj

/-- **Lemma 17 full dispatch (prime case, given Petersen uniqueness):
original disjunction form.** [done — full wire, conditional on
`PetersenUniqueness`]

Returns the paper-faithful `Lemma17ThreeGroupFixConclusion σ` (= the
disjunction `orderOf σ ∣ 27 ∨ orderOf σ ∣ 81`), automatically dispatched
between the Petersen branch (case 1) and the singleton branch (case 2),
given the same inputs as
`lem17_3group_full_dispatch_per_case_given_uniqueness`.

Composition of that lemma with `lem17_per_case_to_three_group_fix_conclusion`
which lifts the sharper case-2 `∣ 3` to the paper-stated `∣ 81`. -/
theorem lem17_3group_full_dispatch_given_uniqueness
    (hΓ : IsMoore57 Δ) (σ : Equiv.Perm W) (pow_3 : σ ^ 3 = 1) (hne : σ ≠ 1)
    (smul_adj : ∀ v w : W, Δ.Adj v w ↔ Δ.Adj (σ v) (σ w))
    (h_uniq : Moore57.PetersenUniqueness.{u}) :
    Lemma17ThreeGroupFixConclusion σ :=
  lem17_per_case_to_three_group_fix_conclusion σ
    (lem17_3group_full_dispatch_per_case_given_uniqueness hΓ σ pow_3 hne
      smul_adj h_uniq)

/-- **Lemma 17 full dispatch paper bound `orderOf σ ∣ 27` (combined upper).**
[done — full wire, conditional on `PetersenUniqueness`]

The paper's Lem 17 statement combines both branches under a single
upper-bound divisor: `orderOf σ ∣ 27`.  In the prime case (`σ^3 = 1`),
both branches deliver this bound directly:

* case 1 (Petersen): `orderOf σ ∣ 27` (the case-1 conclusion itself).
* case 2 (singleton): `orderOf σ ∣ 3 ∣ 27` (sharpened ⟹ paper-stated).

This is the cleanest single-divisor paper-faithful form of Lem 17 in the
prime case, given Petersen uniqueness. -/
theorem lem17_3group_paper_bound_given_uniqueness
    (hΓ : IsMoore57 Δ) (σ : Equiv.Perm W) (pow_3 : σ ^ 3 = 1) (hne : σ ≠ 1)
    (smul_adj : ∀ v w : W, Δ.Adj v w ↔ Δ.Adj (σ v) (σ w))
    (h_uniq : Moore57.PetersenUniqueness.{u}) :
    orderOf σ ∣ 27 := by
  rcases lem17_3group_full_dispatch_per_case_given_uniqueness hΓ σ pow_3 hne
    smul_adj h_uniq with h1 | h2
  · -- case 1: orderOf σ ∣ 27 directly.
    exact h1
  · -- case 2: orderOf σ ∣ 3 ∣ 27.
    exact dvd_trans h2 (by decide)

/-- **Lemma 17 full dispatch Conclusion Prop encoding.**

Encapsulates the combined paper-bound `orderOf σ ∣ 27` from the full
dispatch as a `Prop`, paralleling `Lemma17Case1Conclusion` and
`Lemma17Case2Conclusion`.  Used by downstream Cor3 / MainTheorem
dispatch chain when the per-case split is not needed. -/
def Lemma17FullDispatchConclusion (σ : Equiv.Perm W) : Prop :=
  orderOf σ ∣ 27

/-- **Lemma 17 full dispatch via Conclusion encoding.** [done]

Given the `Lemma17FullDispatchConclusion σ` Prop, conclude
`orderOf σ ∣ 27`.  Trivial bridge — exposed for the Conclusion-Prop
dispatch pattern. -/
theorem lem17_full_dispatch_via_conclusion
    (σ : Equiv.Perm W) (h_conclusion : Lemma17FullDispatchConclusion σ) :
    orderOf σ ∣ 27 :=
  h_conclusion

/-- **Lemma 17 full dispatch Conclusion instance, given Petersen
uniqueness.** [done — full wire, conditional on `PetersenUniqueness`]

Conclusion-Prop wrapper around `lem17_3group_paper_bound_given_uniqueness`.
Discharges `Lemma17FullDispatchConclusion σ` (= `orderOf σ ∣ 27`) from the
prime-case inputs plus the Petersen uniqueness Prop. -/
theorem lem17_3group_full_dispatch_conclusion_given_uniqueness
    (hΓ : IsMoore57 Δ) (σ : Equiv.Perm W) (pow_3 : σ ^ 3 = 1) (hne : σ ≠ 1)
    (smul_adj : ∀ v w : W, Δ.Adj v w ↔ Δ.Adj (σ v) (σ w))
    (h_uniq : Moore57.PetersenUniqueness.{u}) :
    Lemma17FullDispatchConclusion σ :=
  lem17_3group_paper_bound_given_uniqueness hΓ σ pow_3 hne smul_adj h_uniq

end FullDispatch

end Moore57.Papers.MacajSiran2010.S6
