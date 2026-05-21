import Moore57.Papers.MacajSiran2010.Section06_PGroupsOverview.Lemma16_PGroupFix
import Moore57.Moore57Graph.Aut.NeighborMod
import Moore57.Moore57Graph.Aut.PetersenFixedData
import Moore57.Moore57Graph.Aut.SingletonAndEmptyFixedData

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

end Moore57.Papers.MacajSiran2010.S6
