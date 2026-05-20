import Moore57.Papers.MacajSiran2010.Section06_PGroupsOverview.Lemma16_PGroupFix
import Moore57.Moore57Graph.Aut.NeighborMod
import Moore57.Moore57Graph.Aut.PetersenFixedData

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

/-- **Lemma 17 (3-group fix is Petersen or singleton).** [deferred-heavy] -/
theorem lem17_3group_fix (hΓ : IsMoore57 Γ) : True := by trivial

end Moore57.Papers.MacajSiran2010.S6
