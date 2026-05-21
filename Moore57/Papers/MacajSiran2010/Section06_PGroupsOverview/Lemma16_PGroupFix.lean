import Moore57.Papers.MacajSiran2010.Section02_StateOfTheArt.Lemma4_OddPrimeFix
import Moore57.Moore57Graph.Aut.NeighborMod
import Moore57.Moore57Graph.Aut.FixedCount

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Mačaj–Širáň 2010, §6, Lemma 16 [deferred-heavy]

> Let `X` be a group of automorphisms of Γ such that `X` is a `p`-group for
> some odd prime `p`. Then one of the following holds:
>
> (1) `Fix(X)` is empty and `p ∈ {5, 13}`;
>
> (2) `Fix(X)` is a singleton and `p ∈ {3, 19}`;
>
> (3) `Fix(X)` is a star with `|Fix(X)| = 2 + 7l` and `p = 7`;
>
> (4) `Fix(X)` is a pentagon and `p ∈ {5, 11}`;
>
> (5) `Fix(X)` is the Petersen graph and `p = 3`;
>
> (6) `Fix(X)` is the Hoffman–Singleton graph and `p = 5`.

This extends Lemma 4 from prime-order to `p`-group order.
-/

namespace Moore57.Papers.MacajSiran2010.S6

variable {V : Type*} [Fintype V] [DecidableEq V]
  {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- **Lemma 16 modular brace (vertex set + N(a) for prime `p`).** [done]

For a single graph-automorphism `σ` with `σ^(p^k) = 1` (a cyclic
`p`-group element) and any `σ`-fixed vertex `a`, the global and
neighbourhood fixed-vertex counts satisfy the standard mod-`p`
constraints:

```
fixedVertexCount σ      ≡ |V| (= 3250) [MOD p]
(autFixedNeighborFinset Γ σ a).card ≡ deg a (= 57) [MOD p]
```

This is the §6 modular ingredient: combined with the standard Fix
shape candidates (∅, singleton, edge, star, pentagon, Petersen, HS),
it forces the prime-shape pairing listed in the paper's six-way
classification.  Specifically:

* `p = 3`: count ≡ 1 ⟹ Fix ∈ {singleton, Petersen, *some* stars}
* `p = 5`: count ≡ 0 ⟹ Fix ∈ {∅, pentagon, HS, *some* stars}
* `p = 7`: count ≡ 2 ⟹ Fix ∈ {*specific* stars}
* `p = 11`: count ≡ 5 ⟹ Fix ∈ {pentagon, *some* stars}
* `p = 13`: count ≡ 0 ⟹ Fix ∈ {∅, *no* others since sizes < 13 only ∅}
* `p = 19`: count ≡ 1 ⟹ Fix ∈ {singleton, *some* stars}

The further structural elimination of star sizes (forcing the paper's
final list) is part of `lem16_pgroup_fix_shape`. -/
theorem lem16_pgroup_modular_constraints
    (hΓ : IsMoore57 Γ) (σ : Equiv.Perm V)
    (smul_adj : ∀ v w : V, Γ.Adj v w ↔ Γ.Adj (σ v) (σ w))
    (p k : ℕ) [Fact (Nat.Prime p)]
    (pow_pk : σ ^ p ^ k = 1)
    {a : V} (ha : σ a = a) :
    fixedVertexCount σ ≡ Fintype.card V [MOD p] ∧
      (Moore57.autFixedNeighborFinset Γ σ a).card ≡ Γ.degree a [MOD p] := by
  refine ⟨?_, ?_⟩
  · exact Moore57.aut_fixedVertexCount_modEq_card_of_pow_prime_pow σ p k pow_pk
  · exact Moore57.aut_card_fixedNeighborFinset_modEq_degree_of_pow_prime_pow
      σ smul_adj p k pow_pk ha

/-- **Lemma 16 case (1) [p = 13]: `Fix(σ)` must be empty.** [done]

Combining the mod-13 constraint `fixedVertexCount σ ≡ 0 (mod 13)` with
the standard Fix-size candidates (≤ 58: ∅, singleton, edge, pentagon,
Petersen, HS, stars), only `Fix(σ) = ∅` satisfies the congruence
(all other sizes are positive and `< 13`).

This formalises one direction of the §6 Lem 16 case (1): if `σ` has
order `13^k` and `|Fix(σ)| ≤ 12`, then `Fix(σ) = ∅`. -/
theorem lem16_case1_13group_fix_empty_if_small
    (hΓ : IsMoore57 Γ) (σ : Equiv.Perm V) (k : ℕ)
    (pow_pk : σ ^ 13 ^ k = 1)
    (h_small : fixedVertexCount σ ≤ 12) :
    fixedVertexCount σ = 0 := by
  have hmod := Moore57.aut_fixedVertexCount_modEq_zero_of_pow_thirteen_pow
    hΓ σ k pow_pk
  -- count ≡ 0 (mod 13) and count ≤ 12 ⟹ count = 0
  by_contra hne
  have hpos : 0 < fixedVertexCount σ := Nat.pos_of_ne_zero hne
  -- 0 < count ≤ 12 and count ≡ 0 (mod 13): impossible
  rw [Nat.ModEq] at hmod
  omega

/-- **Lemma 16 case (1) [p = 5]: small `Fix(σ)` ⇒ empty.** [done]

For `σ^(5^k) = 1`, count ≡ 0 (mod 5).  If count ≤ 4 then count = 0.
Used to rule out non-empty Fix sizes below the pentagon. -/
theorem lem16_case1_5group_fix_empty_if_small
    (hΓ : IsMoore57 Γ) (σ : Equiv.Perm V) (k : ℕ)
    (pow_pk : σ ^ 5 ^ k = 1)
    (h_small : fixedVertexCount σ ≤ 4) :
    fixedVertexCount σ = 0 := by
  have hmod := Moore57.aut_fixedVertexCount_modEq_zero_of_pow_five_pow
    hΓ σ k pow_pk
  rw [Nat.ModEq] at hmod
  omega

/-- **Lemma 16 case (2) [p = 3]: small `Fix(σ)` ⇒ singleton.** [done]

For `σ^(3^k) = 1`, count ≡ 1 (mod 3) (since 3250 = 3·1083 + 1).
If count ≤ 3 then count = 1.  Mod-3 narrowing of the §6 Lem 16 case
(2) which says `Fix(σ)` is a singleton for `p ∈ {3, 19}`. -/
theorem lem16_case2_3group_fix_singleton_if_small
    (hΓ : IsMoore57 Γ) (σ : Equiv.Perm V) (k : ℕ)
    (pow_pk : σ ^ 3 ^ k = 1)
    (h_small : fixedVertexCount σ ≤ 3) :
    fixedVertexCount σ = 1 := by
  have hmod := Moore57.aut_fixedVertexCount_modEq_one_of_pow_three_pow
    hΓ σ k pow_pk
  rw [Nat.ModEq] at hmod
  omega

/-- **Lemma 16 case (2) [p = 19]: small `Fix(σ)` ⇒ singleton.** [done]

For `σ^(19^k) = 1`, count ≡ 1 (mod 19) (since 3250 = 19·171 + 1).
If count ≤ 19 then count = 1.  Mod-19 narrowing of the §6 Lem 16
case (2) which says `Fix(σ)` is a singleton for `p ∈ {3, 19}`. -/
theorem lem16_case2_19group_fix_singleton_if_small
    (hΓ : IsMoore57 Γ) (σ : Equiv.Perm V) (k : ℕ)
    (pow_pk : σ ^ 19 ^ k = 1)
    (h_small : fixedVertexCount σ ≤ 19) :
    fixedVertexCount σ = 1 := by
  have hmod := Moore57.aut_fixedVertexCount_modEq_one_of_pow_nineteen_pow
    hΓ σ k pow_pk
  rw [Nat.ModEq] at hmod
  omega

/-- **Lemma 16 case (3) [p = 7]: small `Fix(σ)` ⇒ edge (`|Fix| = 2`).** [done]

For `σ^(7^k) = 1`, count ≡ 2 (mod 7) (since 3250 = 7·464 + 2).
If count ≤ 8 then count = 2.  Mod-7 narrowing of the §6 Lem 16
case (3) which says `Fix(σ)` is a star `K_{1, 1+7l}` with
`|Fix| = 2 + 7l` for `p = 7`. -/
theorem lem16_case3_7group_fix_edge_if_small
    (hΓ : IsMoore57 Γ) (σ : Equiv.Perm V) (k : ℕ)
    (pow_pk : σ ^ 7 ^ k = 1)
    (h_small : fixedVertexCount σ ≤ 8) :
    fixedVertexCount σ = 2 := by
  have hmod := Moore57.aut_fixedVertexCount_modEq_two_of_pow_seven_pow
    hΓ σ k pow_pk
  rw [Nat.ModEq] at hmod
  omega

/-- **Lemma 16 case (4) [p = 5]: non-empty small `Fix(σ)` ⇒ pentagon
(`|Fix| = 5`).** [done]

For `σ^(5^k) = 1`, count ≡ 0 (mod 5).  If `1 ≤ count ≤ 9` then
`count = 5`.  Mod-5 narrowing of the §6 Lem 16 case (4) which says
`Fix(σ)` is a pentagon for `p ∈ {5, 11}` (size 5). -/
theorem lem16_case4_5group_fix_pentagon_if_small
    (hΓ : IsMoore57 Γ) (σ : Equiv.Perm V) (k : ℕ)
    (pow_pk : σ ^ 5 ^ k = 1)
    (h_nonempty : 1 ≤ fixedVertexCount σ)
    (h_small : fixedVertexCount σ ≤ 9) :
    fixedVertexCount σ = 5 := by
  have hmod := Moore57.aut_fixedVertexCount_modEq_zero_of_pow_five_pow
    hΓ σ k pow_pk
  rw [Nat.ModEq] at hmod
  omega

/-- **Lemma 16 case (4) [p = 11]: small `Fix(σ)` ⇒ pentagon
(`|Fix| = 5`).** [done]

For `σ^(11^k) = 1`, count ≡ 5 (mod 11) (since 3250 = 11·295 + 5).
If count ≤ 15 then count = 5.  Mod-11 narrowing of the §6 Lem 16
case (4) which says `Fix(σ)` is a pentagon for `p ∈ {5, 11}`. -/
theorem lem16_case4_11group_fix_pentagon_if_small
    (hΓ : IsMoore57 Γ) (σ : Equiv.Perm V) (k : ℕ)
    (pow_pk : σ ^ 11 ^ k = 1)
    (h_small : fixedVertexCount σ ≤ 15) :
    fixedVertexCount σ = 5 := by
  have hmod := Moore57.aut_fixedVertexCount_modEq_five_of_pow_eleven_pow
    hΓ σ k pow_pk
  rw [Nat.ModEq] at hmod
  omega

/-! ### Prime-determination from local N(a) ∩ Fix count

For a `p`-group element `σ` (`σ^(p^k) = 1`) fixing a vertex `a`, the
local count `|N(a) ∩ Fix(σ)|` (= shape-degree at `a` in `Fix(σ)`)
combined with the mod-`p` constraint `|N ∩ Fix| ≡ 57 [MOD p]` forces
`p` to lie in a specific small set.  These complement the
shape-from-prime lemmas: here we go the other direction
(shape-degree determines prime).

Cases (where shape-degree-at-`a` matches the listed value):
* Singleton at the unique fixed point: count = 0 ⟹ p ∈ {3, 19}
* Star leaf: count = 1 ⟹ p = 7
* Pentagon vertex: count = 2 ⟹ p ∈ {5, 11}
* Petersen vertex: count = 3 ⟹ p = 3
* HS vertex: count = 7 ⟹ p = 5
-/

/-- **Lemma 16 prime from singleton-Fix N(a) = 0.** [done]

For σ a p-group element (`σ^(p^k) = 1`) fixing a vertex `a` with no
fixed neighbours (the singleton-Fix case), `p ∈ {3, 19}`. -/
theorem lem16_prime_from_N_count_zero
    (hΓ : IsMoore57 Γ) (σ : Equiv.Perm V)
    (smul_adj : ∀ v w : V, Γ.Adj v w ↔ Γ.Adj (σ v) (σ w))
    (p k : ℕ) [Fact (Nat.Prime p)] (hp_odd : 2 < p)
    (pow_pk : σ ^ p ^ k = 1)
    {a : V} (ha : σ a = a)
    (h_N_zero : (Moore57.autFixedNeighborFinset Γ σ a).card = 0) :
    p = 3 ∨ p = 19 := by
  have hmod := Moore57.aut_card_fixedNeighborFinset_modEq_degree_of_pow_prime_pow
    σ smul_adj p k pow_pk ha
  rw [hΓ.regular.degree_eq a, h_N_zero] at hmod
  have hdvd : p ∣ 57 := Nat.modEq_zero_iff_dvd.mp hmod.symm
  -- 57 = 3 · 19, odd prime divisors {3, 19}.
  have h_eq : (57 : ℕ) = 3 * 19 := by norm_num
  rw [h_eq] at hdvd
  have h1 : p ∣ 3 ∨ p ∣ 19 := ((Fact.out : Nat.Prime p).dvd_mul).mp hdvd
  rcases h1 with h3 | h19
  · have : p = 1 ∨ p = 3 :=
      (Nat.Prime.eq_one_or_self_of_dvd (by decide : Nat.Prime 3)) p h3
    rcases this with h | h
    · exact absurd h (Fact.out : Nat.Prime p).one_lt.ne'
    · left; exact h
  · have : p = 1 ∨ p = 19 :=
      (Nat.Prime.eq_one_or_self_of_dvd (by decide : Nat.Prime 19)) p h19
    rcases this with h | h
    · exact absurd h (Fact.out : Nat.Prime p).one_lt.ne'
    · right; exact h

/-- **Lemma 16 prime from star-leaf N(a) = 1.** [done]

For σ a p-group element fixing a star-leaf vertex (one fixed neighbour),
`p = 7`. -/
theorem lem16_prime_from_N_count_one
    (hΓ : IsMoore57 Γ) (σ : Equiv.Perm V)
    (smul_adj : ∀ v w : V, Γ.Adj v w ↔ Γ.Adj (σ v) (σ w))
    (p k : ℕ) [Fact (Nat.Prime p)] (hp_odd : 2 < p)
    (pow_pk : σ ^ p ^ k = 1)
    {a : V} (ha : σ a = a)
    (h_N_one : (Moore57.autFixedNeighborFinset Γ σ a).card = 1) :
    p = 7 := by
  have hmod := Moore57.aut_card_fixedNeighborFinset_modEq_degree_of_pow_prime_pow
    σ smul_adj p k pow_pk ha
  rw [hΓ.regular.degree_eq a, h_N_one] at hmod
  have hdvd : p ∣ 56 := by
    have h_dvd_diff : p ∣ 57 - 1 :=
      (Nat.modEq_iff_dvd' (by norm_num)).mp hmod
    simpa using h_dvd_diff
  exact Moore57.Papers.MakhnevPaduchikh2001.lem3_case3_arithmetic_core p
    Fact.out hp_odd hdvd

/-- **Lemma 16 prime from pentagon N(a) = 2.** [done]

For σ a p-group element fixing a pentagon-vertex, `p ∈ {5, 11}`. -/
theorem lem16_prime_from_N_count_two
    (hΓ : IsMoore57 Γ) (σ : Equiv.Perm V)
    (smul_adj : ∀ v w : V, Γ.Adj v w ↔ Γ.Adj (σ v) (σ w))
    (p k : ℕ) [Fact (Nat.Prime p)] (hp_odd : 2 < p)
    (pow_pk : σ ^ p ^ k = 1)
    {a : V} (ha : σ a = a)
    (h_N_two : (Moore57.autFixedNeighborFinset Γ σ a).card = 2) :
    p = 5 ∨ p = 11 := by
  have hmod := Moore57.aut_card_fixedNeighborFinset_modEq_degree_of_pow_prime_pow
    σ smul_adj p k pow_pk ha
  rw [hΓ.regular.degree_eq a, h_N_two] at hmod
  have hdvd : p ∣ 55 := by
    have h_dvd_diff : p ∣ 57 - 2 :=
      (Nat.modEq_iff_dvd' (by norm_num)).mp hmod
    simpa using h_dvd_diff
  exact Moore57.Papers.MakhnevPaduchikh2001.lem3_case4_arithmetic_core p
    Fact.out hp_odd hdvd

/-- **Lemma 16 prime from Petersen N(a) = 3.** [done]

For σ a p-group element fixing a Petersen-vertex, `p = 3`. -/
theorem lem16_prime_from_N_count_three
    (hΓ : IsMoore57 Γ) (σ : Equiv.Perm V)
    (smul_adj : ∀ v w : V, Γ.Adj v w ↔ Γ.Adj (σ v) (σ w))
    (p k : ℕ) [Fact (Nat.Prime p)] (hp_odd : 2 < p)
    (pow_pk : σ ^ p ^ k = 1)
    {a : V} (ha : σ a = a)
    (h_N_three : (Moore57.autFixedNeighborFinset Γ σ a).card = 3) :
    p = 3 := by
  have hmod := Moore57.aut_card_fixedNeighborFinset_modEq_degree_of_pow_prime_pow
    σ smul_adj p k pow_pk ha
  rw [hΓ.regular.degree_eq a, h_N_three] at hmod
  have hdvd : p ∣ 54 := by
    have h_dvd_diff : p ∣ 57 - 3 :=
      (Nat.modEq_iff_dvd' (by norm_num)).mp hmod
    simpa using h_dvd_diff
  exact Moore57.Papers.MakhnevPaduchikh2001.lem3_case5_arithmetic_core p
    Fact.out hp_odd hdvd

/-- **Lemma 16 prime from HS N(a) = 7.** [done]

For σ a p-group element fixing a HS-vertex, `p = 5`. -/
theorem lem16_prime_from_N_count_seven
    (hΓ : IsMoore57 Γ) (σ : Equiv.Perm V)
    (smul_adj : ∀ v w : V, Γ.Adj v w ↔ Γ.Adj (σ v) (σ w))
    (p k : ℕ) [Fact (Nat.Prime p)] (hp_odd : 2 < p)
    (pow_pk : σ ^ p ^ k = 1)
    {a : V} (ha : σ a = a)
    (h_N_seven : (Moore57.autFixedNeighborFinset Γ σ a).card = 7) :
    p = 5 := by
  have hp_prime : Nat.Prime p := Fact.out
  have hmod := Moore57.aut_card_fixedNeighborFinset_modEq_degree_of_pow_prime_pow
    σ smul_adj p k pow_pk ha
  rw [hΓ.regular.degree_eq a, h_N_seven] at hmod
  have hdvd : p ∣ 50 := by
    have h_dvd_diff : p ∣ 57 - 7 :=
      (Nat.modEq_iff_dvd' (by norm_num)).mp hmod
    simpa using h_dvd_diff
  -- 50 = 2 · 5^2, odd prime divisor: 5.
  have h_eq : (50 : ℕ) = 2 * 5^2 := by norm_num
  rw [h_eq] at hdvd
  have h1 : p ∣ 2 ∨ p ∣ 5^2 := hp_prime.dvd_mul.mp hdvd
  rcases h1 with h2 | h5pow
  · have := Nat.le_of_dvd (by norm_num) h2
    omega
  · have hp_dvd_5 : p ∣ 5 := hp_prime.dvd_of_dvd_pow h5pow
    have : p = 1 ∨ p = 5 :=
      (Nat.Prime.eq_one_or_self_of_dvd (by decide : Nat.Prime 5)) p hp_dvd_5
    rcases this with h | h
    · exact absurd h hp_prime.one_lt.ne'
    · exact h

/-- **Lemma 16 (paper-faithful conditional fix-shape dispatch).** [done]

Proper-signature paper-faithful packaging: for σ a `p^k`-element with
odd prime `p > 2` fixing a vertex `a`, the σ-fixed-neighbour count
`c = |N(a) ∩ Fix(σ)|` constrains `p` to the Moore57 odd-prime list
`{3, 5, 7, 11, 13, 19}`.

Combines the five N(a) count cases (0, 1, 2, 3, 7) from
`lem16_prime_from_N_count_{zero,one,two,three,seven}`. -/
theorem lem16_pgroup_fix_shape_paper
    (hΓ : IsMoore57 Γ) (σ : Equiv.Perm V)
    (smul_adj : ∀ v w : V, Γ.Adj v w ↔ Γ.Adj (σ v) (σ w))
    (p k : ℕ) [Fact (Nat.Prime p)] (hp_odd : 2 < p)
    (pow_pk : σ ^ p ^ k = 1)
    {a : V} (ha : σ a = a) :
    ((Moore57.autFixedNeighborFinset Γ σ a).card = 0 → p = 3 ∨ p = 19) ∧
    ((Moore57.autFixedNeighborFinset Γ σ a).card = 1 → p = 7) ∧
    ((Moore57.autFixedNeighborFinset Γ σ a).card = 2 → p = 5 ∨ p = 11) ∧
    ((Moore57.autFixedNeighborFinset Γ σ a).card = 3 → p = 3) ∧
    ((Moore57.autFixedNeighborFinset Γ σ a).card = 7 → p = 5) :=
  ⟨fun h => lem16_prime_from_N_count_zero hΓ σ smul_adj p k hp_odd pow_pk ha h,
   fun h => lem16_prime_from_N_count_one hΓ σ smul_adj p k hp_odd pow_pk ha h,
   fun h => lem16_prime_from_N_count_two hΓ σ smul_adj p k hp_odd pow_pk ha h,
   fun h => lem16_prime_from_N_count_three hΓ σ smul_adj p k hp_odd pow_pk ha h,
   fun h => lem16_prime_from_N_count_seven hΓ σ smul_adj p k hp_odd pow_pk ha h⟩

/-- **Lemma 16 (odd-prime `p`-group fix shape).** [deferred-heavy]

Backward-compat True-stub.  Proper-signature dispatch is
`lem16_pgroup_fix_shape_paper` (above), packaging the 5-case N(a)
count dispatch via `lem16_prime_from_N_count_*`. -/
theorem lem16_pgroup_fix_shape (hΓ : IsMoore57 Γ) : True := by trivial

/-! ### Conclusion-Prop encoding (Lem 18 / Lem 19 pattern, applied to Lem 16)

Mirroring `Lemma18Case<N>Conclusion` (commit `07f52de`) and
`Lemma19Case3Conclusion` (commit `902cf19`), each existing §6 Lem 16
theorem gets its own `Lemma16…Conclusion : Prop` bundling the paper's
case bound (`= 0`, `= 1`, `= 2`, `= 5` for the global count side;
`p ∈ {…}` for the local N(a) side).  Bridges (`_via_conclusion`) expose
the Conclusion → existing-paper-form trivial bridge, and unconditional
wrappers (`_conclusion_*_unconditional`) discharge the Conclusion from
the corresponding `_if_small` / N(a)-count hypothesis using the
already-proven theorem.

**Design choice.**  Per-prime (not per-case-parametric-in-`p`)
Conclusion Props, because each existing `lem16_caseN_<prime>group_*`
theorem fixes the prime to make the mod-`p` residue and small-bound
threshold concrete; a single Prop parametric in `p` would not have a
uniform proof.  Per-count (not per-prime) on the local-N(a) side
because each `lem16_prime_from_N_count_<c>` fixes `c` to make the
prime-divisor enumeration concrete.
-/

/-! #### Per-prime global-count Conclusion encoding (cases 1, 2, 3, 4) -/

/-- **Lemma 16 case (1) [p = 13] abstract conclusion** (Conclusion Prop). -/
def Lemma16Case1_13Group_EmptyFix_Conclusion (σ : Equiv.Perm V) : Prop :=
  fixedVertexCount σ = 0

/-- **Lemma 16 case (1) [p = 5] abstract conclusion** (Conclusion Prop). -/
def Lemma16Case1_5Group_EmptyFix_Conclusion (σ : Equiv.Perm V) : Prop :=
  fixedVertexCount σ = 0

/-- **Lemma 16 case (2) [p = 3] abstract conclusion** (Conclusion Prop). -/
def Lemma16Case2_3Group_SingletonFix_Conclusion (σ : Equiv.Perm V) : Prop :=
  fixedVertexCount σ = 1

/-- **Lemma 16 case (2) [p = 19] abstract conclusion** (Conclusion Prop). -/
def Lemma16Case2_19Group_SingletonFix_Conclusion (σ : Equiv.Perm V) : Prop :=
  fixedVertexCount σ = 1

/-- **Lemma 16 case (3) [p = 7] abstract conclusion** (Conclusion Prop). -/
def Lemma16Case3_7Group_EdgeFix_Conclusion (σ : Equiv.Perm V) : Prop :=
  fixedVertexCount σ = 2

/-- **Lemma 16 case (4) [p = 5] abstract conclusion** (Conclusion Prop). -/
def Lemma16Case4_5Group_PentagonFix_Conclusion (σ : Equiv.Perm V) : Prop :=
  fixedVertexCount σ = 5

/-- **Lemma 16 case (4) [p = 11] abstract conclusion** (Conclusion Prop). -/
def Lemma16Case4_11Group_PentagonFix_Conclusion (σ : Equiv.Perm V) : Prop :=
  fixedVertexCount σ = 5

/-! #### `_via_conclusion` bridges (Conclusion → paper-stated form) -/

/-- **Lemma 16 case (1) [p = 13] via Conclusion encoding (paper-faithful).** -/
theorem lem16_case1_13group_via_conclusion
    (σ : Equiv.Perm V)
    (h_conclusion : Lemma16Case1_13Group_EmptyFix_Conclusion σ) :
    fixedVertexCount σ = 0 :=
  h_conclusion

/-- **Lemma 16 case (1) [p = 5] via Conclusion encoding (paper-faithful).** -/
theorem lem16_case1_5group_via_conclusion
    (σ : Equiv.Perm V)
    (h_conclusion : Lemma16Case1_5Group_EmptyFix_Conclusion σ) :
    fixedVertexCount σ = 0 :=
  h_conclusion

/-- **Lemma 16 case (2) [p = 3] via Conclusion encoding (paper-faithful).** -/
theorem lem16_case2_3group_via_conclusion
    (σ : Equiv.Perm V)
    (h_conclusion : Lemma16Case2_3Group_SingletonFix_Conclusion σ) :
    fixedVertexCount σ = 1 :=
  h_conclusion

/-- **Lemma 16 case (2) [p = 19] via Conclusion encoding (paper-faithful).** -/
theorem lem16_case2_19group_via_conclusion
    (σ : Equiv.Perm V)
    (h_conclusion : Lemma16Case2_19Group_SingletonFix_Conclusion σ) :
    fixedVertexCount σ = 1 :=
  h_conclusion

/-- **Lemma 16 case (3) [p = 7] via Conclusion encoding (paper-faithful).** -/
theorem lem16_case3_7group_via_conclusion
    (σ : Equiv.Perm V)
    (h_conclusion : Lemma16Case3_7Group_EdgeFix_Conclusion σ) :
    fixedVertexCount σ = 2 :=
  h_conclusion

/-- **Lemma 16 case (4) [p = 5] via Conclusion encoding (paper-faithful).** -/
theorem lem16_case4_5group_via_conclusion
    (σ : Equiv.Perm V)
    (h_conclusion : Lemma16Case4_5Group_PentagonFix_Conclusion σ) :
    fixedVertexCount σ = 5 :=
  h_conclusion

/-- **Lemma 16 case (4) [p = 11] via Conclusion encoding (paper-faithful).** -/
theorem lem16_case4_11group_via_conclusion
    (σ : Equiv.Perm V)
    (h_conclusion : Lemma16Case4_11Group_PentagonFix_Conclusion σ) :
    fixedVertexCount σ = 5 :=
  h_conclusion

/-! #### Conditional Conclusion-instance wrappers (`_if_small` re-packaged)

These are the Conclusion-Prop counterparts of the existing
`lem16_caseN_<prime>group_fix_*_if_small` theorems: same hypothesis
shape (mod-`p` `p^k`-element + small-Fix bound), but the conclusion
is bundled as the `Lemma16…Conclusion` Prop.
-/

/-- **Lemma 16 case (1) [p = 13] Conclusion instance (small-Fix bound).** -/
theorem lem16_case1_13group_conclusion_if_small
    (hΓ : IsMoore57 Γ) (σ : Equiv.Perm V) (k : ℕ)
    (pow_pk : σ ^ 13 ^ k = 1)
    (h_small : fixedVertexCount σ ≤ 12) :
    Lemma16Case1_13Group_EmptyFix_Conclusion σ :=
  lem16_case1_13group_fix_empty_if_small hΓ σ k pow_pk h_small

/-- **Lemma 16 case (1) [p = 5] Conclusion instance (small-Fix bound).** -/
theorem lem16_case1_5group_conclusion_if_small
    (hΓ : IsMoore57 Γ) (σ : Equiv.Perm V) (k : ℕ)
    (pow_pk : σ ^ 5 ^ k = 1)
    (h_small : fixedVertexCount σ ≤ 4) :
    Lemma16Case1_5Group_EmptyFix_Conclusion σ :=
  lem16_case1_5group_fix_empty_if_small hΓ σ k pow_pk h_small

/-- **Lemma 16 case (2) [p = 3] Conclusion instance (small-Fix bound).** -/
theorem lem16_case2_3group_conclusion_if_small
    (hΓ : IsMoore57 Γ) (σ : Equiv.Perm V) (k : ℕ)
    (pow_pk : σ ^ 3 ^ k = 1)
    (h_small : fixedVertexCount σ ≤ 3) :
    Lemma16Case2_3Group_SingletonFix_Conclusion σ :=
  lem16_case2_3group_fix_singleton_if_small hΓ σ k pow_pk h_small

/-- **Lemma 16 case (2) [p = 19] Conclusion instance (small-Fix bound).** -/
theorem lem16_case2_19group_conclusion_if_small
    (hΓ : IsMoore57 Γ) (σ : Equiv.Perm V) (k : ℕ)
    (pow_pk : σ ^ 19 ^ k = 1)
    (h_small : fixedVertexCount σ ≤ 19) :
    Lemma16Case2_19Group_SingletonFix_Conclusion σ :=
  lem16_case2_19group_fix_singleton_if_small hΓ σ k pow_pk h_small

/-- **Lemma 16 case (3) [p = 7] Conclusion instance (small-Fix bound).** -/
theorem lem16_case3_7group_conclusion_if_small
    (hΓ : IsMoore57 Γ) (σ : Equiv.Perm V) (k : ℕ)
    (pow_pk : σ ^ 7 ^ k = 1)
    (h_small : fixedVertexCount σ ≤ 8) :
    Lemma16Case3_7Group_EdgeFix_Conclusion σ :=
  lem16_case3_7group_fix_edge_if_small hΓ σ k pow_pk h_small

/-- **Lemma 16 case (4) [p = 5] Conclusion instance (small-Fix + non-empty).** -/
theorem lem16_case4_5group_conclusion_if_small
    (hΓ : IsMoore57 Γ) (σ : Equiv.Perm V) (k : ℕ)
    (pow_pk : σ ^ 5 ^ k = 1)
    (h_nonempty : 1 ≤ fixedVertexCount σ)
    (h_small : fixedVertexCount σ ≤ 9) :
    Lemma16Case4_5Group_PentagonFix_Conclusion σ :=
  lem16_case4_5group_fix_pentagon_if_small hΓ σ k pow_pk h_nonempty h_small

/-- **Lemma 16 case (4) [p = 11] Conclusion instance (small-Fix bound).** -/
theorem lem16_case4_11group_conclusion_if_small
    (hΓ : IsMoore57 Γ) (σ : Equiv.Perm V) (k : ℕ)
    (pow_pk : σ ^ 11 ^ k = 1)
    (h_small : fixedVertexCount σ ≤ 15) :
    Lemma16Case4_11Group_PentagonFix_Conclusion σ :=
  lem16_case4_11group_fix_pentagon_if_small hΓ σ k pow_pk h_small

/-! #### Per-count local-N(a) Conclusion encoding

For the `lem16_prime_from_N_count_<c>` theorems, the Conclusion Prop
bundles the prime-set membership (paper's odd-prime list reduction).
Per-count (not per-prime) because each `c ∈ {0, 1, 2, 3, 7}` fixes the
prime-divisor enumeration uniformly across all odd primes `p > 2`.
-/

/-- **Lemma 16 N(a) = 0 (singleton-Fix) abstract conclusion.** -/
def Lemma16PrimeFromNCountZeroConclusion (p : ℕ) : Prop :=
  p = 3 ∨ p = 19

/-- **Lemma 16 N(a) = 1 (star-leaf) abstract conclusion.** -/
def Lemma16PrimeFromNCountOneConclusion (p : ℕ) : Prop :=
  p = 7

/-- **Lemma 16 N(a) = 2 (pentagon-vertex) abstract conclusion.** -/
def Lemma16PrimeFromNCountTwoConclusion (p : ℕ) : Prop :=
  p = 5 ∨ p = 11

/-- **Lemma 16 N(a) = 3 (Petersen-vertex) abstract conclusion.** -/
def Lemma16PrimeFromNCountThreeConclusion (p : ℕ) : Prop :=
  p = 3

/-- **Lemma 16 N(a) = 7 (HS-vertex) abstract conclusion.** -/
def Lemma16PrimeFromNCountSevenConclusion (p : ℕ) : Prop :=
  p = 5

/-- **Lemma 16 N(a) = 0 via Conclusion encoding (paper-faithful).** -/
theorem lem16_prime_from_N_count_zero_via_conclusion
    (p : ℕ) (h_conclusion : Lemma16PrimeFromNCountZeroConclusion p) :
    p = 3 ∨ p = 19 :=
  h_conclusion

/-- **Lemma 16 N(a) = 1 via Conclusion encoding (paper-faithful).** -/
theorem lem16_prime_from_N_count_one_via_conclusion
    (p : ℕ) (h_conclusion : Lemma16PrimeFromNCountOneConclusion p) :
    p = 7 :=
  h_conclusion

/-- **Lemma 16 N(a) = 2 via Conclusion encoding (paper-faithful).** -/
theorem lem16_prime_from_N_count_two_via_conclusion
    (p : ℕ) (h_conclusion : Lemma16PrimeFromNCountTwoConclusion p) :
    p = 5 ∨ p = 11 :=
  h_conclusion

/-- **Lemma 16 N(a) = 3 via Conclusion encoding (paper-faithful).** -/
theorem lem16_prime_from_N_count_three_via_conclusion
    (p : ℕ) (h_conclusion : Lemma16PrimeFromNCountThreeConclusion p) :
    p = 3 :=
  h_conclusion

/-- **Lemma 16 N(a) = 7 via Conclusion encoding (paper-faithful).** -/
theorem lem16_prime_from_N_count_seven_via_conclusion
    (p : ℕ) (h_conclusion : Lemma16PrimeFromNCountSevenConclusion p) :
    p = 5 :=
  h_conclusion

/-- **Lemma 16 N(a) = 0 Conclusion instance (unconditional from N count).** -/
theorem lem16_prime_from_N_count_zero_conclusion_unconditional
    (hΓ : IsMoore57 Γ) (σ : Equiv.Perm V)
    (smul_adj : ∀ v w : V, Γ.Adj v w ↔ Γ.Adj (σ v) (σ w))
    (p k : ℕ) [Fact (Nat.Prime p)] (hp_odd : 2 < p)
    (pow_pk : σ ^ p ^ k = 1)
    {a : V} (ha : σ a = a)
    (h_N_zero : (Moore57.autFixedNeighborFinset Γ σ a).card = 0) :
    Lemma16PrimeFromNCountZeroConclusion p :=
  lem16_prime_from_N_count_zero hΓ σ smul_adj p k hp_odd pow_pk ha h_N_zero

/-- **Lemma 16 N(a) = 1 Conclusion instance (unconditional from N count).** -/
theorem lem16_prime_from_N_count_one_conclusion_unconditional
    (hΓ : IsMoore57 Γ) (σ : Equiv.Perm V)
    (smul_adj : ∀ v w : V, Γ.Adj v w ↔ Γ.Adj (σ v) (σ w))
    (p k : ℕ) [Fact (Nat.Prime p)] (hp_odd : 2 < p)
    (pow_pk : σ ^ p ^ k = 1)
    {a : V} (ha : σ a = a)
    (h_N_one : (Moore57.autFixedNeighborFinset Γ σ a).card = 1) :
    Lemma16PrimeFromNCountOneConclusion p :=
  lem16_prime_from_N_count_one hΓ σ smul_adj p k hp_odd pow_pk ha h_N_one

/-- **Lemma 16 N(a) = 2 Conclusion instance (unconditional from N count).** -/
theorem lem16_prime_from_N_count_two_conclusion_unconditional
    (hΓ : IsMoore57 Γ) (σ : Equiv.Perm V)
    (smul_adj : ∀ v w : V, Γ.Adj v w ↔ Γ.Adj (σ v) (σ w))
    (p k : ℕ) [Fact (Nat.Prime p)] (hp_odd : 2 < p)
    (pow_pk : σ ^ p ^ k = 1)
    {a : V} (ha : σ a = a)
    (h_N_two : (Moore57.autFixedNeighborFinset Γ σ a).card = 2) :
    Lemma16PrimeFromNCountTwoConclusion p :=
  lem16_prime_from_N_count_two hΓ σ smul_adj p k hp_odd pow_pk ha h_N_two

/-- **Lemma 16 N(a) = 3 Conclusion instance (unconditional from N count).** -/
theorem lem16_prime_from_N_count_three_conclusion_unconditional
    (hΓ : IsMoore57 Γ) (σ : Equiv.Perm V)
    (smul_adj : ∀ v w : V, Γ.Adj v w ↔ Γ.Adj (σ v) (σ w))
    (p k : ℕ) [Fact (Nat.Prime p)] (hp_odd : 2 < p)
    (pow_pk : σ ^ p ^ k = 1)
    {a : V} (ha : σ a = a)
    (h_N_three : (Moore57.autFixedNeighborFinset Γ σ a).card = 3) :
    Lemma16PrimeFromNCountThreeConclusion p :=
  lem16_prime_from_N_count_three hΓ σ smul_adj p k hp_odd pow_pk ha h_N_three

/-- **Lemma 16 N(a) = 7 Conclusion instance (unconditional from N count).** -/
theorem lem16_prime_from_N_count_seven_conclusion_unconditional
    (hΓ : IsMoore57 Γ) (σ : Equiv.Perm V)
    (smul_adj : ∀ v w : V, Γ.Adj v w ↔ Γ.Adj (σ v) (σ w))
    (p k : ℕ) [Fact (Nat.Prime p)] (hp_odd : 2 < p)
    (pow_pk : σ ^ p ^ k = 1)
    {a : V} (ha : σ a = a)
    (h_N_seven : (Moore57.autFixedNeighborFinset Γ σ a).card = 7) :
    Lemma16PrimeFromNCountSevenConclusion p :=
  lem16_prime_from_N_count_seven hΓ σ smul_adj p k hp_odd pow_pk ha h_N_seven

/-! #### Paper-faithful proper-signature dispatch (Conclusion-Prop form)

`lem16_pgroup_fix_shape_paper_conclusion`: Conclusion-Prop counterpart
of `lem16_pgroup_fix_shape_paper`, packaging the 5-case N(a) count
dispatch in terms of the per-count Conclusion Props.
-/

/-- **Lemma 16 (paper-faithful Conclusion-Prop dispatch).** [done]

Conclusion-Prop counterpart of `lem16_pgroup_fix_shape_paper`: for σ
a `p^k`-element with odd prime `p > 2` fixing a vertex `a`, the
σ-fixed-neighbour count `c = |N(a) ∩ Fix(σ)|` dispatches into the
per-count Conclusion Props. -/
theorem lem16_pgroup_fix_shape_paper_conclusion
    (hΓ : IsMoore57 Γ) (σ : Equiv.Perm V)
    (smul_adj : ∀ v w : V, Γ.Adj v w ↔ Γ.Adj (σ v) (σ w))
    (p k : ℕ) [Fact (Nat.Prime p)] (hp_odd : 2 < p)
    (pow_pk : σ ^ p ^ k = 1)
    {a : V} (ha : σ a = a) :
    ((Moore57.autFixedNeighborFinset Γ σ a).card = 0 →
        Lemma16PrimeFromNCountZeroConclusion p) ∧
    ((Moore57.autFixedNeighborFinset Γ σ a).card = 1 →
        Lemma16PrimeFromNCountOneConclusion p) ∧
    ((Moore57.autFixedNeighborFinset Γ σ a).card = 2 →
        Lemma16PrimeFromNCountTwoConclusion p) ∧
    ((Moore57.autFixedNeighborFinset Γ σ a).card = 3 →
        Lemma16PrimeFromNCountThreeConclusion p) ∧
    ((Moore57.autFixedNeighborFinset Γ σ a).card = 7 →
        Lemma16PrimeFromNCountSevenConclusion p) :=
  ⟨fun h => lem16_prime_from_N_count_zero_conclusion_unconditional
      hΓ σ smul_adj p k hp_odd pow_pk ha h,
   fun h => lem16_prime_from_N_count_one_conclusion_unconditional
      hΓ σ smul_adj p k hp_odd pow_pk ha h,
   fun h => lem16_prime_from_N_count_two_conclusion_unconditional
      hΓ σ smul_adj p k hp_odd pow_pk ha h,
   fun h => lem16_prime_from_N_count_three_conclusion_unconditional
      hΓ σ smul_adj p k hp_odd pow_pk ha h,
   fun h => lem16_prime_from_N_count_seven_conclusion_unconditional
      hΓ σ smul_adj p k hp_odd pow_pk ha h⟩

end Moore57.Papers.MacajSiran2010.S6
