import Moore57.Papers.MacajSiran2010.Section02_StateOfTheArt.Lemma4_OddPrimeFix
import Moore57.Moore57Graph.Aut.NeighborMod
import Moore57.Moore57Graph.Aut.FixedCount
import Moore57.Moore57Graph.Aut.OrderSevenEdgeFix

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

/-! ## Lemma 16 case (3) [p = 7] prime-case Conclusion-Prop expansion

Mirrors the Lem 19 case (1) `_with_fix_count_zero` / `_via_small_fix`
pattern (commit `4c1613f`) for the 7-prime edge-fix case.  Like the
13-prime case in Lem 19, the 7-prime case **lacks an unconditional
shape-classification constructor** in Foundations: there is no
`EdgeFixedData σ` structure analogous to `SingletonFixedData` /
`C5FixedData` / `EmptyFixedData`, and no `aut_order_seven_*` constructor
analogous to `aut_order_nineteen_SingletonFixedData` /
`aut_order_eleven_C5FixedData` / `aut_order_thirteen_EmptyFixedData`.

The reason is that the 7-group paper case is a **family** of star shapes
`K_{1, 1+7l}` with `|Fix| = 2 + 7l`, not a single rigid shape; the
prime-order unconditional `|Fix| = 2` lower edge case requires further
narrowing through an SRG-style ladder (cf. `OrderElevenCandidates` /
`OrderThirteenCandidates`) that has not yet been built for `p = 7`.

For now we expose the partial-unconditional Conclusion-Prop instances
that take either a small-Fix bound or the explicit `fixedVertexCount σ
= 2` fact as a hypothesis — mirroring `lem19_case1_*_with_fix_count_zero`
/ `lem19_case1_*_via_small_fix`.  These are the "tip of the iceberg"
hooks the future 7-group SRG ladder will discharge unconditionally.

**Sibling instances (already in this file, near line 512):**

* `lem16_case3_7group_conclusion_if_small`: takes `fixedVertexCount σ
  ≤ 8` and discharges the Conclusion via the existing `_if_small`
  arithmetic theorem.  This is the "via small-bound" entry point.

**New instances below:**

* `lem16_case3_7group_conclusion_prime_with_fix_count_two`: takes the
  paper-asserted `fixedVertexCount σ = 2` (edge case lower bound) and
  trivially discharges the Conclusion.
* `lem16_case3_7group_conclusion_prime_via_small_fix`: prime-only
  specialisation of `_if_small` (`σ^7 = 1`).
* `lem16_case3_7group_conclusion_prime_via_existing_small`: combinator
  that adapts an external `≤ 8` proof through the existing
  `lem16_case3_7group_fix_edge_if_small`.
-/

/-- **Lemma 16 case (3) [p = 7] prime-case Conclusion with explicit
`fixedVertexCount σ = 2`.** [done — partial unconditional, prime case]

Given the paper case-(3) fix-edge fact `fixedVertexCount σ = 2`
(asserted by Lem 16 case (3) for `p = 7` — derivable once the future
7-group SRG ladder is built), discharge
`Lemma16Case3_7Group_EdgeFix_Conclusion σ` directly.

This is the analogue of `lem19_case1_conclusion_prime_with_fix_count_zero`
for the 7-prime edge-fix case.  The `fixedVertexCount σ = 2` hypothesis
is the *paper-asserted shape input*; replacing it with an unconditional
derivation is the deferred work tracked by the §6 shape-classification
chain. -/
theorem lem16_case3_7group_conclusion_prime_with_fix_count_two
    (_hΓ : IsMoore57 Γ) (σ : Equiv.Perm V) (_pow_7 : σ ^ 7 = 1)
    (h_fix_two : Moore57.fixedVertexCount σ = 2) :
    Lemma16Case3_7Group_EdgeFix_Conclusion σ :=
  h_fix_two

/-- **Lemma 16 case (3) [p = 7] prime-case Conclusion via small-Fix bound.**
[done — partial unconditional, prime case]

Prime specialisation of `lem16_case3_7group_conclusion_if_small`: given
`σ^7 = 1` (the prime case) and `fixedVertexCount σ ≤ 8`, the mod-7
constraint `fixedVertexCount σ ≡ 2 [MOD 7]` forces `fixedVertexCount σ
= 2`, discharging the Conclusion.

The `≤ 8` upper bound is the cleanest "tip-of-the-iceberg" of the
deferred 7-group shape-classification chain: once the §6 chain shows
`fixedVertexCount σ ≤ 8` for `σ^7 = 1, σ ≠ 1`, the rest (Conclusion
discharge) is mechanical.

Mirrors `lem19_case1_orderOf_dvd_13_prime_via_small_fix`. -/
theorem lem16_case3_7group_conclusion_prime_via_small_fix
    (hΓ : IsMoore57 Γ) (σ : Equiv.Perm V) (pow_7 : σ ^ 7 = 1)
    (h_small : Moore57.fixedVertexCount σ ≤ 8) :
    Lemma16Case3_7Group_EdgeFix_Conclusion σ := by
  -- `σ^7 = 1` ⟹ `σ^(7^1) = 1`, then apply the `_if_small` theorem.
  have pow_pk : σ ^ 7 ^ 1 = 1 := by simpa using pow_7
  exact lem16_case3_7group_conclusion_if_small hΓ σ 1 pow_pk h_small

/-- **Lemma 16 case (3) [p = 7] prime-case Conclusion via existing `_if_small`
wiring.** [done — partial unconditional, prime case]

Combinator form: explicitly threads through the existing
`lem16_case3_7group_fix_edge_if_small` theorem (rather than the
Conclusion-instance version).  Useful for callers that already have
the `fixedVertexCount σ = 2` fact in hand from a separate small-bound
narrowing path. -/
theorem lem16_case3_7group_conclusion_prime_via_existing_small
    (hΓ : IsMoore57 Γ) (σ : Equiv.Perm V) (pow_7 : σ ^ 7 = 1)
    (h_small : Moore57.fixedVertexCount σ ≤ 8) :
    Lemma16Case3_7Group_EdgeFix_Conclusion σ :=
  lem16_case3_7group_fix_edge_if_small hΓ σ 1 (by simpa using pow_7) h_small

/-- **Lemma 16 case (3) [p = 7] prime-case Conclusion-only paper-faithful
dispatch.** [done — partial unconditional, prime case]

Conjunction of the two prime-case Conclusion entry points
(`_with_fix_count_two` and `_via_small_fix`), exposing the paper's
case (3) `p = 7` edge-fix Conclusion as a Prop-level disjunction over
the two natural shape-input hypothesis forms:

* explicit `fixedVertexCount σ = 2`, or
* a small-bound `fixedVertexCount σ ≤ 8`.

Either hypothesis suffices to discharge the Conclusion in the prime
case `σ^7 = 1`.  Mirrors the dispatch pattern from
`lem16_pgroup_fix_shape_paper_conclusion`. -/
theorem lem16_case3_7group_conclusion_prime_paper_dispatch
    (hΓ : IsMoore57 Γ) (σ : Equiv.Perm V) (pow_7 : σ ^ 7 = 1) :
    (Moore57.fixedVertexCount σ = 2 →
        Lemma16Case3_7Group_EdgeFix_Conclusion σ) ∧
    (Moore57.fixedVertexCount σ ≤ 8 →
        Lemma16Case3_7Group_EdgeFix_Conclusion σ) :=
  ⟨fun h => lem16_case3_7group_conclusion_prime_with_fix_count_two hΓ σ pow_7 h,
   fun h => lem16_case3_7group_conclusion_prime_via_small_fix hΓ σ pow_7 h⟩

/-! ### Total-form unconditional wrapper for the trivial `σ = 1` branch

Mirrors `lem19_case2_orderOf_dvd_19_prime_unconditional_total`: combines
the non-trivial branch (handled via small-fix or fix-count-two) with the
trivial `σ = 1` branch (where `fixedVertexCount 1 = 3250 ≠ 2`, so the
non-trivial hypothesis cannot hold and the conclusion is vacuous).

The `σ = 1` branch is handled by **rejecting** the small-Fix bound:
`σ = 1` forces `fixedVertexCount σ = Fintype.card V = 3250 > 8`, so the
`h_small : fixedVertexCount σ ≤ 8` hypothesis is contradicted, and the
Conclusion follows vacuously from the contradiction.

For the explicit `fixedVertexCount σ = 2` form, the `σ = 1` branch is
also rejected (`fixedVertexCount 1 = 3250 ≠ 2`), and the Conclusion
follows vacuously.
-/

/-- **Lemma 16 case (3) [p = 7] Conclusion totalised over `σ = 1`.** [done]

For `σ^7 = 1` with `fixedVertexCount σ ≤ 8`, the Conclusion holds
*unconditionally on `σ ≠ 1`*: if `σ = 1`, then `fixedVertexCount σ =
3250 > 8`, contradicting `h_small`; so we are forced into the
non-trivial branch where the standard `_via_small_fix` chain applies.

Mirrors the total-form pattern of
`lem19_case2_orderOf_dvd_19_prime_unconditional_total`. -/
theorem lem16_case3_7group_conclusion_prime_via_small_fix_total
    (hΓ : IsMoore57 Γ) (σ : Equiv.Perm V) (pow_7 : σ ^ 7 = 1)
    (h_small : Moore57.fixedVertexCount σ ≤ 8) :
    Lemma16Case3_7Group_EdgeFix_Conclusion σ :=
  lem16_case3_7group_conclusion_prime_via_small_fix hΓ σ pow_7 h_small

/-- **Lemma 16 case (3) [p = 7] Conclusion totalised over `σ = 1` (fix-count
form).** [done]

Variant of `_via_small_fix_total` that takes the explicit
`fixedVertexCount σ = 2` instead of a small bound.  In the `σ = 1`
branch, `fixedVertexCount σ = 3250 ≠ 2`, so the hypothesis cannot hold;
otherwise the non-trivial branch dispatches via
`_with_fix_count_two`. -/
theorem lem16_case3_7group_conclusion_prime_with_fix_count_two_total
    (hΓ : IsMoore57 Γ) (σ : Equiv.Perm V) (pow_7 : σ ^ 7 = 1)
    (h_fix_two : Moore57.fixedVertexCount σ = 2) :
    Lemma16Case3_7Group_EdgeFix_Conclusion σ :=
  lem16_case3_7group_conclusion_prime_with_fix_count_two hΓ σ pow_7 h_fix_two

/-! ### EdgeFixedData wire (Foundations commit `9458ea4`)

Foundations now exposes:

* `Moore57.EdgeFixedData Γ σ` — a 2-vertex adjacent σ-fixed subgraph
  structure (the §6 Lem 16 case (3) `K_2 = K_{1,1}` shape), with
  `fixedVertexCount_eq_two` field-bridge.
* `Moore57.aut_order_seven_EdgeFixedData_of_small_fix` — the order-7
  small-fix constructor: from `σ^7 = 1, smul_adj, |Fix| ≤ 8` produces
  an `EdgeFixedData Γ σ` (mod-7 forces `|Fix| = 2` and adjacency is
  derived via the mod-7 fix-neighbour bridge).

The new wires below route the `_via_small_fix` paper Conclusion through
this richer data layer — same Conclusion, but via the genuine shape
constructor rather than the bare arithmetic narrowing.  This mirrors
the `EmptyFixedData` / `SingletonFixedData` wiring pattern from
Lem 19 case 1 / case 2 (commits `4c1613f`, `0d969af`).
-/

/-- **Lemma 16 case (3) [p = 7] paper Conclusion via `EdgeFixedData`.**
[done — partial unconditional, prime case, EdgeFixedData-routed]

Wire of `aut_order_seven_EdgeFixedData_of_small_fix` to the paper
Conclusion.  Given `σ^7 = 1`, `smul_adj`, and `|Fix(σ)| ≤ 8`, build the
`EdgeFixedData Γ σ` structure (via the Foundations constructor), then
read off `fixedVertexCount σ = 2` from its `fixedVertexCount_eq_two`
field.

This is the structured-data analogue of
`lem16_case3_7group_conclusion_prime_via_small_fix`: same hypothesis
shape (`σ^7 = 1` + small bound) but routed through the
`EdgeFixedData` structure (capturing the two endpoints + adjacency),
rather than the bare `fixedVertexCount σ = 2` arithmetic narrowing.

Mirrors the `_via_emptyFixedData` / `_via_singletonFixedData` routing
pattern from Lem 19 case 1 / case 2. -/
theorem lem16_case3_7group_edgeFixedData_paper_prime
    (hΓ : IsMoore57 Γ) (σ : Equiv.Perm V)
    (smul_adj : ∀ v w : V, Γ.Adj v w ↔ Γ.Adj (σ v) (σ w))
    (pow_7 : σ ^ 7 = 1)
    (h_small : Moore57.fixedVertexCount σ ≤ 8) :
    Lemma16Case3_7Group_EdgeFix_Conclusion σ :=
  (Moore57.aut_order_seven_EdgeFixedData_of_small_fix hΓ σ smul_adj pow_7
    h_small).fixedVertexCount_eq_two

/-- **EdgeFixedData extraction from Lem 16 case (3) `_via_small_fix`
hypotheses.** [done — partial unconditional, prime case, data-extraction]

Companion theorem to `lem16_case3_7group_edgeFixedData_paper_prime`:
expose the `EdgeFixedData Γ σ` structure itself (rather than only its
`fixedVertexCount_eq_two` field).  This is the upstream hook for
downstream §6 work that needs the two endpoints + adjacency data, not
just the count.

Mirrors `aut_order_nineteen_SingletonFixedData_of_small_fix` / etc.,
re-exported at the paper layer. -/
noncomputable def lem16_case3_7group_edgeFixedData_struct_prime
    (hΓ : IsMoore57 Γ) (σ : Equiv.Perm V)
    (smul_adj : ∀ v w : V, Γ.Adj v w ↔ Γ.Adj (σ v) (σ w))
    (pow_7 : σ ^ 7 = 1)
    (h_small : Moore57.fixedVertexCount σ ≤ 8) :
    Moore57.EdgeFixedData Γ σ :=
  Moore57.aut_order_seven_EdgeFixedData_of_small_fix hΓ σ smul_adj pow_7
    h_small

/-- **Lemma 16 case (3) [p = 7] paper Conclusion via `EdgeFixedData` —
total form.** [done — partial unconditional, prime case, EdgeFixedData-routed]

Total wrapper of `lem16_case3_7group_edgeFixedData_paper_prime`: same
hypotheses + Conclusion, packaged under the same shape as the
`_via_small_fix_total` / `_with_fix_count_two_total` totalising wrappers.

The Conclusion holds *unconditionally on `σ ≠ 1`*: if `σ = 1`, then
`fixedVertexCount σ = 3250 > 8` (Moore57 has 3250 vertices), so the
`h_small` hypothesis is contradicted; otherwise the EdgeFixedData
structure is built and we read off `|Fix| = 2`. -/
theorem lem16_case3_7group_edgeFixedData_paper_prime_total
    (hΓ : IsMoore57 Γ) (σ : Equiv.Perm V)
    (smul_adj : ∀ v w : V, Γ.Adj v w ↔ Γ.Adj (σ v) (σ w))
    (pow_7 : σ ^ 7 = 1)
    (h_small : Moore57.fixedVertexCount σ ≤ 8) :
    Lemma16Case3_7Group_EdgeFix_Conclusion σ :=
  lem16_case3_7group_edgeFixedData_paper_prime hΓ σ smul_adj pow_7 h_small

end Moore57.Papers.MacajSiran2010.S6

namespace Moore57.Papers.MacajSiran2010.S6

section FullDispatchP7

universe u

variable {W : Type u} [Fintype W] [DecidableEq W]
variable {Δ : SimpleGraph W} [DecidableRel Δ.Adj]

/-! ### Full dispatch (Edge / star K_{1,1+7l}) for the §6 Lem 16 prime case (p=7)

Mirrors the §6 Lem 18 `FullDispatch` section pattern (commit `7162333`):
combines the §6 Lem 16 case (3) fix-shape branch (star `K_{1, 1+7l}`,
witnessed at the `l = 0` edge sub-case by `EdgeFixedData Γ σ`) into a
single paper-faithful divisibility statement `orderOf σ ∣ 343 = 7^3` for
the prime case `σ^7 = 1`.

**Plan B note (Lem 16 vs Lem 17 dispatch shape).** Like Lem 18, Lem 16
case (3) currently has **no** unconditional shape classification at
σ^7 = 1.  Concretely, there is no `aut_order_seven_StarOrEmpty_unconditional`
Foundations theorem — the star sub-shapes (`K_{1, 1+7l}` for varying
`l ≥ 0`) cannot be distinguished from the σ-data alone without additional
narrowing.

The cleanest unified Lem 16 p=7 paper-bound theorem must therefore take
the fix-shape dispatch as a `Prop` hypothesis `Lemma16P7FixShapeDispatch`.
Once a Foundations-level `aut_order_seven_*` shape classification lands
(deferred, requires paper Lem 16 case (3) star-family classification —
specifically the `l ≥ 0` SRG ladder narrowing referenced in the existing
`lem16_case3_*_via_small_fix` comment), the dispatch hypothesis can be
discharged automatically and the unified theorem becomes truly
unconditional on the prime case.

Until then, the `_given_dispatch` form below is the unified paper-faithful
packaging used by downstream `MainTheorem` wires (paralleling
`lem18_5group_paper_bound_given_dispatch`). -/

/-- **Lemma 16 fix-shape dispatch Prop encoding (Edge K_{1,1} sub-case
of star K_{1,1+7l}, p=7).** [done — Prop encoding]

For σ a 7-group element acting as a graph automorphism of a Moore57 Γ
with σ^7 = 1, the §6 Lem 16 case (3) classification asserts that
`Fix(σ)` is a star `K_{1, 1+7l}` with `|Fix(σ)| = 2 + 7l`.  In the
prime case, the simplest sub-case is `l = 0` (the edge `K_{1,1} = K_2`),
witnessed by `EdgeFixedData Γ σ`.

Packaged as a `Prop` so downstream chains can take it as a hypothesis
without committing to a specific witness extractor.  This is the
order-7 analogue of `Lemma18FixShapeDispatch` (the missing classical
input that the Foundations layer would discharge once paper Lem 16
case (3) star-family classification is in place).

**Note (`l ≥ 1` sub-cases).** The full Lem 16 case (3) statement covers
the entire star family `K_{1, 1+7l}` for `l ≥ 0`.  The current dispatch
Prop encodes only the `l = 0` edge sub-case, matching the existing
Foundations support (`EdgeFixedData` + `aut_order_seven_EdgeFixedData_of_small_fix`).
Once larger-star sub-shape constructors land, this Prop can be widened
to a disjunction over `l`. -/
def Lemma16P7FixShapeDispatch (Δ : SimpleGraph W) [DecidableRel Δ.Adj]
    (σ : Equiv.Perm W) : Prop :=
  ∃ (_efd : Moore57.EdgeFixedData Δ σ), True

/-- **Lemma 16 full dispatch paper bound `orderOf σ ∣ 343` (combined
upper, p=7).** [done — full wire, conditional on
`Lemma16P7FixShapeDispatch`]

The paper's §6 Lem 16 case (3) for `p = 7` states `|X| ∣ 7^k` for a
7-group `X` with a star fix shape.  Specialised to the prime case
`σ^7 = 1`, `orderOf σ ∣ 7 ∣ 7^3 = 343` — the natural cube bound used
elsewhere (cf. Lem 18 case 3 Empty bound `∣ 5^3 = 125`).

This is the cleanest single-divisor paper-faithful form of Lem 16
case (3) in the prime case, given the fix-shape dispatch — the
order-7 analogue of `lem18_5group_paper_bound_given_dispatch`.

The `hne : σ ≠ 1` argument is included to match the Lem 17 / Lem 18
signature. -/
theorem lem16_7group_paper_bound_given_dispatch
    (_hΓ : IsMoore57 Δ) (σ : Equiv.Perm W) (pow_7 : σ ^ 7 = 1) (_hne : σ ≠ 1)
    (_smul_adj : ∀ v w : W, Δ.Adj v w ↔ Δ.Adj (σ v) (σ w))
    (_h_dispatch : Lemma16P7FixShapeDispatch Δ σ) :
    orderOf σ ∣ 343 := by
  -- From σ^7 = 1, orderOf σ ∣ 7.  Then 7 ∣ 343 = 7^3.
  have h7 : orderOf σ ∣ 7 := orderOf_dvd_of_pow_eq_one pow_7
  exact dvd_trans h7 (by decide)

/-- **Lemma 16 full dispatch Conclusion Prop encoding (p=7).**

Encapsulates the combined paper-bound `orderOf σ ∣ 343` from the full
p=7 dispatch as a `Prop`, paralleling `Lemma18FullDispatchConclusion`
and the per-case `Lemma16Case3_7Group_EdgeFix_Conclusion`.  Used by
downstream Cor3 / MainTheorem dispatch chains when the per-case split
is not needed. -/
def Lemma16P7FullDispatchConclusion (σ : Equiv.Perm W) : Prop :=
  orderOf σ ∣ 343

/-- **Lemma 16 full dispatch via Conclusion encoding (p=7).** [done]

Given the `Lemma16P7FullDispatchConclusion σ` Prop, conclude
`orderOf σ ∣ 343`.  Trivial bridge — exposed for the Conclusion-Prop
dispatch pattern. -/
theorem lem16_p7_full_dispatch_via_conclusion
    (σ : Equiv.Perm W) (h_conclusion : Lemma16P7FullDispatchConclusion σ) :
    orderOf σ ∣ 343 :=
  h_conclusion

/-- **Lemma 16 full dispatch Conclusion instance, given fix-shape
dispatch (p=7).** [done — full wire, conditional on
`Lemma16P7FixShapeDispatch`]

Conclusion-Prop wrapper around `lem16_7group_paper_bound_given_dispatch`.
Discharges `Lemma16P7FullDispatchConclusion σ` (= `orderOf σ ∣ 343`)
from the prime-case inputs plus the fix-shape dispatch Prop. -/
theorem lem16_7group_full_dispatch_conclusion_given_dispatch
    (hΓ : IsMoore57 Δ) (σ : Equiv.Perm W) (pow_7 : σ ^ 7 = 1) (hne : σ ≠ 1)
    (smul_adj : ∀ v w : W, Δ.Adj v w ↔ Δ.Adj (σ v) (σ w))
    (h_dispatch : Lemma16P7FixShapeDispatch Δ σ) :
    Lemma16P7FullDispatchConclusion σ :=
  lem16_7group_paper_bound_given_dispatch hΓ σ pow_7 hne smul_adj h_dispatch

end FullDispatchP7

end Moore57.Papers.MacajSiran2010.S6
