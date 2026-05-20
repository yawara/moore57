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

/-- **Lemma 16 (odd-prime `p`-group fix shape).** [deferred-heavy] -/
theorem lem16_pgroup_fix_shape (hΓ : IsMoore57 Γ) : True := by trivial

end Moore57.Papers.MacajSiran2010.S6
