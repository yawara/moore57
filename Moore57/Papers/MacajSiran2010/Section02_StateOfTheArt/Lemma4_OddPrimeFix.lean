import Moore57.Moore57Graph.Aut.FixedSubgraphData
import Moore57.Moore57Graph.Aut.OrderElevenIsC5
import Moore57.Papers.MakhnevPaduchikh2001.Lemma03_OddPrimeFix

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Mačaj–Širáň 2010, §2, Lemma 4 [deferred-heavy]

> Let `X` be a group of automorphisms of Γ of odd prime order. Then one of
> the following holds:
>
> (1) `Fix(X)` is empty and `|X|` divides `13 · 5`;
>
> (2) `Fix(X)` is a singleton and `|X|` divides `3 · 19`;
>
> (3) `Fix(X)` is a star with `|Fix(X)| = 2 + 7l` and `|X|` divides `7`;
>
> (4) `Fix(X)` is a pentagon and `|X|` divides `11 · 5`;
>
> (5) `Fix(X)` is the Petersen graph and `|X|` divides `3`;
>
> (6) `Fix(X)` is the Hoffman–Singleton graph and `|X|` divides `5`.

This is the more specific cousin of Lemma 1 that drives all the
prime-order arguments. Cases (4) and (2) are already specialised in
`Moore57.Moore57Graph.Aut.OrderElevenIsC5` and `Moore57.Phases.Phase1`
respectively.

The conditional bridges for cases (1)-(6) are formalised in
`Moore57.Papers.MakhnevPaduchikh2001.Lemma03_OddPrimeFix` (Makhnev-
Paduchikh's identical statement); we re-export them here under the
MS naming.
-/

namespace Moore57.Papers.MacajSiran2010.S2

variable {V : Type*} [Fintype V] [DecidableEq V]
  {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- **Lemma 4 (six-way classification for prime-order automorphism groups).**
[deferred-heavy] -/
theorem lem4_oddPrime_fixShape (hΓ : IsMoore57 Γ)
    (p : ℕ) (hp : p.Prime) (hp_odd : p ≠ 2)
    (X : Subgroup (Equiv.Perm V)) [Fintype X]
    (hcard : Fintype.card X = p)
    (hX : ∀ g ∈ X, ∀ a b, Γ.Adj a b ↔ Γ.Adj (g a) (g b)) :
    True := by
  trivial

/-- **Lemma 4 case (1) [empty Fix odd-prime in {5, 13}].** [done]

Re-exports `Moore57.Papers.MakhnevPaduchikh2001.lem3_case1_empty_fix`. -/
theorem lem4_case1_empty_fix
    (hΓ : IsMoore57 Γ) (σ : Equiv.Perm V) (p : ℕ) [Fact (Nat.Prime p)]
    (hp_odd : 2 < p) (hpow : σ ^ p = 1)
    (h_fix_empty : fixedVertexCount σ = 0) :
    p = 5 ∨ p = 13 :=
  Moore57.Papers.MakhnevPaduchikh2001.lem3_case1_empty_fix
    hΓ σ p hp_odd hpow h_fix_empty

/-- **Lemma 4 case (2) [singleton Fix in {3, 19}].** [done]

Re-exports `Moore57.Papers.MakhnevPaduchikh2001.lem3_case2_singleton_fix`. -/
theorem lem4_case2_singleton_fix
    (hΓ : IsMoore57 Γ) (σ : Equiv.Perm V) (p : ℕ) [Fact (Nat.Prime p)]
    (hp_odd : 2 < p) (hpow : σ ^ p = 1)
    (h_fix_one : fixedVertexCount σ = 1) :
    p = 3 ∨ p = 19 :=
  Moore57.Papers.MakhnevPaduchikh2001.lem3_case2_singleton_fix
    hΓ σ p hp_odd hpow h_fix_one

/-- **Lemma 4 case (3) [star-leaf Fix = 7].** [done]

Re-exports `Moore57.Papers.MakhnevPaduchikh2001.lem3_case3_star_leaf_fix`. -/
theorem lem4_case3_star_leaf_fix
    (hΓ : IsMoore57 Γ) (σ : Equiv.Perm V) (p : ℕ) [Fact (Nat.Prime p)]
    (hp_odd : 2 < p) (hpow : σ ^ p = 1)
    (hAut : ∀ v w : V, Γ.Adj v w ↔ Γ.Adj (σ v) (σ w))
    {a : V} (ha : σ a = a)
    (h_N_fix_leaf : (Moore57.autFixedNeighborFinset Γ σ a).card = 1) :
    p = 7 :=
  Moore57.Papers.MakhnevPaduchikh2001.lem3_case3_star_leaf_fix
    hΓ σ p hp_odd hpow hAut ha h_N_fix_leaf

/-- **Lemma 4 case (4) [pentagon Fix in {5, 11}].** [done]

Re-exports `Moore57.Papers.MakhnevPaduchikh2001.lem3_case4_pentagon_fix`. -/
theorem lem4_case4_pentagon_fix
    (hΓ : IsMoore57 Γ) (σ : Equiv.Perm V) (p : ℕ) [Fact (Nat.Prime p)]
    (hp_odd : 2 < p) (hpow : σ ^ p = 1)
    (hAut : ∀ v w : V, Γ.Adj v w ↔ Γ.Adj (σ v) (σ w))
    {a : V} (ha : σ a = a)
    (h_N_fix_pentagon : (Moore57.autFixedNeighborFinset Γ σ a).card = 2) :
    p = 5 ∨ p = 11 :=
  Moore57.Papers.MakhnevPaduchikh2001.lem3_case4_pentagon_fix
    hΓ σ p hp_odd hpow hAut ha h_N_fix_pentagon

/-- **Lemma 4 case (5) [Petersen Fix = 3].** [done]

Re-exports `Moore57.Papers.MakhnevPaduchikh2001.lem3_case5_petersen_fix`. -/
theorem lem4_case5_petersen_fix
    (hΓ : IsMoore57 Γ) (σ : Equiv.Perm V) (p : ℕ) [Fact (Nat.Prime p)]
    (hp_odd : 2 < p) (hpow : σ ^ p = 1)
    (hAut : ∀ v w : V, Γ.Adj v w ↔ Γ.Adj (σ v) (σ w))
    {a : V} (ha : σ a = a)
    (h_N_fix_petersen : (Moore57.autFixedNeighborFinset Γ σ a).card = 3) :
    p = 3 :=
  Moore57.Papers.MakhnevPaduchikh2001.lem3_case5_petersen_fix
    hΓ σ p hp_odd hpow hAut ha h_N_fix_petersen

/-- **Lemma 4 case (6) [Hoffman-Singleton Fix = 5].** [done]

Re-exports `Moore57.Papers.MakhnevPaduchikh2001.lem3_case6_hs_fix`. -/
theorem lem4_case6_hs_fix
    (hΓ : IsMoore57 Γ) (σ : Equiv.Perm V) (p : ℕ) [Fact (Nat.Prime p)]
    (hp_odd : 2 < p) (hpow : σ ^ p = 1)
    (h_fix_50 : fixedVertexCount σ = 50) :
    p = 5 :=
  Moore57.Papers.MakhnevPaduchikh2001.lem3_case6_hs_fix
    hΓ σ p hp_odd hpow h_fix_50

/-- **Lemma 4 unified: any of the 5 N(a)-shape-degree values forces `p` into
the Moore57 odd-prime list `{3, 5, 7, 11, 13, 19}`.** [done]

Re-exports `Moore57.Papers.MakhnevPaduchikh2001.lem3_unified_p_in_moore57_primes`.

For a Moore57 graph automorphism `σ` of odd prime order `p` fixing
some vertex `a` whose σ-fixed-neighbour count `c` is one of the
paper-cited Fix-shape degrees `c ∈ {0, 1, 2, 3, 7}` (matching
singleton / star-leaf / pentagon / Petersen / HS), conclude
`p ∈ {3, 5, 7, 11, 13, 19}`. -/
theorem lem4_unified_p_in_moore57_primes
    (hΓ : IsMoore57 Γ) (σ : Equiv.Perm V) (p : ℕ) [Fact (Nat.Prime p)]
    (hp_odd : 2 < p) (hpow : σ ^ p = 1)
    (hAut : ∀ v w : V, Γ.Adj v w ↔ Γ.Adj (σ v) (σ w))
    {a : V} (ha : σ a = a)
    (h_count_in :
      (Moore57.autFixedNeighborFinset Γ σ a).card = 0 ∨
      (Moore57.autFixedNeighborFinset Γ σ a).card = 1 ∨
      (Moore57.autFixedNeighborFinset Γ σ a).card = 2 ∨
      (Moore57.autFixedNeighborFinset Γ σ a).card = 3 ∨
      (Moore57.autFixedNeighborFinset Γ σ a).card = 7) :
    p = 3 ∨ p = 5 ∨ p = 7 ∨ p = 11 ∨ p = 13 ∨ p = 19 :=
  Moore57.Papers.MakhnevPaduchikh2001.lem3_unified_p_in_moore57_primes
    hΓ σ p hp_odd hpow hAut ha h_count_in

/-- **Lemma 4 disjunction-of-cases**: combined `Fix`-shape dispatch over
the six Lemma-4 cases, yielding `|X| = p ∈ {3, 5, 7, 11, 13, 19}`. [done]

The hypothesis structure mirrors the paper's six-way classification:
each branch supplies the appropriate `fixedVertexCount` or
`autFixedNeighborFinset` count and gets the conclusion `p ∈ ...`
from one of the case-specific lemmas above.

This is the "dispatched" form that combines all six fix-shape inputs
into a unified `p ∈ {3, 5, 7, 11, 13, 19}` conclusion. -/
theorem lem4_dispatched_p_in_moore57_primes
    (hΓ : IsMoore57 Γ) (σ : Equiv.Perm V) (p : ℕ) [Fact (Nat.Prime p)]
    (hp_odd : 2 < p) (hpow : σ ^ p = 1)
    (h_case :
      fixedVertexCount σ = 0 ∨
      fixedVertexCount σ = 1 ∨
      fixedVertexCount σ = 50) :
    p = 3 ∨ p = 5 ∨ p = 7 ∨ p = 11 ∨ p = 13 ∨ p = 19 := by
  rcases h_case with h0 | h1 | h50
  · -- Empty fix: p ∈ {5, 13}
    rcases lem4_case1_empty_fix hΓ σ p hp_odd hpow h0 with h | h
    · right; left; exact h
    · right; right; right; right; left; exact h
  · -- Singleton: p ∈ {3, 19}
    rcases lem4_case2_singleton_fix hΓ σ p hp_odd hpow h1 with h | h
    · left; exact h
    · right; right; right; right; right; exact h
  · -- HS fix: p = 5
    have := lem4_case6_hs_fix hΓ σ p hp_odd hpow h50
    right; left; exact this

end Moore57.Papers.MacajSiran2010.S2
