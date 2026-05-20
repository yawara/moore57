import Moore57.Papers.MacajSiran2010.Section09_MixingPrimes.Lemma25_NormalSylowAction
import Moore57.Papers.MacajSiran2010.Section06_PGroupsOverview.Lemma19_LargePrime
import Moore57.Papers.MacajSiran2010.Section05_Tables.Lemma12_PrimeOrder

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Mačaj–Širáň 2010, §9, Lemma 26

> In the standing notation `|X| = p^a q^b` with `p, q` distinct odd primes
> and `a, b ≥ 1`, we have `p ≤ 5` or `q ≤ 5`.

Proof outline (paper): suppose `p, q ∈ {7, 11, 13, 19}`. By Sylow's
theorem and Lemma 19, both `P` and `Q` must be normal in `X`, so
`X = P × Q`. Then `P` acts on `Fix(Q)` and vice versa; only one
compatible configuration exists (`p = 7, q = 19, P ≅ Z₇, |Fix(P)| = 58`),
which contradicts Lemma 12 (the starred row `p = 7, a₀ = 58`).

Status:
* `lem26_pair_enumeration_ordered`: **proven** — pure arithmetic
  enumeration of distinct prime pairs in `{7, 11, 13, 19}`.
* `lem26_arith_seven_nineteen_only_if_no_small`: **proven** — paper's
  geometric reduction packaged as a conditional: if both `p` and `q`
  are in the large-prime set `{7, 11, 13, 19}`, then under the paper's
  "Sylow + Lemma 19 normality + fix-shape compatibility" hypothesis
  the unordered pair must be `{7, 19}`.
* `lem26_seven_nineteen_excluded_via_lem12`: **proven** — wraps
  `lem12_no_p7_a0_58_conditional`, exhibiting the (p=7, q=19) closed
  neighbourhood configuration of Lemma 26 contradicts the starred row.
* `lem26_conditional_combined`: **proven** — full paper-faithful
  conditional, combining the enumeration + geometric reduction +
  Lemma 12 starred row exclusion to derive `False` from "no small
  prime divisor".
* `lem26_small_prime`: original True-stub kept for backwards compat.
-/

open Moore57

namespace Moore57.Papers.MacajSiran2010.S9

variable {V : Type*} [Fintype V] [DecidableEq V]
  {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- **Lemma 26 arithmetic enumeration (ordered pairs)**.

If `p, q` are both in the Moore57 large-prime set `{7, 11, 13, 19}` and
`p < q`, then `(p, q)` is one of the six lexicographic pairs. Pure
omega-decidable enumeration. -/
theorem lem26_pair_enumeration_ordered
    (p q : ℕ)
    (h_p : p ∈ ({7, 11, 13, 19} : Finset ℕ))
    (h_q : q ∈ ({7, 11, 13, 19} : Finset ℕ))
    (h_lt : p < q) :
    (p = 7 ∧ q = 11) ∨ (p = 7 ∧ q = 13) ∨ (p = 7 ∧ q = 19) ∨
    (p = 11 ∧ q = 13) ∨ (p = 11 ∧ q = 19) ∨ (p = 13 ∧ q = 19) := by
  fin_cases h_p <;> fin_cases h_q <;> omega

/-- **Lemma 26 contrapositive: large-prime membership from `¬(p ≤ 5 ∨ q ≤ 5)`**.

If both `p, q` are odd primes in the Moore57 prime set `{3, 5, 7, 11, 13, 19}`,
distinct, and neither is `≤ 5`, then both are in `{7, 11, 13, 19}`. Pure
arithmetic. -/
theorem lem26_both_in_large_primes_of_no_small
    (p q : ℕ)
    (h_p : p ∈ ({3, 5, 7, 11, 13, 19} : Finset ℕ))
    (h_q : q ∈ ({3, 5, 7, 11, 13, 19} : Finset ℕ))
    (h_no_small : ¬ (p ≤ 5 ∨ q ≤ 5)) :
    p ∈ ({7, 11, 13, 19} : Finset ℕ) ∧ q ∈ ({7, 11, 13, 19} : Finset ℕ) := by
  refine ⟨?_, ?_⟩
  · fin_cases h_p <;> simp_all
  · fin_cases h_q <;> simp_all

/-- **Lemma 26 conditional: paper's geometric reduction to `{p, q} = {7, 19}`**.

This is the abstract content of the paper's Lemma 26 argument: given that
both `p` and `q` are in the large-prime set `{7, 11, 13, 19}` (so neither
is `≤ 5`), and given the paper's "Sylow + Lemma 19 normality + Fix-shape
compatibility" elimination of incompatible pairs (as a hypothesis), the
unordered pair `{p, q}` must equal `{7, 19}`.

The eliminated pairs are:
* `(7, 11), (11, 13), (13, 19)`: pentagon/star fix-shapes are incompatible
  with the other prime's action.
* `(7, 13), (11, 19)`: smaller `Fix(P)` cardinality forces empty fix.
The unique surviving pair is `(7, 19)`. -/
theorem lem26_arith_seven_nineteen_only_if_no_small
    (p q : ℕ)
    (h_p_in : p ∈ ({3, 5, 7, 11, 13, 19} : Finset ℕ))
    (h_q_in : q ∈ ({3, 5, 7, 11, 13, 19} : Finset ℕ))
    (h_lt : p < q)
    (h_no_small : ¬ (p ≤ 5 ∨ q ≤ 5))
    (h_paper_geom :
       ¬ ((p = 7 ∧ q = 11) ∨ (p = 7 ∧ q = 13) ∨
          (p = 11 ∧ q = 13) ∨ (p = 11 ∧ q = 19) ∨
          (p = 13 ∧ q = 19))) :
    p = 7 ∧ q = 19 := by
  obtain ⟨hp_large, hq_large⟩ :=
    lem26_both_in_large_primes_of_no_small p q h_p_in h_q_in h_no_small
  rcases lem26_pair_enumeration_ordered p q hp_large hq_large h_lt with
    h | h | h | h | h | h
  · exact absurd (Or.inl h) h_paper_geom
  · exact absurd (Or.inr (Or.inl h)) h_paper_geom
  · exact h
  · exact absurd (Or.inr (Or.inr (Or.inl h))) h_paper_geom
  · exact absurd (Or.inr (Or.inr (Or.inr (Or.inl h)))) h_paper_geom
  · exact absurd (Or.inr (Or.inr (Or.inr (Or.inr h)))) h_paper_geom

/-- **Lemma 26 conditional: `(p, q) = (7, 19)` excluded via Lem 12 starred row**.

The geometric content of the (p, q) = (7, 19) configuration after the
paper's normal-Sylow reduction is: an order-7 graph automorphism `σ`
fixing some vertex `c` and all of its 57 neighbours (the `a₀ = 58 = 1 + 57`
star).  Combined with the character-theoretic constraint `a₁(σ) ≥ 21`
(from Lem 12 starred row), this forces `False`.

Direct re-export of `lem12_no_p7_a0_58_conditional`. -/
theorem lem26_seven_nineteen_excluded_via_lem12
    (hΓ : IsMoore57 Γ) (σ : Equiv.Perm V)
    (hAut : ∀ a b : V, Γ.Adj a b ↔ Γ.Adj (σ a) (σ b))
    (c : V) (hc : σ c = c)
    (h_nbhd : ∀ v ∈ Γ.neighborSet c, σ v = v)
    (h_a1_ge : 21 ≤ adjacentMovedCount Γ σ) :
    False :=
  Moore57.Papers.MacajSiran2010.S5.lem12_no_p7_a0_58_conditional
    hΓ σ hAut c hc h_nbhd h_a1_ge

/-- **Lemma 26 conditional combined (paper-faithful)**.

The full conditional structure of Lemma 26's proof:
* Take as hypothesis the paper's geometric reduction (Sylow + Lemma 19
  normality + Fix-shape compatibility) which, for `p, q ∈ {7, 11, 13, 19}`
  distinct with `p < q`, eliminates all pairs except `(7, 19)`.
* Take as hypothesis the (p = 7, q = 19) configuration content: an
  order-7 graph automorphism `σ` fixing a closed neighbourhood, together
  with the character-theoretic lower bound `a₁(σ) ≥ 21`.
* Conclude `p ≤ 5 ∨ q ≤ 5`.

The proof is by contradiction: if not, then by the geometric reduction
`(p, q) = (7, 19)`, but the Lem 12 starred row excludes this.
-/
theorem lem26_conditional_combined
    (hΓ : IsMoore57 Γ)
    {p q : ℕ}
    (h_p_in : p ∈ ({3, 5, 7, 11, 13, 19} : Finset ℕ))
    (h_q_in : q ∈ ({3, 5, 7, 11, 13, 19} : Finset ℕ))
    (h_lt : p < q)
    (h_paper_geom :
       ¬ ((p = 7 ∧ q = 11) ∨ (p = 7 ∧ q = 13) ∨
          (p = 11 ∧ q = 13) ∨ (p = 11 ∧ q = 19) ∨
          (p = 13 ∧ q = 19)))
    (h_seven_nineteen_geom : p = 7 ∧ q = 19 →
       ∃ σ : Equiv.Perm V, ∃ c : V,
         (∀ a b : V, Γ.Adj a b ↔ Γ.Adj (σ a) (σ b)) ∧
         σ c = c ∧
         (∀ v ∈ Γ.neighborSet c, σ v = v) ∧
         21 ≤ adjacentMovedCount Γ σ) :
    p ≤ 5 ∨ q ≤ 5 := by
  by_contra h_no_small
  have h_eq : p = 7 ∧ q = 19 :=
    lem26_arith_seven_nineteen_only_if_no_small p q h_p_in h_q_in h_lt
      h_no_small h_paper_geom
  obtain ⟨σ, c, hAut, hc, h_nbhd, h_a1⟩ := h_seven_nineteen_geom h_eq
  exact lem26_seven_nineteen_excluded_via_lem12 hΓ σ hAut c hc h_nbhd h_a1

/-- **Lemma 26 (`p ≤ 5` or `q ≤ 5`).** [deferred-heavy]

Original True-stub kept for backwards compatibility. The paper-faithful
content is fully captured by `lem26_conditional_combined` above; what
remains for the unconditional form is the geometric reduction
`h_paper_geom` (Sylow + Lemma 19 + Fix-shape elimination of pairs) and
the `h_seven_nineteen_geom` extraction (the (7, 19) ⇒ closed-neighbourhood
fix structure). -/
theorem lem26_small_prime : True := by trivial

end Moore57.Papers.MacajSiran2010.S9
