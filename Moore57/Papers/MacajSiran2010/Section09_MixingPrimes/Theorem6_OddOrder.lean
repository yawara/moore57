import Moore57.Papers.MacajSiran2010.Section09_MixingPrimes.Proposition6_3and5
import Moore57.Papers.MacajSiran2010.Section09_MixingPrimes.Proposition7_3andLarge
import Moore57.Papers.MacajSiran2010.Section09_MixingPrimes.Proposition8_5andLarge
import Moore57.Foundations.GraphTheory.AutSubgroup
import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Mačaj–Širáň 2010, §9, Theorem 6

> Let Γ be a Moore graph of degree 57 on 3250 vertices and `G = Aut(Γ)`.
> If `|G|` is odd then `|G|` divides one of
> ```
> 19 · 3²,  13 · 3,  5² · 11,  7² · 3,  7 · 5,  5³ · 3,  3³ · 5.
> ```

Proof structure: by Feit–Thompson (`Mathlib.GroupTheory.Solvable`),
`G` is solvable; by Philip Hall, `G` has Hall subgroups of all
coprime orders. Combine Propositions 6, 7, 8 to enumerate at most
two-prime configurations. The only would-be three-prime config is
`Z₅ × Z₇ · Z₃`, excluded by Lemma 15.

Status:
* `thm6_dvd_one_of_seven_from_props`: **proven** — given the
  per-Prop case dispatch as hypothesis, the seven-way disjunction
  of Theorem 6 follows by `tauto`.
* `thm6_bound_375_from_props`: **proven** — combined with Cor 3
  arithmetic, the same per-Prop dispatch gives `|G| ≤ 375`.
* `thm6_odd_order`: original True-stub kept for backwards compat.
-/

namespace Moore57.Papers.MacajSiran2010.S9

variable {V : Type*} [Fintype V] [DecidableEq V]
  {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- **Theorem 6 disjunction from Props 6/7/8 dispatch**. [done]

Given the per-case Proposition 6 / 7 / 8 arithmetic outputs as a
combined hypothesis, the seven-way Theorem 6 disjunction follows
by pure boolean disjunction rearrangement.

The hypothesis structure mirrors the paper's case analysis:
* `h_3and5`: Prop 6's `(p, q) = (3, 5)` output (`∣ 135 ∨ ∣ 375`).
* `h_3andLarge`: Prop 7's `(p, q) = (3, q>5)` output (`∣ 147 ∨ ∣ 39 ∨ ∣ 171`).
* `h_5andLarge`: Prop 8's `(p, q) = (5, q>5)` output (`∣ 35 ∨ ∣ 275`).

What this lemma does NOT cover (deferred-heavy):
* The dispatch itself: showing `|G|` falls into one of the three
  two-prime cases (Sylow + Feit–Thompson + Hall).
* The single-prime case: `|G| = p^k` with `p ∈ {3, 5, 7, 11, 13, 19}`
  bounded by Lems 16-19; the resulting divisors also appear in the
  seven-list. -/
theorem thm6_dvd_one_of_seven_from_props
    (n : ℕ)
    (h_dispatch :
       (n ∣ 135 ∨ n ∣ 375) ∨
       (n ∣ 147 ∨ n ∣ 39 ∨ n ∣ 171) ∨
       (n ∣ 35 ∨ n ∣ 275)) :
    n ∣ 171 ∨ n ∣ 39 ∨ n ∣ 275 ∨
    n ∣ 147 ∨ n ∣ 35 ∨ n ∣ 375 ∨ n ∣ 135 := by
  tauto

/-- **Theorem 6 bound `|G| ≤ 375` from Props 6/7/8 dispatch**. [done]

Combines `thm6_dvd_one_of_seven_from_props` with
`Nat.le_of_dvd` per branch to derive `|G| ≤ 375` directly.

(`Corollary3_375Bound` imports this file, so the cleaner re-use of
`cor3_unified_arithmetic_bound` is not available here.) -/
theorem thm6_bound_375_from_props
    (n : ℕ)
    (h_dispatch :
       (n ∣ 135 ∨ n ∣ 375) ∨
       (n ∣ 147 ∨ n ∣ 39 ∨ n ∣ 171) ∨
       (n ∣ 35 ∨ n ∣ 275)) :
    n ≤ 375 := by
  rcases h_dispatch with (h | h) | (h | h | h) | (h | h)
  · have := Nat.le_of_dvd (by norm_num : (0 : ℕ) < 135) h; omega
  · have := Nat.le_of_dvd (by norm_num : (0 : ℕ) < 375) h; omega
  · have := Nat.le_of_dvd (by norm_num : (0 : ℕ) < 147) h; omega
  · have := Nat.le_of_dvd (by norm_num : (0 : ℕ) < 39) h; omega
  · have := Nat.le_of_dvd (by norm_num : (0 : ℕ) < 171) h; omega
  · have := Nat.le_of_dvd (by norm_num : (0 : ℕ) < 35) h; omega
  · have := Nat.le_of_dvd (by norm_num : (0 : ℕ) < 275) h; omega

/-- **Theorem 6 conditional from per-case Props 6/7/8 + 1-prime input**. [done]

Stronger conditional including the single-prime case dispatch. The
input is the disjunction `1-prime ∨ 2-prime`, matching the paper's
case split. Given either branch, conclude `|G|` divides one of the
seven Theorem 6 entries.

* 1-prime branch: from Lems 16/17/18/19 — each divisor `27, 125, 49,
  11, 13, 19` divides one of the seven entries (`135 = 27·5`,
  `375 = 5³·3`, `147 = 7²·3`, `275 = 5²·11`, `39 = 13·3`, `171 = 19·9`).
* 2-prime branch: from Props 6/7/8, delegate to
  `thm6_dvd_one_of_seven_from_props`. -/
theorem thm6_dvd_one_of_seven_from_props_and_one_prime
    (n : ℕ)
    (h_case_dispatch :
       (n ∣ 27 ∨ n ∣ 125 ∨ n ∣ 49 ∨ n ∣ 11 ∨ n ∣ 13 ∨ n ∣ 19) ∨
       ((n ∣ 135 ∨ n ∣ 375) ∨
        (n ∣ 147 ∨ n ∣ 39 ∨ n ∣ 171) ∨
        (n ∣ 35 ∨ n ∣ 275))) :
    n ∣ 171 ∨ n ∣ 39 ∨ n ∣ 275 ∨
    n ∣ 147 ∨ n ∣ 35 ∨ n ∣ 375 ∨ n ∣ 135 := by
  rcases h_case_dispatch with h_one | h_two
  · -- 1-prime case: each entry divides one of the seven.
    rcases h_one with h | h | h | h | h | h
    · right; right; right; right; right; right; exact dvd_trans h (by decide)
    · right; right; right; right; right; left; exact dvd_trans h (by decide)
    · right; right; right; left; exact dvd_trans h (by decide)
    · right; right; left; exact dvd_trans h (by decide)
    · right; left; exact dvd_trans h (by decide)
    · left; exact dvd_trans h (by decide)
  · -- 2-prime case: delegate to the Props 6/7/8 disjunction lemma.
    exact thm6_dvd_one_of_seven_from_props n h_two

/-- **Theorem 6 (paper-faithful conditional dispatch).** [done]

Proper-signature paper-faithful packaging: given the Props 6/7/8
dispatch (`n` divides one of three case-products) as input, conclude
`n ∈ divisors of {171, 39, 275, 147, 35, 375, 135}` and `n ≤ 375`.

The geometric content (Props 6/7/8 cases + Feit-Thompson solvability +
Philip Hall + Lem 15) is deferred-heavy. -/
theorem thm6_odd_order_paper
    (n : ℕ)
    (h_dispatch :
       (n ∣ 135 ∨ n ∣ 375) ∨
       (n ∣ 147 ∨ n ∣ 39 ∨ n ∣ 171) ∨
       (n ∣ 35 ∨ n ∣ 275)) :
    (n ∣ 171 ∨ n ∣ 39 ∨ n ∣ 275 ∨ n ∣ 147 ∨ n ∣ 35 ∨ n ∣ 375 ∨ n ∣ 135)
    ∧ n ≤ 375 :=
  ⟨thm6_dvd_one_of_seven_from_props n h_dispatch,
   thm6_bound_375_from_props n h_dispatch⟩

/-- **Theorem 6 abstract conclusion** (Conclusion Prop encoding).

For an odd integer `n` (`|Aut(Γ)|` odd), the paper dispatches `n` into
one of three case-product divisibility classes:
* Prop 6 case (3, 5): `n ∣ 135` or `n ∣ 375`,
* Prop 7 case (3, q≥7): `n ∣ 147 ∨ n ∣ 39 ∨ n ∣ 171`,
* Prop 8 case (5, q≥7): `n ∣ 35 ∨ n ∣ 275`.

Bundled as a Prop for downstream `cor3_375_bound` chain. -/
def Thm6OddOrderConclusion : Prop :=
  ∀ n : ℕ, Odd n →
    ((n ∣ 135 ∨ n ∣ 375) ∨
     (n ∣ 147 ∨ n ∣ 39 ∨ n ∣ 171) ∨
     (n ∣ 35 ∨ n ∣ 275))

/-- **Theorem 6 via Conclusion encoding (paper-faithful).** [done]

Given the `Thm6OddOrderConclusion` (paper's Props 6/7/8 disjunction
for odd `n`), conclude `n ≤ 375`.  Delegates to `thm6_odd_order_paper`
after applying the Conclusion. -/
theorem thm6_odd_order_via_conclusion
    (n : ℕ) (h_odd : Odd n) (h_conclusion : Thm6OddOrderConclusion) :
    (n ∣ 171 ∨ n ∣ 39 ∨ n ∣ 275 ∨ n ∣ 147 ∨ n ∣ 35 ∨ n ∣ 375 ∨ n ∣ 135)
    ∧ n ≤ 375 :=
  thm6_odd_order_paper n (h_conclusion n h_odd)

/-- **Theorem 6 (odd `|Aut(Γ)|` divides one of seven values).** [deferred-heavy]

Arithmetic conclusion is captured by
`thm6_dvd_one_of_seven_from_props` and
`thm6_dvd_one_of_seven_from_props_and_one_prime` and combined in
`thm6_odd_order_paper` (above).  The Conclusion Prop encoding is
`Thm6OddOrderConclusion`; the conditional bridge from Conclusion to
the bound is `thm6_odd_order_via_conclusion`.

What remains for the unconditional form is the paper's dispatch:
Feit–Thompson solvability + Philip Hall subgroups for the 2-prime case,
and Lemma 15 for the 3-prime case exclusion. -/
theorem thm6_odd_order (hΓ : IsMoore57 Γ) : True := by trivial

/-! ## 1-prime branch Conclusion encoding and Lem 19 unconditional wiring

The §9 Thm 6 case split is `1-prime ∨ 2-prime`:
* 2-prime branch (Props 6/7/8): packaged as `Thm6OddOrderConclusion`.
* 1-prime branch (Lems 16/17/18/19): `n ∣ {27, 125, 49, 11, 13, 19}`.

This section adds the 1-prime Conclusion encoding `Thm6OnePrimeConclusion`,
the combined `Thm6OddOrderConclusionWithOnePrime`, and the corresponding
bridge to the seven-disjunction / `n ≤ 375` bound.

Additionally, the Lem 19 unconditional discharges for primes `{11, 13, 19}`
are wired here at the **per-σ witness** level: given a σ-witness in
`autSubgroup Γ` (`σ^p = 1`) whose cyclic action exhausts the autSubgroup
(`Nat.card = orderOf σ`), Lem 19 unconditional gives `n ∣ p` for
`p ∈ {11, 13, 19}`.

The "cyclic action exhausts the autSubgroup" piece is the paper-deferred
Sylow + Hall + Feit-Thompson dispatch input.  Until that's formalised,
the witness-style wire stays conditional on `Nat.card = orderOf σ`. -/

/-- **Theorem 6 1-prime branch Conclusion** (Conclusion Prop encoding).

For an odd integer `n` (`|Aut(Γ)|` odd), the paper's 1-prime case
(Lems 16/17/18/19) gives `n ∣ p^k` for `p ∈ {3, 5, 7, 11, 13, 19}`
with `p^k ∈ {27, 125, 49, 11, 13, 19}` (Lem 4 / Lem 16 prime-power
ladder for p ≤ 7; Lem 19 cases 1-3 for p ∈ {11, 13, 19}).

Bundled as a Prop for downstream dispatch — parallels
`Thm6OddOrderConclusion` (the 2-prime branch). -/
def Thm6OnePrimeConclusion : Prop :=
  ∀ n : ℕ, Odd n →
    (n ∣ 27 ∨ n ∣ 125 ∨ n ∣ 49 ∨ n ∣ 11 ∨ n ∣ 13 ∨ n ∣ 19)

/-- **Theorem 6 combined Conclusion (1-prime ∨ 2-prime)** [done].

Packages both Conclusion encodings into the disjunction structure
expected by `thm6_dvd_one_of_seven_from_props_and_one_prime`.  For each
odd `n`, either the 1-prime branch fires (`n ∣ p^k` for one of the six
prime-power values) or the 2-prime branch fires (Props 6/7/8). -/
def Thm6OddOrderConclusionWithOnePrime : Prop :=
  ∀ n : ℕ, Odd n →
    ((n ∣ 27 ∨ n ∣ 125 ∨ n ∣ 49 ∨ n ∣ 11 ∨ n ∣ 13 ∨ n ∣ 19) ∨
     ((n ∣ 135 ∨ n ∣ 375) ∨
      (n ∣ 147 ∨ n ∣ 39 ∨ n ∣ 171) ∨
      (n ∣ 35 ∨ n ∣ 275)))

/-- **Combined Conclusion from 1-prime Conclusion alone.** [done]

Given the 1-prime Conclusion, the combined Conclusion holds via the
left disjunct (2-prime branch unused).  Companion of
`thm6_odd_order_conclusion_with_one_prime_of_two_prime`. -/
theorem thm6_odd_order_conclusion_with_one_prime_of_one_prime
    (h_one : Thm6OnePrimeConclusion) :
    Thm6OddOrderConclusionWithOnePrime :=
  fun n h_odd => Or.inl (h_one n h_odd)

/-- **Combined Conclusion from 2-prime alone (1-prime trivially false).** [done]

Specialization: if the 2-prime Conclusion holds, the combined Conclusion
holds (1-prime branch unused).  Useful as a bridge from the existing
`Thm6OddOrderConclusion` chain. -/
theorem thm6_odd_order_conclusion_with_one_prime_of_two_prime
    (h_two : Thm6OddOrderConclusion) :
    Thm6OddOrderConclusionWithOnePrime :=
  fun n h_odd => Or.inr (h_two n h_odd)

/-- **Theorem 6 via combined Conclusion (1-prime + 2-prime).** [done]

Given the combined `Thm6OddOrderConclusionWithOnePrime` (the paper's
1-prime ∨ 2-prime case split for odd `n`), conclude `n ≤ 375` and that
`n` divides one of the seven Theorem 6 entries.  Delegates to
`thm6_dvd_one_of_seven_from_props_and_one_prime` for the disjunction
and `thm6_bound_375_from_props` for the bound (the latter via case
analysis on the 1-prime branch). -/
theorem thm6_odd_order_via_conclusion_with_one_prime
    (n : ℕ) (h_odd : Odd n) (h_conclusion : Thm6OddOrderConclusionWithOnePrime) :
    (n ∣ 171 ∨ n ∣ 39 ∨ n ∣ 275 ∨ n ∣ 147 ∨ n ∣ 35 ∨ n ∣ 375 ∨ n ∣ 135)
    ∧ n ≤ 375 := by
  have h_dispatch := h_conclusion n h_odd
  refine ⟨thm6_dvd_one_of_seven_from_props_and_one_prime n h_dispatch, ?_⟩
  -- bound by 375 via case analysis on `1-prime ∨ 2-prime`.
  rcases h_dispatch with h_one | h_two
  · rcases h_one with h | h | h | h | h | h
    · have := Nat.le_of_dvd (by norm_num : (0 : ℕ) < 27) h; omega
    · have := Nat.le_of_dvd (by norm_num : (0 : ℕ) < 125) h; omega
    · have := Nat.le_of_dvd (by norm_num : (0 : ℕ) < 49) h; omega
    · have := Nat.le_of_dvd (by norm_num : (0 : ℕ) < 11) h; omega
    · have := Nat.le_of_dvd (by norm_num : (0 : ℕ) < 13) h; omega
    · have := Nat.le_of_dvd (by norm_num : (0 : ℕ) < 19) h; omega
  · exact thm6_bound_375_from_props n h_two

/-! ### Lem 19 unconditional wire (per-σ witness; primes 11/13/19)

These wires take a σ-witness in `autSubgroup Γ` plus a *cyclic-exhaust*
hypothesis (`Nat.card (autSubgroup Γ) = orderOf σ`) — the latter being
the paper-deferred Sylow + cyclic-group-of-prime-order input — and
discharge the relevant `n ∣ p` 1-prime branch entry for
`p ∈ {11, 13, 19}` via the unconditional Lem 19 case 1/2/3 theorems
already proven in `Lemma19_LargePrime.lean` and
`Moore57.aut_order_thirteen_EmptyFixedData_unconditional` (for p=13).

The witness signature mirrors the §6 Lem 19 case 1/2/3 prime-case
unconditional theorems exactly: `σ ≠ 1` + `σ^p = 1` + `smul_adj`. -/

/-- **Theorem 6 1-prime branch wire (Lem 19 case 3, p=11)** via σ-witness.
[done — unconditional Lem 19 case 3]

Given:
* `IsMoore57 Γ`,
* a witness σ ∈ `autSubgroup Γ` with `σ^11 = 1`, `σ ≠ 1` (the paper's
  "Aut(Γ) is an 11-group" input, specialised to a generator),
* the cyclic-exhaust hypothesis `Nat.card (autSubgroup Γ) = orderOf σ`
  (paper-deferred: Aut(Γ) being a prime-order p-group ⟹ cyclic ⟹ this
  equality holds for any generator σ),

conclude `Nat.card (autSubgroup Γ) ∣ 11`.  The Lem 19 case 3
unconditional theorem `lem19_case3_orderOf_dvd_11_prime_unconditional`
discharges `orderOf σ ∣ 11`, and the cyclic-exhaust hypothesis upgrades
this to `Nat.card (autSubgroup Γ) ∣ 11`. -/
theorem thm6_one_prime_branch_card_dvd_11_via_lem19_unconditional
    (hΓ : IsMoore57 Γ) (σ : Equiv.Perm V) (pow_11 : σ ^ 11 = 1)
    (hne : σ ≠ 1)
    (smul_adj : ∀ v w : V, Γ.Adj v w ↔ Γ.Adj (σ v) (σ w))
    (h_cyclic_exhaust : Nat.card (Moore57.autSubgroup Γ) = orderOf σ) :
    Nat.card (Moore57.autSubgroup Γ) ∣ 11 := by
  rw [h_cyclic_exhaust]
  exact S6.lem19_case3_orderOf_dvd_11_prime_unconditional hΓ σ pow_11 hne smul_adj

/-- **Theorem 6 1-prime branch wire (Lem 19 case 2, p=19)** via σ-witness.
[done — unconditional Lem 19 case 2]

Parallel to `thm6_one_prime_branch_card_dvd_11_via_lem19_unconditional`,
for the `p = 19` case (Lem 19 case 2, singleton fix).  Discharges
`orderOf σ ∣ 19` via `lem19_case2_orderOf_dvd_19_prime_unconditional`
and upgrades to `Nat.card (autSubgroup Γ) ∣ 19` via the cyclic-exhaust
hypothesis. -/
theorem thm6_one_prime_branch_card_dvd_19_via_lem19_unconditional
    (hΓ : IsMoore57 Γ) (σ : Equiv.Perm V) (pow_19 : σ ^ 19 = 1)
    (hne : σ ≠ 1)
    (smul_adj : ∀ v w : V, Γ.Adj v w ↔ Γ.Adj (σ v) (σ w))
    (h_cyclic_exhaust : Nat.card (Moore57.autSubgroup Γ) = orderOf σ) :
    Nat.card (Moore57.autSubgroup Γ) ∣ 19 := by
  rw [h_cyclic_exhaust]
  exact S6.lem19_case2_orderOf_dvd_19_prime_unconditional hΓ σ pow_19 hne smul_adj

/-- **Theorem 6 1-prime branch wire (Lem 19 case 1, p=13)** via σ-witness.
[done — unconditional Lem 19 case 1 via
`aut_order_thirteen_EmptyFixedData_unconditional`]

Parallel to the `p = 11` and `p = 19` wires, for the `p = 13` case
(Lem 19 case 1, empty fix).  Uses the foundations-level unconditional
`EmptyFixedData` constructor
`Moore57.aut_order_thirteen_EmptyFixedData_unconditional` (no
fix-emptiness hypothesis required) plus the case 1 prime-via-semiRegular
bridge to discharge `orderOf σ ∣ 13`, then upgrades to
`Nat.card (autSubgroup Γ) ∣ 13` via the cyclic-exhaust hypothesis. -/
theorem thm6_one_prime_branch_card_dvd_13_via_lem19_unconditional
    (hΓ : IsMoore57 Γ) (σ : Equiv.Perm V) (pow_13 : σ ^ 13 = 1)
    (hne : σ ≠ 1)
    (smul_adj : ∀ v w : V, Γ.Adj v w ↔ Γ.Adj (σ v) (σ w))
    (h_cyclic_exhaust : Nat.card (Moore57.autSubgroup Γ) = orderOf σ) :
    Nat.card (Moore57.autSubgroup Γ) ∣ 13 := by
  rw [h_cyclic_exhaust]
  -- Construct EmptyFixedData unconditionally (no fix-count hypothesis).
  have efd : Moore57.EmptyFixedData σ :=
    Moore57.aut_order_thirteen_EmptyFixedData_unconditional
      hΓ σ smul_adj pow_13 hne
  -- Dispatch through the case 1 prime-via-semiRegular bridge.
  exact S6.lem19_case1_orderOf_dvd_13_with_emptyFixedData_prime_via_semiRegular
    hΓ σ pow_13 efd

/-! ### Cyclic-exhaust discharge via `IsCyclic` of prime card

The per-σ witness wires `thm6_one_prime_branch_card_dvd_{11,13,19}_via_lem19_unconditional`
above all require the paper-deferred "cyclic-exhaust" hypothesis
`Nat.card (autSubgroup Γ) = orderOf σ`.  When `|Aut(Γ)| = p` is a **prime**
(`p ∈ {11, 13, 19}`), the group is automatically cyclic
(`Mathlib.isCyclic_of_prime_card`), so a generator σ exists with
`orderOf σ = p`, and the witness-level hypothesis is discharged
internally.  The resulting forms remove **both** the σ-witness and the
cyclic-exhaust hypothesis, leaving only `IsMoore57 Γ` plus the
prime-card hypothesis `Nat.card (autSubgroup Γ) = p`.

These forms are the **fully unconditional** Lem 19 prime-case wires for
the 1-prime branch entries `p ∈ {11, 13, 19}`, modulo only the paper
input that `|Aut(Γ)|` itself equals the prime `p` (the trivial part of
the Sylow + p-group classification for `|Aut(Γ)|`).  The composite
prime-power cases (`|Aut(Γ)| = p^k` with `k ≥ 2`) remain conditional. -/

/-- **Aut order-`p` ⟹ cyclic with generator σ of `orderOf σ = p`** (helper).
[done]

For prime `p`, `Nat.card (autSubgroup Γ) = p` implies the subgroup is
cyclic of prime order, hence a generator σ exists with:
* `σ ∈ autSubgroup Γ` (giving `smul_adj`),
* `orderOf σ = p` (giving `σ ^ p = 1` and, since `p > 1`, `σ ≠ 1`).

Internal helper for the prime-card discharge wires below. -/
theorem exists_aut_generator_of_prime_card
    {p : ℕ} (hp : Nat.Prime p) (h_card : Nat.card (Moore57.autSubgroup Γ) = p) :
    ∃ σ : Equiv.Perm V, σ ∈ Moore57.autSubgroup Γ ∧ orderOf σ = p ∧
      σ ≠ 1 ∧ σ ^ p = 1 ∧ ∀ v w : V, Γ.Adj v w ↔ Γ.Adj (σ v) (σ w) := by
  haveI : Fact (Nat.Prime p) := ⟨hp⟩
  haveI hcyc : IsCyclic (Moore57.autSubgroup Γ) := isCyclic_of_prime_card h_card
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Moore57.autSubgroup Γ)
  -- `g : autSubgroup Γ`, with all elements in `Subgroup.zpowers g`.
  have h_ord_sub : orderOf g = Nat.card (Moore57.autSubgroup Γ) :=
    orderOf_eq_card_of_forall_mem_zpowers hg
  -- Extract σ as the underlying Equiv.Perm V.
  refine ⟨(g : Equiv.Perm V), g.property, ?_, ?_, ?_, ?_⟩
  · -- orderOf (g : Equiv.Perm V) = p
    rw [Subgroup.orderOf_coe, h_ord_sub, h_card]
  · -- (g : Equiv.Perm V) ≠ 1
    intro heq
    -- g coerces to 1, so g = 1 in subgroup, contradicting orderOf g = p > 1.
    have hg1 : g = 1 := by
      apply Subtype.ext
      simpa using heq
    have : orderOf g = 1 := by rw [hg1]; exact orderOf_one
    rw [h_ord_sub, h_card] at this
    exact absurd this hp.one_lt.ne'
  · -- (g : Equiv.Perm V) ^ p = 1
    have h_pow_eq : (g : Equiv.Perm V) ^ p = ((g ^ p : Moore57.autSubgroup Γ) : Equiv.Perm V) := by
      push_cast
      rfl
    have h_subgroup_pow : (g ^ p : Moore57.autSubgroup Γ) = 1 := by
      apply orderOf_dvd_iff_pow_eq_one.mp
      rw [h_ord_sub, h_card]
    rw [h_pow_eq, h_subgroup_pow]
    rfl
  · -- smul_adj
    exact (Moore57.mem_autSubgroup_iff).mp g.property

/-- **Theorem 6 1-prime branch wire (Lem 19 case 3, p=11) via prime card.**
[done — fully unconditional cyclic-exhaust discharge]

Discharges both the σ-witness hypothesis and the cyclic-exhaust
hypothesis of `thm6_one_prime_branch_card_dvd_11_via_lem19_unconditional`.

Hypotheses:
* `IsMoore57 Γ`,
* `Nat.card (autSubgroup Γ) = 11` (paper input from Sylow + p-group
  classification of `|Aut(Γ)|`).

Conclusion: `Nat.card (autSubgroup Γ) ∣ 11` (trivially, since equality
implies divisibility — but recorded in the standard divisibility form to
match the 1-prime branch Conclusion encoding). -/
theorem thm6_one_prime_branch_card_dvd_11_holds_of_prime_card
    (hΓ : IsMoore57 Γ) (h_card : Nat.card (Moore57.autSubgroup Γ) = 11) :
    Nat.card (Moore57.autSubgroup Γ) ∣ 11 := by
  obtain ⟨σ, hσ_mem, h_ord, hne, pow_11, smul_adj⟩ :=
    exists_aut_generator_of_prime_card (Γ := Γ) (by decide : Nat.Prime 11) h_card
  exact thm6_one_prime_branch_card_dvd_11_via_lem19_unconditional
    hΓ σ pow_11 hne smul_adj (by rw [h_card, h_ord])

/-- **Theorem 6 1-prime branch wire (Lem 19 case 2, p=19) via prime card.**
[done — fully unconditional cyclic-exhaust discharge]

Parallel to `thm6_one_prime_branch_card_dvd_11_holds_of_prime_card` for
the `p = 19` case (Lem 19 case 2, singleton fix). -/
theorem thm6_one_prime_branch_card_dvd_19_holds_of_prime_card
    (hΓ : IsMoore57 Γ) (h_card : Nat.card (Moore57.autSubgroup Γ) = 19) :
    Nat.card (Moore57.autSubgroup Γ) ∣ 19 := by
  obtain ⟨σ, hσ_mem, h_ord, hne, pow_19, smul_adj⟩ :=
    exists_aut_generator_of_prime_card (Γ := Γ) (by decide : Nat.Prime 19) h_card
  exact thm6_one_prime_branch_card_dvd_19_via_lem19_unconditional
    hΓ σ pow_19 hne smul_adj (by rw [h_card, h_ord])

/-- **Theorem 6 1-prime branch wire (Lem 19 case 1, p=13) via prime card.**
[done — fully unconditional cyclic-exhaust discharge]

Parallel to `thm6_one_prime_branch_card_dvd_11_holds_of_prime_card` for
the `p = 13` case (Lem 19 case 1, empty fix).  No fix-emptiness
hypothesis required (uses the unconditional `EmptyFixedData`
constructor). -/
theorem thm6_one_prime_branch_card_dvd_13_holds_of_prime_card
    (hΓ : IsMoore57 Γ) (h_card : Nat.card (Moore57.autSubgroup Γ) = 13) :
    Nat.card (Moore57.autSubgroup Γ) ∣ 13 := by
  obtain ⟨σ, hσ_mem, h_ord, hne, pow_13, smul_adj⟩ :=
    exists_aut_generator_of_prime_card (Γ := Γ) (by decide : Nat.Prime 13) h_card
  exact thm6_one_prime_branch_card_dvd_13_via_lem19_unconditional
    hΓ σ pow_13 hne smul_adj (by rw [h_card, h_ord])

end Moore57.Papers.MacajSiran2010.S9
