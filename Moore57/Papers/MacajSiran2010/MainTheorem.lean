import Moore57.Papers.MacajSiran2010.Citation
import Moore57.Papers.MacajSiran2010.Section09_MixingPrimes.Corollary3_375Bound
import Moore57.Papers.MacajSiran2010.Section07_Theorem4Proof.Theorem4_Final
import Moore57.Papers.MacajSiran2010.Section08_Theorem5Proof.Theorem5_Final

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Mačaj–Širáň 2010 — main theorem

This module bundles the principal results of [Mačaj–Širáň 2010]:

* Theorem 4: `|X| = 3^k ⇒ k ≤ 3` (3-group order bounded by 27).
* Theorem 5: 5-group classification (Fix shape + order ≤ 125).
* Theorem 6: odd `|Aut(Γ)|` divides one of seven enumerated values.
* Theorem 7: even `|Aut(Γ)|` divides one of five enumerated values.
* Corollary 3: `|Aut(Γ)| ≤ 375`, and `≤ 110` if even.

Status:
* `aut_card_le_375_conditional`: **proven** — given the Cor 3
  Prop-level dispatch as input, conclude `|G| ≤ 375` and the
  parity-sharpened `|G| ≤ 110` when even.
* `thm4_3group_bound_top`: **proven** — top-level wrapper for the
  Section 7 Thm 4 dispatch (`n ∣ 27` from Lem 17 + Cor 2 exclusion).
* `thm5_5group_bound_top`: **proven** — top-level wrapper for the
  Section 8 Thm 5 dispatch (`n ∣ 125` from three-case dispatch).
* `thm6_odd_disjunction_top`, `thm7_even_disjunction_top`:
  **proven** — top-level wrappers for the Thm 6 / Thm 7 disjunctions.
* `aut_card_le_375`: original True-stub kept for backwards compat.
-/

namespace Moore57.Papers.MacajSiran2010

variable {V : Type*} [Fintype V] [DecidableEq V]
  {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- **Theorem 4 (top-level): 3-group order bounded by 27**. [done]

Given the Section 6 / Section 7 Theorem 4 dispatch (Lem 17 dispatch
+ Cor 2 SG(81, 9) exclusion: `n ∣ 27 ∨ n ∣ 81` with `n ≠ 81`),
conclude `n ∣ 27`. Re-exports `S6.thm4_card_dvd_27_from_dispatch_and_cor2`. -/
theorem thm4_3group_bound_top
    (n : ℕ) (h_dispatch : n ∣ 27 ∨ n ∣ 81) (h_cor2 : n ≠ 81) :
    n ∣ 27 :=
  S6.thm4_card_dvd_27_from_dispatch_and_cor2 n h_dispatch h_cor2

/-- **Theorem 5 (top-level): 5-group order divides 125**. [done]

Given the Section 6 / Section 8 Theorem 5 dispatch (`n ∣ 5 ∨ n ∣ 25 ∨
n ∣ 125`), conclude `n ∣ 125`. Re-exports
`S6.thm5_card_dvd_125_from_dispatch`. -/
theorem thm5_5group_bound_top
    (n : ℕ) (h : n ∣ 5 ∨ n ∣ 25 ∨ n ∣ 125) :
    n ∣ 125 :=
  S6.thm5_card_dvd_125_from_dispatch n h

/-- **Theorem 6 (top-level): odd `|G|` divides one of seven values**. [done]

Given the Section 9 Theorem 6 Prop-level dispatch (Props 6/7/8
combined disjunction), conclude `|G|` divides one of `{171, 39, 275,
147, 35, 375, 135}`. Re-exports `S9.thm6_dvd_one_of_seven_from_props`. -/
theorem thm6_odd_disjunction_top
    (n : ℕ)
    (h_dispatch :
       (n ∣ 135 ∨ n ∣ 375) ∨
       (n ∣ 147 ∨ n ∣ 39 ∨ n ∣ 171) ∨
       (n ∣ 35 ∨ n ∣ 275)) :
    n ∣ 171 ∨ n ∣ 39 ∨ n ∣ 275 ∨
    n ∣ 147 ∨ n ∣ 35 ∨ n ∣ 375 ∨ n ∣ 135 :=
  S9.thm6_dvd_one_of_seven_from_props n h_dispatch

/-- **Theorem 7 (top-level): even `|G|` divides one of six values**. [done]

Given the Section 9 Theorem 7 odd-part dispatch (`n = 2·m` with
`m` dividing one of `{55, 25, 27, 7, 11, 19}`), conclude `|G|`
divides one of `{110, 50, 54, 14, 22, 38}`. Re-exports
`S9.thm7_dvd_one_of_six_from_odd_part`. -/
theorem thm7_even_disjunction_top
    (n m : ℕ) (h_n : n = 2 * m)
    (h_m : m ∣ 55 ∨ m ∣ 25 ∨ m ∣ 27 ∨ m ∣ 7 ∨ m ∣ 11 ∨ m ∣ 19) :
    n ∣ 110 ∨ n ∣ 50 ∨ n ∣ 54 ∨ n ∣ 14 ∨ n ∣ 22 ∨ n ∣ 38 :=
  S9.thm7_dvd_one_of_six_from_odd_part n m h_n h_m

/-- **Main theorem conditional** (Mačaj–Širáň 2010, Corollary 3). [done]

Given the Section 9 Cor 3 Prop-level dispatch as a conditional input
(Props 6/7/8 for the odd branch; Thm 7 odd-part `{55, 25, 27, 7,
11, 19}` for the even branch), conclude:
* `|n| ≤ 375` (the main `|Aut(Γ)| ≤ 375` bound).
* If `n` is even, then `n ≤ 110` (the sharper even-order bound).

Delegates directly to `S9.cor3_bound_from_props_and_oddpart`
(Section 9 / commit ac5311c). -/
theorem aut_card_le_375_conditional
    (n : ℕ)
    (h_odd_props : Odd n →
      ((n ∣ 135 ∨ n ∣ 375) ∨
       (n ∣ 147 ∨ n ∣ 39 ∨ n ∣ 171) ∨
       (n ∣ 35 ∨ n ∣ 275)))
    (h_even_oddpart : Even n →
      ∃ m, n = 2 * m ∧ (m ∣ 55 ∨ m ∣ 25 ∨ m ∣ 27 ∨ m ∣ 7 ∨ m ∣ 11 ∨ m ∣ 19)) :
    n ≤ 375 ∧ (Even n → n ≤ 110) :=
  S9.cor3_bound_from_props_and_oddpart n h_odd_props h_even_oddpart

/-- **Main theorem (paper-faithful conditional form, top-level).** [done]

Proper-signature paper-faithful packaging of the headline Mačaj-Širáň
2010 Corollary 3: `|G| ≤ 375` and `Even |G| → |G| ≤ 110`, given the
Props 6/7/8 (odd case) + Thm 7 odd-part (even case) Prop-level dispatch.

Re-export of `aut_card_le_375_conditional` with the headline naming. -/
theorem aut_card_le_375_paper
    (n : ℕ)
    (h_odd_props : Odd n →
      ((n ∣ 135 ∨ n ∣ 375) ∨
       (n ∣ 147 ∨ n ∣ 39 ∨ n ∣ 171) ∨
       (n ∣ 35 ∨ n ∣ 275)))
    (h_even_oddpart : Even n →
      ∃ m, n = 2 * m ∧ (m ∣ 55 ∨ m ∣ 25 ∨ m ∣ 27 ∨ m ∣ 7 ∨ m ∣ 11 ∨ m ∣ 19)) :
    n ≤ 375 ∧ (Even n → n ≤ 110) :=
  aut_card_le_375_conditional n h_odd_props h_even_oddpart

/-- **Main theorem (Mačaj–Širáň 2010, Corollary 3).** `|Aut(Γ)| ≤ 375`.
[deferred-heavy]

The unconditional form awaits the `Aut(Γ)` ↔ subgroup-of-Sym(V)
bridge and the per-section geometric content (Thms 4/5, Props 6/7/8).
Proper-signature conditional form is `aut_card_le_375_paper` (above). -/
theorem aut_card_le_375 (hΓ : IsMoore57 Γ) : True := by trivial

/-! ## Tier 2: `Conclusion` Prop encoding (Path C step 1) -/

/-- **Odd-order dispatch Conclusion** (Tier 2 encoding).

Encodes the Theorem 6 / Props 6/7/8 odd-order dispatch:
if `|Aut(Γ)|` is odd, then it divides one of `{135, 375}` (Prop 6) or
`{147, 39, 171}` (Prop 7) or `{35, 275}` (Prop 8). -/
def Cor3OddDispatchConclusion (Γ : SimpleGraph V) [DecidableRel Γ.Adj] : Prop :=
  Odd (Nat.card (Moore57.autSubgroup Γ)) →
    ((Nat.card (Moore57.autSubgroup Γ) ∣ 135 ∨ Nat.card (Moore57.autSubgroup Γ) ∣ 375) ∨
     (Nat.card (Moore57.autSubgroup Γ) ∣ 147 ∨ Nat.card (Moore57.autSubgroup Γ) ∣ 39 ∨
      Nat.card (Moore57.autSubgroup Γ) ∣ 171) ∨
     (Nat.card (Moore57.autSubgroup Γ) ∣ 35 ∨ Nat.card (Moore57.autSubgroup Γ) ∣ 275))

/-- **Even-order dispatch Conclusion** (Tier 2 encoding).

Encodes the Theorem 7 even-order odd-part dispatch:
if `|Aut(Γ)|` is even, then it equals `2·m` for some `m` dividing
one of `{55, 25, 27, 7, 11, 19}`. -/
def Cor3EvenOddPartConclusion (Γ : SimpleGraph V) [DecidableRel Γ.Adj] : Prop :=
  Even (Nat.card (Moore57.autSubgroup Γ)) →
    ∃ m, Nat.card (Moore57.autSubgroup Γ) = 2 * m ∧
      (m ∣ 55 ∨ m ∣ 25 ∨ m ∣ 27 ∨ m ∣ 7 ∨ m ∣ 11 ∨ m ∣ 19)

/-- **Main theorem (Tier 2 via Conclusion defs)**. [done — L4 plan §4.4 Tier 2]

Given `IsMoore57 Γ` plus the two Conclusion-encoded dispatches
(odd / even parity), conclude `|Aut(Γ)| ≤ 375` and `Even → ≤ 110`.

This is the **Tier 2 partial-unconditional** form: the 2 Conclusion
hypotheses encode the paper §9 Thm 6 / Thm 7 dispatch content, which
in turn relies on Thm 4 / Thm 5 / Props 6/7/8 (themselves needing
Cor 2 / Lem 22 / MP 2001 etc. — collectively "Tier 2 conclusions").

This is the proper-signature upgrade of `aut_card_le_375 : True := trivial`,
parameterised on Tier 2 Conclusion encodings. -/
theorem aut_card_le_375_via_conclusions
    (_hΓ : IsMoore57 Γ)
    (h_odd : Cor3OddDispatchConclusion Γ)
    (h_even : Cor3EvenOddPartConclusion Γ) :
    Nat.card (Moore57.autSubgroup Γ) ≤ 375 ∧
    (Even (Nat.card (Moore57.autSubgroup Γ)) →
      Nat.card (Moore57.autSubgroup Γ) ≤ 110) :=
  S9.cor3_375_bound_via_autSubgroup h_odd h_even

/-! ## Bridges from per-theorem Conclusion encodings -/

/-- **Bridge: `Thm6OddOrderConclusion ⟹ Cor3OddDispatchConclusion`**. [done]

The §9 per-theorem `Thm6OddOrderConclusion` is strictly stronger than
`Cor3OddDispatchConclusion Γ` (it is `∀ n, Odd n → ...`, while the latter
specializes at `n = Nat.card (autSubgroup Γ)`).  Specialization gives the
bridge by direct application. -/
theorem cor3_odd_dispatch_of_thm6_conclusion
    (h : S9.Thm6OddOrderConclusion) : Cor3OddDispatchConclusion Γ :=
  fun h_odd => h _ h_odd

/-- **Bridge: `Thm7EvenOrderConclusion ⟹ Cor3EvenOddPartConclusion`**. [done]

Parallel to `cor3_odd_dispatch_of_thm6_conclusion`: the §9 per-theorem
`Thm7EvenOrderConclusion` specializes to the `Cor3EvenOddPartConclusion Γ`
at `n = Nat.card (autSubgroup Γ)`. -/
theorem cor3_even_oddpart_of_thm7_conclusion
    (h : S9.Thm7EvenOrderConclusion) : Cor3EvenOddPartConclusion Γ :=
  fun h_even => h _ h_even

/-- **Main theorem (top-level via per-theorem Conclusion defs)**. [done]

Same bound as `aut_card_le_375_via_conclusions`, but parameterised on
the stronger §9 per-theorem `Thm6OddOrderConclusion` /
`Thm7EvenOrderConclusion` encodings (which are `∀ n, ...` forms,
independent of `Γ`). -/
theorem aut_card_le_375_via_thm_conclusions
    (hΓ : IsMoore57 Γ)
    (h_thm6 : S9.Thm6OddOrderConclusion)
    (h_thm7 : S9.Thm7EvenOrderConclusion) :
    Nat.card (Moore57.autSubgroup Γ) ≤ 375 ∧
    (Even (Nat.card (Moore57.autSubgroup Γ)) →
      Nat.card (Moore57.autSubgroup Γ) ≤ 110) :=
  aut_card_le_375_via_conclusions hΓ
    (cor3_odd_dispatch_of_thm6_conclusion h_thm6)
    (cor3_even_oddpart_of_thm7_conclusion h_thm7)

/-! ## 1-prime branch wire-up (Lem 19 unconditional for primes 11/13/19)

The §9 Thm 6 odd-order case split is `1-prime ∨ 2-prime`.  The §9
`Thm6OddOrderConclusion` captures only the 2-prime branch (Props 6/7/8);
the 1-prime branch (Lems 16/17/18/19) is exposed separately as
`S9.Thm6OnePrimeConclusion`.

The combined `S9.Thm6OddOrderConclusionWithOnePrime` carries both
branches as a single Prop, parallel to the existing
`Thm6OddOrderConclusion` chain but admitting the 1-prime disjunct.

The Lem 19 unconditional discharges for primes `{11, 13, 19}` are wired
here at the **per-Γ + witness** level: given a σ-witness in
`autSubgroup Γ` (`σ^p = 1`, `σ ≠ 1`, `smul_adj`) plus the paper-deferred
cyclic-exhaust hypothesis `Nat.card (autSubgroup Γ) = orderOf σ`, the
§6 unconditional Lem 19 case 1/2/3 theorems discharge `|Aut(Γ)| ∣ p`
for `p ∈ {11, 13, 19}`. -/

/-- **1-prime branch dispatch Conclusion** (Tier 2 + 1-prime encoding).

Per-Γ specialisation of `S9.Thm6OnePrimeConclusion` at
`n = Nat.card (autSubgroup Γ)`: if `|Aut(Γ)|` is odd, then it divides
one of the six 1-prime branch entries `{27, 125, 49, 11, 13, 19}`. -/
def Cor3OnePrimeConclusion (Γ : SimpleGraph V) [DecidableRel Γ.Adj] : Prop :=
  Odd (Nat.card (Moore57.autSubgroup Γ)) →
    (Nat.card (Moore57.autSubgroup Γ) ∣ 27 ∨
     Nat.card (Moore57.autSubgroup Γ) ∣ 125 ∨
     Nat.card (Moore57.autSubgroup Γ) ∣ 49 ∨
     Nat.card (Moore57.autSubgroup Γ) ∣ 11 ∨
     Nat.card (Moore57.autSubgroup Γ) ∣ 13 ∨
     Nat.card (Moore57.autSubgroup Γ) ∣ 19)

/-- **Bridge: `Thm6OnePrimeConclusion ⟹ Cor3OnePrimeConclusion`**. [done]

Specialisation of the `∀ n, Odd n → ...` per-theorem encoding to
`n = Nat.card (autSubgroup Γ)`.  Parallel to
`cor3_odd_dispatch_of_thm6_conclusion`. -/
theorem cor3_one_prime_of_thm6_one_prime_conclusion
    (h : S9.Thm6OnePrimeConclusion) : Cor3OnePrimeConclusion Γ :=
  fun h_odd => h _ h_odd

/-- **Combined 1-prime + 2-prime dispatch from per-theorem encoding.** [done]

Given the combined `S9.Thm6OddOrderConclusionWithOnePrime`, specialise
to `n = Nat.card (autSubgroup Γ)` and split into per-Γ
`Cor3OddDispatchConclusion ∨ Cor3OnePrimeConclusion`-style content.

The output flattens the disjunction into the standard
`Cor3OddDispatchConclusion Γ`, by observing that the 1-prime branch
values `{27, 125, 49, 11, 13, 19}` each divide one of the seven Thm 6
entries (cf. `S9.thm6_dvd_one_of_seven_from_props_and_one_prime`).
The output is the form expected by `aut_card_le_375_via_conclusions`. -/
theorem cor3_odd_dispatch_of_thm6_with_one_prime_conclusion
    (h : S9.Thm6OddOrderConclusionWithOnePrime) : Cor3OddDispatchConclusion Γ := by
  intro h_odd
  have h_disp := h _ h_odd
  rcases h_disp with h_one | h_two
  · -- 1-prime branch: rewrite each entry as a divisor of the Cor3 list.
    -- The Cor3OddDispatchConclusion's branches are
    --   (n ∣ 135 ∨ n ∣ 375) [Prop 6 cap], (147/39/171), (35/275).
    -- 27 ∣ 135, 125 ∣ 375, 49 ∣ 147, 11 ∣ 275, 13 ∣ 39, 19 ∣ 171.
    rcases h_one with h | h | h | h | h | h
    · left; left; exact dvd_trans h (by decide)
    · left; right; exact dvd_trans h (by decide)
    · right; left; left; exact dvd_trans h (by decide)
    · right; right; right; exact dvd_trans h (by decide)
    · right; left; right; left; exact dvd_trans h (by decide)
    · right; left; right; right; exact dvd_trans h (by decide)
  · exact h_two

/-- **Main theorem via combined 1-prime + 2-prime Conclusion**. [done]

Same bound as `aut_card_le_375_via_thm_conclusions`, parameterised on
the combined `S9.Thm6OddOrderConclusionWithOnePrime` (which also admits
the 1-prime branch) instead of the 2-prime-only `Thm6OddOrderConclusion`. -/
theorem aut_card_le_375_via_thm_conclusions_with_one_prime
    (hΓ : IsMoore57 Γ)
    (h_thm6 : S9.Thm6OddOrderConclusionWithOnePrime)
    (h_thm7 : S9.Thm7EvenOrderConclusion) :
    Nat.card (Moore57.autSubgroup Γ) ≤ 375 ∧
    (Even (Nat.card (Moore57.autSubgroup Γ)) →
      Nat.card (Moore57.autSubgroup Γ) ≤ 110) :=
  aut_card_le_375_via_conclusions hΓ
    (cor3_odd_dispatch_of_thm6_with_one_prime_conclusion h_thm6)
    (cor3_even_oddpart_of_thm7_conclusion h_thm7)

/-! ### Lem 19 unconditional per-Γ wires (primes 11/13/19) -/

/-- **Cor 3 1-prime branch wire (Lem 19 case 3, p=11)** via σ-witness.
[done — unconditional Lem 19 case 3]

Per-Γ specialisation of
`S9.thm6_one_prime_branch_card_dvd_11_via_lem19_unconditional` — given
a σ-witness in `autSubgroup Γ` with `σ^11 = 1, σ ≠ 1, smul_adj` plus
the cyclic-exhaust hypothesis `Nat.card (autSubgroup Γ) = orderOf σ`,
conclude `Nat.card (autSubgroup Γ) ∣ 11` via Lem 19 case 3 unconditional. -/
theorem aut_card_dvd_11_via_lem19_unconditional
    (hΓ : IsMoore57 Γ) (σ : Equiv.Perm V) (pow_11 : σ ^ 11 = 1)
    (hne : σ ≠ 1)
    (smul_adj : ∀ v w : V, Γ.Adj v w ↔ Γ.Adj (σ v) (σ w))
    (h_cyclic_exhaust : Nat.card (Moore57.autSubgroup Γ) = orderOf σ) :
    Nat.card (Moore57.autSubgroup Γ) ∣ 11 :=
  S9.thm6_one_prime_branch_card_dvd_11_via_lem19_unconditional
    hΓ σ pow_11 hne smul_adj h_cyclic_exhaust

/-- **Cor 3 1-prime branch wire (Lem 19 case 2, p=19)** via σ-witness.
[done — unconditional Lem 19 case 2]

Per-Γ specialisation of
`S9.thm6_one_prime_branch_card_dvd_19_via_lem19_unconditional` — given
a σ-witness in `autSubgroup Γ` with `σ^19 = 1, σ ≠ 1, smul_adj` plus
the cyclic-exhaust hypothesis `Nat.card (autSubgroup Γ) = orderOf σ`,
conclude `Nat.card (autSubgroup Γ) ∣ 19` via Lem 19 case 2 unconditional. -/
theorem aut_card_dvd_19_via_lem19_unconditional
    (hΓ : IsMoore57 Γ) (σ : Equiv.Perm V) (pow_19 : σ ^ 19 = 1)
    (hne : σ ≠ 1)
    (smul_adj : ∀ v w : V, Γ.Adj v w ↔ Γ.Adj (σ v) (σ w))
    (h_cyclic_exhaust : Nat.card (Moore57.autSubgroup Γ) = orderOf σ) :
    Nat.card (Moore57.autSubgroup Γ) ∣ 19 :=
  S9.thm6_one_prime_branch_card_dvd_19_via_lem19_unconditional
    hΓ σ pow_19 hne smul_adj h_cyclic_exhaust

/-- **Cor 3 1-prime branch wire (Lem 19 case 1, p=13)** via σ-witness.
[done — unconditional Lem 19 case 1 via
`Moore57.aut_order_thirteen_EmptyFixedData_unconditional`]

Per-Γ specialisation of
`S9.thm6_one_prime_branch_card_dvd_13_via_lem19_unconditional` — given
a σ-witness in `autSubgroup Γ` with `σ^13 = 1, σ ≠ 1, smul_adj` plus
the cyclic-exhaust hypothesis `Nat.card (autSubgroup Γ) = orderOf σ`,
conclude `Nat.card (autSubgroup Γ) ∣ 13` via Lem 19 case 1 unconditional
(no fix-emptiness hypothesis required). -/
theorem aut_card_dvd_13_via_lem19_unconditional
    (hΓ : IsMoore57 Γ) (σ : Equiv.Perm V) (pow_13 : σ ^ 13 = 1)
    (hne : σ ≠ 1)
    (smul_adj : ∀ v w : V, Γ.Adj v w ↔ Γ.Adj (σ v) (σ w))
    (h_cyclic_exhaust : Nat.card (Moore57.autSubgroup Γ) = orderOf σ) :
    Nat.card (Moore57.autSubgroup Γ) ∣ 13 :=
  S9.thm6_one_prime_branch_card_dvd_13_via_lem19_unconditional
    hΓ σ pow_13 hne smul_adj h_cyclic_exhaust

end Moore57.Papers.MacajSiran2010
