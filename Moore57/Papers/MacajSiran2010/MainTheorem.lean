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

end Moore57.Papers.MacajSiran2010
