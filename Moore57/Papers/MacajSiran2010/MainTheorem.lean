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
* `aut_card_le_375`: original True-stub kept for backwards compat.
-/

namespace Moore57.Papers.MacajSiran2010

variable {V : Type*} [Fintype V] [DecidableEq V]
  {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

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
  Moore57.Papers.MacajSiran2010.S9.cor3_bound_from_props_and_oddpart
    n h_odd_props h_even_oddpart

/-- **Main theorem (Mačaj–Širáň 2010, Corollary 3).** `|Aut(Γ)| ≤ 375`.
[deferred-heavy]

The unconditional form awaits the `Aut(Γ)` ↔ subgroup-of-Sym(V)
bridge and the per-section geometric content (Thms 4/5, Props 6/7/8). -/
theorem aut_card_le_375 (hΓ : IsMoore57 Γ) : True := by trivial

end Moore57.Papers.MacajSiran2010
