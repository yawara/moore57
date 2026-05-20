import Mathlib.Tactic.NormNum
import Moore57.Foundations.GraphTheory.AdjacentMovedCount
import Moore57.Papers.MacajSiran2010.Section07_Theorem4Proof.Corollary2_SmallGroup81_9
import Moore57.Papers.MacajSiran2010.Section06_PGroupsOverview.Theorem4_3GroupBound

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Mačaj–Širáň 2010, §7, Theorem 4 (full proof) [deferred-heavy]

> Let `X` be a group of automorphisms of Γ of order `3^k`. Then `k ≤ 3`.

Proof strategy (paper §7):
1. By Lemma 17, the case `Fix(X) = singleton` is the only non-trivial one.
2. Assume `|X| = 81` for contradiction. By Corollary 2,
   `X = SmallGroup(81, 9)`.
3. Compute orbit structure in GAP: `1 + 3·3 + 6·27 + 38·81 = 3250`.
4. By Lemma 8, `Tr(X) = 26 + 30l`. By Lemma 9, `81 Tr(X) = 18 a₁(x)`
   for any order-9 element `x`, hence `a₁(x) = 117 + 135l`.
5. Common subgroup `Y ≅ Z₉ × Z₃` containing all order-9 elements; orbits
   split into size 27, so `a₁(x) = 27 k` — contradicts `a₁ = 117 + 135l`.
-/

namespace Moore57.Papers.MacajSiran2010.S7

open Moore57

variable {V : Type*} [Fintype V] [DecidableEq V]
  {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- **Step 4-5 arithmetic contradiction.** [done]

In the §7 proof, Lemma 8 plus Lemma 9 give
`81 * (26 + 30 l) = 18 * a₁(x)`, while the common `Z₉ × Z₃` orbit
splitting gives `a₁(x) = 27 k`.  These two numerical constraints are
incompatible. -/
theorem thm4_trace_orbit_arithmetic_contradiction (l a k : ℕ)
    (h_trace : 81 * (26 + 30 * l) = 18 * a)
    (h_orbit : a = 27 * k) :
    False := by
  omega

/-- **Step 4-5 sharper arithmetic contradiction (ℤ form, parity-free).**
[done]

Drops the parity input: Lemma 8's mod-15 congruence alone, combined
with Lemma 9's trace-a₁ link and the orbit-splitting, suffices to
derive a contradiction.  This isolates the *minimal* set of arithmetic
constraints the paper actually uses:

* `h_lem8` : Lemma 8 with `k = 48` orbits: `Tr(X) ≡ 11 (mod 15)`.
* `h_lem9` : Lemma 9 (2) + conjugation symmetry: `81·Tr(X) = 18·a₁(x)`.
* `h_orbit` : Common Z₉ × Z₃ orbit splitting: `a₁(x) = 27·k`.

The proof reduces (via `h_lem9` + `h_orbit`) to `Tr(X) = 6·k`, then
checks via the mod-15 congruence that `6·k ≡ 11 (mod 15)` has no
solution (since `6·k mod 15 ∈ {0, 3, 6, 9, 12}`). -/
theorem thm4_trace_orbit_arithmetic_min_contradiction (Tr a k : ℤ)
    (h_lem8 : (Tr - 11) % 15 = 0)
    (h_lem9 : 81 * Tr = 18 * a)
    (h_orbit : a = 27 * k) :
    False := by
  omega

/-- **Lemma 8 + parity ⇒ `Tr = 26 + 30·l` pin-down.** [done]

Combining Lemma 8 (mod-15 congruence with `k = 48`) and Lemma 6 (2)
parity (`|X| = 81` odd ⇒ `Tr(X)` even) via CRT pins `Tr(X)` to the
form `26 + 30·l` that appears in the §7 Theorem 4 proof. -/
theorem trace_pin_down_via_lem8_and_parity (Tr : ℤ)
    (h_lem8 : (Tr - 11) % 15 = 0) (h_parity : Tr % 2 = 0) :
    (Tr - 26) % 30 = 0 := by
  omega

/-- **Theorem 4 conditional form: contradiction from the three §7
geometric inputs.** [done given hypotheses]

Encodes the conditional content of §7 Steps 4-5 with the paper's
intermediate quantities exposed:

* `X` is an order-81 subgroup of `Sym(V)` acting by graph automorphisms
  on a Moore57 graph `Γ`.
* `x : X` has order `9`.
* **Lemma 8 input** (`h_lem8`): `Tr(X) = 26 + 30 l` for some `l : ℕ` — the
  specific congruence forced by the GAP orbit structure
  `1 + 3·3 + 6·27 + 38·81 = 3250` (48 orbits, deferred-heavy).
* **Lemma 9 input** (`h_lem9`): `81 · Tr(X) = 18 · a₁(x)` — combines
  `|X| · Tr(X) = Σ_y a₁(y)` (Lemma 9 (2), proven) with conjugation
  symmetry plus vanishing on orders ≠ 9 in `SG(81, 9)` (deferred-heavy).
* **Common `Z₉ × Z₃` orbit splitting** (`h_orbit_split`): every
  order-9 element's `a₁` value is divisible by `27`, since the orbits
  of the common subgroup containing all order-9 elements all have
  size 27 (deferred-heavy).

The three hypotheses combine to a pure ℕ arithmetic contradiction. -/
theorem thm4_conditional_arithmetic
    (_hΓ : IsMoore57 Γ)
    (X : Subgroup (Equiv.Perm V)) [Fintype X]
    (_hX_card : Fintype.card X = 81)
    (_hX_aut : ∀ x : X, ∀ a b : V, Γ.Adj a b ↔ Γ.Adj (x • a) (x • b))
    (x : X) (_hx_order : orderOf x = 9)
    (Tr l : ℕ) (h_lem8 : Tr = 26 + 30 * l)
    (h_lem9 : 81 * Tr = 18 * adjacentMovedCount Γ (x : Equiv.Perm V))
    (k : ℕ)
    (h_orbit_split : adjacentMovedCount Γ (x : Equiv.Perm V) = 27 * k) :
    False := by
  subst h_lem8
  exact thm4_trace_orbit_arithmetic_contradiction l _ k h_lem9 h_orbit_split

/-- **Theorem 4 (Section 7 full proof) arithmetic dispatch**. [done]

Given the Section 7 dispatch (Lem 17 case 1: `|X| ∣ 27` from Petersen-fix;
Lem 17 case 2 + Cor 2 sharpening: `|X| ∣ 81` with `|X| ≠ 81` from
SG(81, 9) classification), conclude `|X| ∣ 27`. Directly delegates to
the Section 6 `thm4_card_dvd_27_from_dispatch_and_cor2` arithmetic. -/
theorem thm4_final_dvd_27_from_dispatch_and_cor2
    (n : ℕ) (h_dispatch : n ∣ 27 ∨ n ∣ 81)
    (h_cor2 : n ≠ 81) :
    n ∣ 27 :=
  Moore57.Papers.MacajSiran2010.S6.thm4_card_dvd_27_from_dispatch_and_cor2
    n h_dispatch h_cor2

/-- **Theorem 4 (Section 7) exponent bound**. [done]

For a 3-group `|X| = 3^k`, the dispatch + Cor 2 exclusion forces `k ≤ 3`.
Delegates to Section 6's `thm4_3pow_le_3_from_dispatch`. -/
theorem thm4_final_3pow_le_3_from_dispatch
    (k : ℕ) (h_dispatch : 3 ^ k ∣ 27 ∨ 3 ^ k ∣ 81)
    (h_not_81 : 3 ^ k ≠ 81) :
    k ≤ 3 :=
  Moore57.Papers.MacajSiran2010.S6.thm4_3pow_le_3_from_dispatch
    k h_dispatch h_not_81

/-- **Theorem 4 (Section 7) numeric bound**. [done]

The dispatch + Cor 2 exclusion gives `|X| ≤ 27`. -/
theorem thm4_final_card_le_27_from_dispatch_and_cor2
    (n : ℕ) (h_dispatch : n ∣ 27 ∨ n ∣ 81)
    (h_cor2 : n ≠ 81) :
    n ≤ 27 :=
  Moore57.Papers.MacajSiran2010.S6.thm4_card_le_27_from_dispatch_and_cor2
    n h_dispatch h_cor2

/-- **Theorem 4 (no 3-group of order > 27).** [deferred-heavy]

Arithmetic backbone via `thm4_final_dvd_27_from_dispatch_and_cor2`,
`thm4_final_3pow_le_3_from_dispatch`, and
`thm4_final_card_le_27_from_dispatch_and_cor2`. What remains is the
Cor 2 geometric content (SG(81, 9) classification among 15 order-81
groups, GAP-heavy). -/
theorem thm4_final (_hΓ : IsMoore57 Γ) : True := by trivial

end Moore57.Papers.MacajSiran2010.S7
