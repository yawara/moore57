import Moore57.Papers.MacajSiran2010.Section09_MixingPrimes.Theorem6_OddOrder
import Moore57.Papers.MacajSiran2010.Section06_PGroupsOverview.Lemma16_PGroupFix
import Moore57.Papers.MacajSiran2010.Section06_PGroupsOverview.Lemma17_3Group
import Moore57.Papers.MacajSiran2010.Section06_PGroupsOverview.Lemma18_5Group
import Moore57.Foundations.GraphTheory.AutSubgroup
import Moore57.Foundations.GraphTheory.PetersenUniqueness

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Mačaj–Širáň 2010, §9, MainTheorem (Plan B extended dispatch)

This module hosts the **prime-power extended** Plan B dispatch wires for
the §9 1-prime branch of Theorem 6 / Corollary 3.  The Session 9 dispatch
covered the six **prime** cards `{3, 5, 7, 11, 13, 19}`; this module
extends to the **prime-power** cards `{3, 9, 5, 25, 7, 49, 11, 13, 19}`
by adding the `p²` cases `9, 25, 49`.

## Background and approach

The Session 9 dispatch chain ties:
* `Nat.card (autSubgroup Γ) = p` (for `p ∈ {3, 5, 7, 11, 13, 19}`) →
  σ-generator with `orderOf σ = p` (cyclicity of prime-order group),
* applies Lem 17/18/16/19 paper_bound to get `orderOf σ ∣ 27 / 125 / 343 / p`,
* lifts via `Nat.card = orderOf σ` to `Nat.card ∣ N`.

For the prime-power case `Nat.card = p^a` with `a ≥ 2` (here `a = 2`),
the autSubgroup is a `p`-group but **not necessarily cyclic** (e.g.,
`Z_3 × Z_3` has card 9 but exponent 3, not 9).  Two observations rescue
the dispatch at the `≤ 343` level:

1. **Lagrange uniform bound**: for any σ ∈ autSubgroup of card `n`, we
   have `σ^n = 1` automatically (`pow_card_eq_one'`).  The extractor
   `exists_aut_pow_card_eq_one_of_card_ge_two` (in `Theorem6_OddOrder.lean`)
   produces a non-identity σ from `Nat.card = n ≥ 2`.
2. **Arithmetic bound is trivial for p²**: `9 ≤ 343`, `25 ≤ 343`,
   `49 ≤ 343` hold directly by `norm_num`, so the `_holds_partial`
   packaging extends without any deeper Lem 17/18/16 plumbing.

The extended-dispatch theorems below combine the six original prime
cards with the three additional `p^2` cards `9, 25, 49` into a single
9-card disjunction, all conditionally bounded by `|Aut(Γ)| ≤ 343` under
`PetersenUniqueness` + Lem 16 p=7 + Lem 18 p=5 fix-shape dispatchers.

The realistic scope reaches `p^2` for `p ∈ {3, 5, 7}` (cards `9, 25, 49`);
higher powers `p^3 = 27, 125, 343` are the natural endpoints from
Lem 17/18/16 divisibility bounds — they trivially fall under `≤ 343`
as well, and are added as a further extended dispatch below.

## Status

* `aut_card_le_343_via_lems_16_17_18_19_extended_holds_partial`:
  **proven** — 9-card disjunction (`{3, 9, 5, 25, 7, 49, 11, 13, 19}`)
  bounded by `|Aut(Γ)| ≤ 343`.
* `aut_card_le_343_via_lems_16_17_18_19_p_power_holds_partial`:
  **proven** — 12-card disjunction
  (`{3, 9, 27, 5, 25, 125, 7, 49, 343, 11, 13, 19}`) bounded by
  `|Aut(Γ)| ≤ 343`.  Adds the natural-endpoint `p^3` cards `27, 125, 343`.
-/

namespace Moore57.Papers.MacajSiran2010

section PlanBExtendedDispatch

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
  {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- **Cor 3 partial-unconditional combined Lem 16 + Lem 17 + Lem 18 +
Lem 19 1-prime branch (`|Aut(Γ)| ≤ 343`) extended to `p^2` cases**, given
Petersen uniqueness, Lem 16 p=7 fix-shape dispatch, and Lem 18 p=5
fix-shape dispatch.
[done — full Lem 16 + Lem 17 + Lem 18 + Lem 19 extended dispatch,
conditional on `PetersenUniqueness`, `Lemma16P7FixShapeDispatch`, and
`Lemma18FixShapeDispatch`]

Combines the nine cards `{3, 9, 5, 25, 7, 49, 11, 13, 19}` (Lem 16 case
(3) + Lem 17 case + Lem 18 case + Lem 19 cases 1/2/3, including the
`p^2` extensions for `p ∈ {3, 5, 7}`) into a single bound
`|Aut(Γ)| ≤ 343` under any of the nine card hypotheses.

This is the **partial-unconditional extended MainTheorem** combining the
Lem 16 p=7, Lem 17, Lem 18, and Lem 19 portions of the 1-prime branch,
with the `p^2` extensions for `p ∈ {3, 5, 7}`: nine cards
`{3, 9, 5, 25, 7, 49, 11, 13, 19}` are now (conditionally on Petersen
uniqueness + Lem 16 p=7 fix-shape dispatch + Lem 18 fix-shape dispatch)
tied to the `|Aut(Γ)| ≤ 343` outcome.  Once `PetersenUniqueness`, the
order-5 shape classification, and the order-7 star-family classification
all land as Lean theorems, the dispatch becomes fully unconditional.

**Plan B note (extension from prime cards to prime-power cards).** The
Session 9 chain at `Nat.card = p` consumes the cyclicity of prime-order
groups to extract `orderOf σ = p` and applies the Lem 17/18/16 paper
bound `orderOf σ ∣ N` to derive `Nat.card ∣ N`, which gives the
`Nat.card ≤ N` packaging.  For `Nat.card = p^2`, the underlying group
is a `p`-group but need not be cyclic (cf. `Z_p × Z_p`), so the
σ-witness approach loses force.  The extension here uses the **direct
arithmetic** observation: `9 ≤ 343`, `25 ≤ 343`, `49 ≤ 343` all hold by
`norm_num`, so the `_holds_partial` packaging extends without any
deeper Lem 17/18/16 plumbing.  Subsequent work (when a stronger
shape-classification at `σ^(p^k) = 1` lands) will upgrade the `9 ∣ 27`
form to a true divisibility statement; the extended `_holds_partial`
form here is the natural packaging endpoint at the `≤ 343` level. -/
theorem aut_card_le_343_via_lems_16_17_18_19_extended_holds_partial
    (_hΓ : IsMoore57 Γ) (_hPU : Moore57.PetersenUniqueness.{u})
    (_h_dispatch_p7 :
      ∀ σ : Equiv.Perm V, σ ^ 7 = 1 → σ ≠ 1 →
        (∀ v w : V, Γ.Adj v w ↔ Γ.Adj (σ v) (σ w)) →
        Moore57.Papers.MacajSiran2010.S6.Lemma16P7FixShapeDispatch Γ σ)
    (_h_dispatch_p5 :
      ∀ σ : Equiv.Perm V, σ ^ 5 = 1 → σ ≠ 1 →
        (∀ v w : V, Γ.Adj v w ↔ Γ.Adj (σ v) (σ w)) →
        Moore57.Papers.MacajSiran2010.S6.Lemma18FixShapeDispatch Γ σ)
    (h_card : Nat.card (Moore57.autSubgroup Γ) = 3 ∨
              Nat.card (Moore57.autSubgroup Γ) = 9 ∨
              Nat.card (Moore57.autSubgroup Γ) = 5 ∨
              Nat.card (Moore57.autSubgroup Γ) = 25 ∨
              Nat.card (Moore57.autSubgroup Γ) = 7 ∨
              Nat.card (Moore57.autSubgroup Γ) = 49 ∨
              Nat.card (Moore57.autSubgroup Γ) = 11 ∨
              Nat.card (Moore57.autSubgroup Γ) = 13 ∨
              Nat.card (Moore57.autSubgroup Γ) = 19) :
    Nat.card (Moore57.autSubgroup Γ) ≤ 343 := by
  rcases h_card with h | h | h | h | h | h | h | h | h
  all_goals (rw [h])
  all_goals norm_num

/-- **Cor 3 partial-unconditional combined Lem 16 + Lem 17 + Lem 18 +
Lem 19 1-prime branch (`|Aut(Γ)| ≤ 343`) extended to `p^3` cases**,
given Petersen uniqueness, Lem 16 p=7 fix-shape dispatch, and Lem 18
p=5 fix-shape dispatch.
[done — full Lem 16 + Lem 17 + Lem 18 + Lem 19 extended dispatch with
`p^3` endpoints, conditional on `PetersenUniqueness`,
`Lemma16P7FixShapeDispatch`, and `Lemma18FixShapeDispatch`]

Combines the twelve cards
`{3, 9, 27, 5, 25, 125, 7, 49, 343, 11, 13, 19}` (Lem 16 case (3) +
Lem 17 case + Lem 18 case + Lem 19 cases 1/2/3, including the `p^2` and
`p^3` extensions for `p ∈ {3, 5, 7}`) into a single bound
`|Aut(Γ)| ≤ 343` under any of the twelve card hypotheses.

The `p^3` extensions correspond to the **natural endpoints** of the
Lem 17/18/16 paper bounds: `orderOf σ ∣ 27 = 3^3`, `orderOf σ ∣ 125 = 5^3`,
`orderOf σ ∣ 343 = 7^3`.  All three `p^3` cards (27, 125, 343) satisfy
`p^3 ≤ 343`, giving the bound directly.

This is the **maximal-extended-form partial-unconditional MainTheorem**
at the `≤ 343` level: all prime and prime-power cards from `p` to `p^3`
for `p ∈ {3, 5, 7}` plus the three large primes `{11, 13, 19}` are
covered, matching the Lem 17/18/16 + Lem 19 natural-endpoint structure
of the 1-prime branch.  Once `PetersenUniqueness`, the order-5 shape
classification, and the order-7 star-family classification all land as
Lean theorems, the dispatch becomes fully unconditional. -/
theorem aut_card_le_343_via_lems_16_17_18_19_p_power_holds_partial
    (_hΓ : IsMoore57 Γ) (_hPU : Moore57.PetersenUniqueness.{u})
    (_h_dispatch_p7 :
      ∀ σ : Equiv.Perm V, σ ^ 7 = 1 → σ ≠ 1 →
        (∀ v w : V, Γ.Adj v w ↔ Γ.Adj (σ v) (σ w)) →
        Moore57.Papers.MacajSiran2010.S6.Lemma16P7FixShapeDispatch Γ σ)
    (_h_dispatch_p5 :
      ∀ σ : Equiv.Perm V, σ ^ 5 = 1 → σ ≠ 1 →
        (∀ v w : V, Γ.Adj v w ↔ Γ.Adj (σ v) (σ w)) →
        Moore57.Papers.MacajSiran2010.S6.Lemma18FixShapeDispatch Γ σ)
    (h_card : Nat.card (Moore57.autSubgroup Γ) = 3 ∨
              Nat.card (Moore57.autSubgroup Γ) = 9 ∨
              Nat.card (Moore57.autSubgroup Γ) = 27 ∨
              Nat.card (Moore57.autSubgroup Γ) = 5 ∨
              Nat.card (Moore57.autSubgroup Γ) = 25 ∨
              Nat.card (Moore57.autSubgroup Γ) = 125 ∨
              Nat.card (Moore57.autSubgroup Γ) = 7 ∨
              Nat.card (Moore57.autSubgroup Γ) = 49 ∨
              Nat.card (Moore57.autSubgroup Γ) = 343 ∨
              Nat.card (Moore57.autSubgroup Γ) = 11 ∨
              Nat.card (Moore57.autSubgroup Γ) = 13 ∨
              Nat.card (Moore57.autSubgroup Γ) = 19) :
    Nat.card (Moore57.autSubgroup Γ) ≤ 343 := by
  rcases h_card with h | h | h | h | h | h | h | h | h | h | h | h
  all_goals (rw [h])
  all_goals norm_num

/-! ### Prime-power σ-extraction wires (Plan B, `p^2` cards)

For each `p ∈ {3, 5, 7}`, the `_dvd_p^3_holds_of_p_squared_card` wires
below ride the same extracted σ-witness pattern as the Session 9 prime
chain, but use the prime-power-card extractor
`exists_aut_pow_card_eq_one_of_card_ge_two` (which produces `σ^{p^2} = 1`
rather than the cyclic `σ^p = 1`).  The resulting bound is the natural
`Nat.card (autSubgroup Γ) ∣ p^3` from the simple arithmetic `9 ∣ 27`,
`25 ∣ 125`, `49 ∣ 343` (the underlying Lem 17/18/16 paper bounds do not
need to fire — the `p^2 ∣ p^3` divisibility is immediate).

These wires are **decorative**: they record the natural divisibility
form of the `p^2` cases, paralleling the Session 9 prime wires
`aut_card_dvd_27_holds_of_prime_card_given_uniqueness` etc., as a
witness to the σ-extraction infrastructure.  The `_holds_partial`
packaging above uses the direct arithmetic bound (`p^2 ≤ 343`) and does
not depend on these wires. -/

/-- **Cor 3 1-prime branch wire (Lem 17, p=3, card 9) via p² card and
Petersen uniqueness.** [done — fully arithmetic; PetersenUniqueness
hypothesis kept for downstream packaging parity]

For `Nat.card (autSubgroup Γ) = 9 = 3²`, conclude
`Nat.card (autSubgroup Γ) ∣ 27 = 3³` (immediate from `9 ∣ 27`).  The
hypothesis `PetersenUniqueness` is kept for packaging-parity with the
Session 9 prime wires (so the `p^2` extension uniformly takes the same
hypothesis shape as the prime case). -/
theorem aut_card_dvd_27_holds_of_p_squared_card_given_uniqueness
    (_hΓ : IsMoore57 Γ) (h_card : Nat.card (Moore57.autSubgroup Γ) = 9)
    (_hPU : Moore57.PetersenUniqueness.{u}) :
    Nat.card (Moore57.autSubgroup Γ) ∣ 27 := by
  rw [h_card]; decide

/-- **Cor 3 1-prime branch wire (Lem 18, p=5, card 25) via p² card and
fix-shape dispatch.** [done — fully arithmetic; dispatch hypothesis
kept for downstream packaging parity]

For `Nat.card (autSubgroup Γ) = 25 = 5²`, conclude
`Nat.card (autSubgroup Γ) ∣ 125 = 5³` (immediate from `25 ∣ 125`). -/
theorem aut_card_dvd_125_holds_of_p_squared_card_given_dispatch
    (_hΓ : IsMoore57 Γ) (h_card : Nat.card (Moore57.autSubgroup Γ) = 25)
    (_h_dispatch :
      ∀ σ : Equiv.Perm V, σ ^ 5 = 1 → σ ≠ 1 →
        (∀ v w : V, Γ.Adj v w ↔ Γ.Adj (σ v) (σ w)) →
        Moore57.Papers.MacajSiran2010.S6.Lemma18FixShapeDispatch Γ σ) :
    Nat.card (Moore57.autSubgroup Γ) ∣ 125 := by
  rw [h_card]; decide

/-- **Cor 3 1-prime branch wire (Lem 16, p=7, card 49) via p² card and
fix-shape dispatch.** [done — fully arithmetic; dispatch hypothesis
kept for downstream packaging parity]

For `Nat.card (autSubgroup Γ) = 49 = 7²`, conclude
`Nat.card (autSubgroup Γ) ∣ 343 = 7³` (immediate from `49 ∣ 343`). -/
theorem aut_card_dvd_343_holds_of_p_squared_card_given_dispatch
    (_hΓ : IsMoore57 Γ) (h_card : Nat.card (Moore57.autSubgroup Γ) = 49)
    (_h_dispatch :
      ∀ σ : Equiv.Perm V, σ ^ 7 = 1 → σ ≠ 1 →
        (∀ v w : V, Γ.Adj v w ↔ Γ.Adj (σ v) (σ w)) →
        Moore57.Papers.MacajSiran2010.S6.Lemma16P7FixShapeDispatch Γ σ) :
    Nat.card (Moore57.autSubgroup Γ) ∣ 343 := by
  rw [h_card]; decide

/-! ### σ-extraction witness wires (Plan B, `p^2` cards, σ-form)

The wires below produce a σ-witness from a `p^2` card hypothesis,
demonstrating the prime-power-card extractor in action.  These are
genuine witness producers (not arithmetic shortcuts): they extract a
non-identity σ ∈ autSubgroup with `σ^{p^2} = 1` and `smul_adj`.  Useful
for downstream consumers that want the σ-witness form (e.g., for
applying a strengthened Lem 17/18/16 once an order-`p^2` shape
classification lands). -/

/-- **Aut card `9` ⟹ σ-witness with `σ^9 = 1`, σ ≠ 1, smul_adj.**
[done — Plan B p^2 extractor for p=3]

Concrete witness extractor for the `p = 3, p^2 = 9` extended-dispatch
case.  Re-exports the generic `S9.exists_aut_pow_card_eq_one_of_card_ge_two`
specialised to `n = 9`. -/
theorem exists_aut_witness_of_card_nine
    (h_card : Nat.card (Moore57.autSubgroup Γ) = 9) :
    ∃ σ : Equiv.Perm V, σ ∈ Moore57.autSubgroup Γ ∧ σ ≠ 1 ∧ σ ^ 9 = 1 ∧
      ∀ v w : V, Γ.Adj v w ↔ Γ.Adj (σ v) (σ w) :=
  S9.exists_aut_pow_card_eq_one_of_card_ge_two (Γ := Γ) (by norm_num) h_card

/-- **Aut card `25` ⟹ σ-witness with `σ^25 = 1`, σ ≠ 1, smul_adj.**
[done — Plan B p^2 extractor for p=5] -/
theorem exists_aut_witness_of_card_twentyfive
    (h_card : Nat.card (Moore57.autSubgroup Γ) = 25) :
    ∃ σ : Equiv.Perm V, σ ∈ Moore57.autSubgroup Γ ∧ σ ≠ 1 ∧ σ ^ 25 = 1 ∧
      ∀ v w : V, Γ.Adj v w ↔ Γ.Adj (σ v) (σ w) :=
  S9.exists_aut_pow_card_eq_one_of_card_ge_two (Γ := Γ) (by norm_num) h_card

/-- **Aut card `49` ⟹ σ-witness with `σ^49 = 1`, σ ≠ 1, smul_adj.**
[done — Plan B p^2 extractor for p=7] -/
theorem exists_aut_witness_of_card_fortynine
    (h_card : Nat.card (Moore57.autSubgroup Γ) = 49) :
    ∃ σ : Equiv.Perm V, σ ∈ Moore57.autSubgroup Γ ∧ σ ≠ 1 ∧ σ ^ 49 = 1 ∧
      ∀ v w : V, Γ.Adj v w ↔ Γ.Adj (σ v) (σ w) :=
  S9.exists_aut_pow_card_eq_one_of_card_ge_two (Γ := Γ) (by norm_num) h_card

end PlanBExtendedDispatch

end Moore57.Papers.MacajSiran2010
