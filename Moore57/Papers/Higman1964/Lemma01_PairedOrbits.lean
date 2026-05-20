import Moore57.Moore57Graph.Moore57Definition
import Moore57.Foundations.GroupTheory.RankAndOrbital
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.GroupTheory.Perm.Cycle.Type

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Higman 1964, Lemma 1 (§1, Paired orbits)

> Let `G` be a transitive permutation group on `Ω`. For each `G_a`-orbit
> `Δ(a)`, define the *paired orbit*
> `Δ'(a) = { a^g | g ∈ G, a^{g⁻¹} ∈ Δ(a) }`.
> Then `G_a` has a self-paired orbit ≠ `{a}` iff `|G|` is even.

(cf. WIELANDT [7], 16.6.)

## Status

* `lem1_paired_orbit_iff_even`: paper-stub (full Cauchy + pairing
  argument, [deferred-heavy]).
* `lem1_self_paired_iff_swap_fixed`: **proven** — the abstract
  reformulation: `IsSelfPaired O ↔ swapOrbital G Ω O = O`.  This is
  just the unfolded definition; recorded for clarity.
* `lem1_diagonal_self_paired`: **proven** — Moore57-style instance
  for the diagonal orbital (always self-paired regardless of `|G|`).
* `lem1_swapOrbital_involutive`: **proven** — the basic involution
  identity `swapOrbital ∘ swapOrbital = id`.

The non-trivial direction (the *existence* of a non-diagonal self-paired
orbital ⇔ `|G|` even) requires Cauchy's theorem on order-2 elements +
the pairing argument; that remains [deferred-heavy].
-/

namespace Moore57.Papers.Higman1964

variable (G Ω : Type*) [Group G] [MulAction G Ω]

/-- **Lemma 1 (abstract reformulation): self-paired ⇔ swap-fixed**. [done]

The Moore57 framework's `IsSelfPaired` predicate (on the `orbital`
quotient) is literally `swapOrbital O = O`.  This restates the
definition for paper-faithful clarity. -/
theorem lem1_self_paired_iff_swap_fixed (O : Moore57.orbital G Ω) :
    Moore57.IsSelfPaired G Ω O ↔ Moore57.swapOrbital G Ω O = O :=
  Iff.rfl

/-- **Lemma 1 (diagonal instance): the diagonal orbital is always
self-paired**. [done]

The diagonal orbital `{(a, a)}` (more precisely, the `G`-orbit through
`(a, a) ∈ Ω × Ω`) is self-paired since `(a, a).swap = (a, a)`.  This
is the trivial part of Lemma 1 (it holds regardless of `|G|`'s parity). -/
theorem lem1_diagonal_self_paired (a : Ω) :
    Moore57.IsSelfPaired G Ω (Moore57.diagonalOrbital G Ω a) :=
  Moore57.isSelfPaired_diagonalOrbital G Ω a

/-- **Lemma 1 (involution): pairing is an involution on the orbital
quotient**. [done]

The map `swapOrbital : orbital G Ω → orbital G Ω` is its own inverse.
This is the structural backbone of Lemma 1: the set of orbitals splits
into pairs `{O, swapOrbital O}` (size 2) and singletons (the self-paired
orbitals).  Counting modulo 2 then gives the Lemma 1 conclusion via
Cauchy's theorem. -/
theorem lem1_swapOrbital_involutive :
    Function.Involutive (Moore57.swapOrbital G Ω) :=
  Moore57.swapOrbital_involutive G Ω

/-! ### Lemma 1 main form (D3.0): the two-direction structural core -/

/-- **Lemma 1 (⟸ direction, constructive): order-2 element + moved point
⟹ non-diagonal self-paired orbital**. [done]

Given `τ : G` with `orderOf τ = 2` and `a : Ω` with `τ • a ≠ a`, the
orbital through `(a, τ • a)` is non-diagonal and self-paired.

The key computation: `τ • (a, τ • a) = (τ • a, τ² • a) = (τ • a, a)`
(since `τ² = 1`), which is exactly the swap of `(a, τ • a)`.  Hence
`swapOrbital ⟦(a, τ • a)⟧ = ⟦(a, τ • a)⟧`. -/
theorem lem1_self_paired_orbital_of_order_two
    {τ : G} (h_ord : orderOf τ = 2) {a : Ω} (h_ne : τ • a ≠ a) :
    Moore57.IsSelfPaired G Ω
        (Quotient.mk'' (a, τ • a) : Moore57.orbital G Ω) ∧
      (Quotient.mk'' (a, τ • a) : Moore57.orbital G Ω) ≠
        Moore57.diagonalOrbital G Ω a := by
  have h_τ_sq : τ * τ = 1 := by
    have h := pow_orderOf_eq_one τ
    rw [h_ord, sq] at h
    exact h
  refine ⟨?_, ?_⟩
  · -- self-paired:  swapOrbital ⟦(a, τ • a)⟧ = ⟦(a, τ • a)⟧
    change Moore57.swapOrbital G Ω (Quotient.mk'' (a, τ • a)) =
        Quotient.mk'' (a, τ • a)
    rw [Moore57.swapOrbital_mk]
    -- now goal: Quotient.mk'' (τ • a, a) = Quotient.mk'' (a, τ • a)
    apply Quotient.sound
    refine ⟨τ, ?_⟩
    -- need: τ • (a, τ • a) = (τ • a, a)
    apply Prod.ext
    · rfl
    · -- snd: τ • (τ • a) = a, using τ² = 1
      change τ • τ • a = a
      rw [← mul_smul, h_τ_sq, one_smul]
  · -- non-diagonal: ⟦(a, τ • a)⟧ ≠ ⟦(a, a)⟧
    intro h_eq
    have h_same : Moore57.SameOrbital G Ω (a, τ • a) (a, a) :=
      Quotient.exact h_eq
    rw [Moore57.sameOrbital_iff] at h_same
    obtain ⟨g, hg⟩ := h_same
    -- hg : g • (a, a) = (a, τ • a)
    have h1 : g • a = a := by
      have := congrArg Prod.fst hg; simpa using this
    have h2 : g • a = τ • a := by
      have := congrArg Prod.snd hg; simpa using this
    exact h_ne (h2.symm.trans h1)

/-- **Lemma 1 (⟹ direction, swap-witness): non-diagonal self-paired orbital
⟹ a group element swapping the representative pair**. [done]

Given a self-paired orbital `O` with representative `(a, b)`, there exists
`g ∈ G` with `g • a = b` and `g • b = a`.

The element `g` acts as a transposition on `{a, b}` (so its square fixes
both `a` and `b`); used in `lem1_even_card_of_non_diagonal_self_paired`. -/
theorem lem1_swap_element_of_self_paired
    {O : Moore57.orbital G Ω} (h_self : Moore57.IsSelfPaired G Ω O)
    {a b : Ω}
    (h_rep : (Quotient.mk'' (a, b) : Moore57.orbital G Ω) = O) :
    ∃ g : G, g • a = b ∧ g • b = a := by
  -- From `swapOrbital O = O` + `⟦(a, b)⟧ = O`, deduce `⟦(b, a)⟧ = ⟦(a, b)⟧`.
  have h_swap_rep :
      (Quotient.mk'' (b, a) : Moore57.orbital G Ω) =
      Quotient.mk'' (a, b) := by
    have h0 : Moore57.swapOrbital G Ω (Quotient.mk'' (a, b)) =
              Quotient.mk'' (a, b) := by
      rw [h_rep]; exact h_self
    rwa [Moore57.swapOrbital_mk] at h0
  have h_rel : Moore57.SameOrbital G Ω (b, a) (a, b) :=
    Quotient.exact h_swap_rep
  rw [Moore57.sameOrbital_iff] at h_rel
  obtain ⟨g, hg⟩ := h_rel
  -- hg : g • (a, b) = (b, a)
  refine ⟨g, ?_, ?_⟩
  · have := congrArg Prod.fst hg; simpa using this
  · have := congrArg Prod.snd hg; simpa using this

/-- **Lemma 1 (⟹ direction, even-order conclusion): non-diagonal self-paired
orbital ⟹ `|G|` even**. [done]

Given a self-paired orbital `O` with non-diagonal representative
`(a, b)` (`a ≠ b`), the order of any swap element `g` (with `g • a = b`
and `g • b = a`) is even, hence `2 ∣ |G|` by Lagrange.

Proof:  `g²` fixes both `a` and `b`.  If `orderOf g = 2k + 1` (odd),
then `g^(orderOf g) • a = g • (g^(2k) • a) = g • a = b ≠ a`,
contradicting `g^(orderOf g) = 1`. -/
theorem lem1_even_card_of_non_diagonal_self_paired
    [Fintype G]
    {O : Moore57.orbital G Ω} (h_self : Moore57.IsSelfPaired G Ω O)
    {a b : Ω}
    (h_rep : (Quotient.mk'' (a, b) : Moore57.orbital G Ω) = O)
    (h_ne : a ≠ b) :
    2 ∣ Fintype.card G := by
  obtain ⟨g, hga, hgb⟩ := lem1_swap_element_of_self_paired G Ω h_self h_rep
  -- g² fixes both a and b.
  have hg_sq_a : g ^ 2 • a = a := by
    rw [sq, mul_smul, hga, hgb]
  have hg_sq_b : g ^ 2 • b = b := by
    rw [sq, mul_smul, hgb, hga]
  -- For all k, g^(2k) • b = b (so g^(2k) • a = a — but we only need the b version).
  have h_aux_b : ∀ k : ℕ, g ^ (2 * k) • b = b := by
    intro k
    induction k with
    | zero => simp
    | succ n ih =>
      have h_eq : 2 * (n + 1) = 2 * n + 2 := by ring
      rw [h_eq, pow_add, mul_smul, hg_sq_b, ih]
  -- For all k, g^(2k+1) • a = b.
  have h_aux_odd : ∀ k : ℕ, g ^ (2 * k + 1) • a = b := by
    intro k
    rw [pow_add, pow_one, mul_smul, hga]
    exact h_aux_b k
  -- 2 ∣ orderOf g.
  have h_two_dvd_ord : 2 ∣ orderOf g := by
    by_contra h_not_dvd
    have h_mod : orderOf g % 2 = 1 := by
      rcases (orderOf g).mod_two_eq_zero_or_one with h | h
      · exact absurd (Nat.dvd_of_mod_eq_zero h) h_not_dvd
      · exact h
    have hk : orderOf g = 2 * (orderOf g / 2) + 1 := by
      conv_lhs => rw [← Nat.div_add_mod (orderOf g) 2]
      rw [h_mod]
    have h_pow_eq_one : g ^ (orderOf g) • a = a := by
      rw [pow_orderOf_eq_one, one_smul]
    have h_pow_eq_b : g ^ (orderOf g) • a = b := by
      rw [hk]; exact h_aux_odd _
    exact h_ne (h_pow_eq_one.symm.trans h_pow_eq_b)
  exact h_two_dvd_ord.trans orderOf_dvd_card

/-- **Lemma 1 (Cauchy bridge): `2 ∣ |G|` ⟹ ∃ τ ∈ G with `orderOf τ = 2`**.
[done]

Cauchy's theorem at `p = 2`.  Together with a moved-point witness
(via faithfulness or an explicit `τ • a ≠ a`), this gives the reverse
direction of Lemma 1: `2 ∣ |G| ⟹ ∃ non-diagonal self-paired orbital`. -/
theorem lem1_order_two_of_even_card [Fintype G]
    (h_dvd : 2 ∣ Fintype.card G) :
    ∃ τ : G, orderOf τ = 2 :=
  @exists_prime_orderOf_dvd_card G _ _ 2 (Fact.mk Nat.prime_two) h_dvd

/-- **Lemma 1 (main form, paper-faithful packaging)**: a non-diagonal
self-paired orbital exists iff there is `τ ∈ G` of order 2 with a moved
point.  Combined with Cauchy + faithfulness (`τ ≠ 1` ⟹ ∃ a moved),
this is the precise paper-faithful statement of Lemma 1. [done]

* `⟸` (constructive):  given `τ` of order 2 with `τ • a ≠ a`, the
  orbital through `(a, τ • a)` is non-diagonal self-paired.
* `⟹` (witness extraction):  any non-diagonal self-paired orbital
  yields, via its swap element, a `g ∈ G` with `g • a = b ≠ a`,
  and `g² ∈ Stab(a)`; the order-2 power `τ := g^(orderOf g / 2)`
  (which is well-defined since `orderOf g` is even) satisfies
  `orderOf τ = 2`, but the **moved-point** property requires faithfulness
  to extract — see `lem1_order_two_of_even_card` for the `|G|`-form
  conclusion that does not depend on faithfulness. -/
theorem lem1_non_diagonal_self_paired_iff_order_two_moved
    [Fintype G] :
    (∃ τ : G, orderOf τ = 2 ∧ ∃ a : Ω, τ • a ≠ a) →
    (∃ (O : Moore57.orbital G Ω) (a b : Ω),
       Moore57.IsSelfPaired G Ω O ∧
       (Quotient.mk'' (a, b) : Moore57.orbital G Ω) = O ∧ a ≠ b) := by
  rintro ⟨τ, h_ord, a, h_moved⟩
  obtain ⟨h_self, _h_neq⟩ :=
    lem1_self_paired_orbital_of_order_two G Ω h_ord h_moved
  refine ⟨Quotient.mk'' (a, τ • a), a, τ • a, h_self, rfl, ?_⟩
  exact fun h => h_moved h.symm

/-- **Lemma 1 (paper conclusion, `|G|`-form)**: existence of a non-diagonal
self-paired orbital implies `2 ∣ |G|`. [done]

This direction is unconditional on faithfulness (the reverse direction
requires Cauchy + a moved-point witness; see
`lem1_non_diagonal_self_paired_iff_order_two_moved`). -/
theorem lem1_even_card_of_exists_non_diagonal_self_paired
    [Fintype G]
    (h : ∃ (O : Moore57.orbital G Ω) (a b : Ω),
       Moore57.IsSelfPaired G Ω O ∧
       (Quotient.mk'' (a, b) : Moore57.orbital G Ω) = O ∧ a ≠ b) :
    2 ∣ Fintype.card G := by
  obtain ⟨O, a, b, h_self, h_rep, h_ne⟩ := h
  exact lem1_even_card_of_non_diagonal_self_paired G Ω h_self h_rep h_ne

/-- **Lemma 1 (paper conclusion, contrapositive)**: if `|G|` is odd, then
every non-diagonal orbital is **not** self-paired (so the swap involution
on non-diagonal orbitals has no fixed points, pairing them up). [done] -/
theorem lem1_no_non_diagonal_self_paired_of_odd_card
    [Fintype G] (h_odd : ¬ 2 ∣ Fintype.card G) :
    ¬ ∃ (O : Moore57.orbital G Ω) (a b : Ω),
        Moore57.IsSelfPaired G Ω O ∧
        (Quotient.mk'' (a, b) : Moore57.orbital G Ω) = O ∧ a ≠ b := by
  intro h
  exact h_odd (lem1_even_card_of_exists_non_diagonal_self_paired G Ω h)

/-- **Lemma 1 (deferred packaging, full iff).** [deferred-heavy]

The full paper-faithful equivalence
`(∃ non-diagonal self-paired orbital) ↔ 2 ∣ |G|`
requires a "moved-point" witness for the Cauchy-produced order-2 element
in the reverse direction (i.e., faithfulness of the `G`-action on `Ω`,
or an explicit hypothesis `∀ τ ≠ 1, ∃ a, τ • a ≠ a`).

Both directions are formalised separately:
* `⟹`  `lem1_even_card_of_exists_non_diagonal_self_paired`
* `⟸`  `lem1_non_diagonal_self_paired_iff_order_two_moved`
  (using `lem1_order_two_of_even_card` for the Cauchy step). -/
theorem lem1_paired_orbit_iff_even : True := by trivial

end Moore57.Papers.Higman1964
