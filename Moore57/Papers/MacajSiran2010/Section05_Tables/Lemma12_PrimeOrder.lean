import Moore57.Papers.MacajSiran2010.Section04_Characters.Proposition2_CharacterSystem
import Moore57.Papers.MacajSiran2010.Section02_StateOfTheArt.Lemma2_Involution
import Moore57.Papers.MacajSiran2010.Section02_StateOfTheArt.Lemma3_Chi1Formula
import Moore57.Foundations.GraphTheory.AdjacentMovedCount
import Moore57.Moore57Graph.Aut.FixedCount
import Moore57.Moore57Graph.Aut.OrderElevenIsC5
import Moore57.Moore57Graph.Aut.FixedSubgraphData
import Moore57.Moore57Graph.Aut.HSFixedData
import Moore57.Moore57Graph.Aut.PetersenFixedData
import Moore57.Moore57Graph.Aut.SingletonAndEmptyFixedData
import Moore57.Moore57Graph.Aut.TraceIntegrality

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Mačaj–Širáň 2010, §5, Lemma 12

> Let `x` be an automorphism of a Moore (57, 2)-graph Γ of prime order `p`.
> Then the values `a₁(x)` and `χ₁(x)` satisfy a 17-row table parameterised
> by `(a₀(x), p)`.

Key rows used downstream (with the existing Lean infrastructure that proves
them):
- `p = 2, a₀ = 56`: `a₁ = 112` — see [Section02.Lemma2_Involution].
- `p = 19, a₀ = 1`: from `Moore57.Moore57Graph.Aut.FixedCount`
  (`order19_aut_fixedVertexCount_eq_one`).
- `p = 11, a₀ = 5`: from `Moore57.Moore57Graph.Aut.OrderElevenIsC5`
  (`aut_order_eleven_fixedVertexCount_eq_five`).
- Starred case `p = 3, a₀ = 1`: contradiction.  Half proven directly:
  any order-3 graph automorphism has `a₁ = 0` (no-triangle argument,
  `lem12_p3_a1_eq_zero`).  Combined with the character-theoretic
  constraint `a₁ ∈ {27 + 45k : k ∈ ℕ}` (deferred), this excludes
  `a₀ = 1`.
- Starred case `p = 7, a₀ = 58`: contradiction.  Remains skeleton
  (orbit-counting argument from the paper).
-/

open Moore57

namespace Moore57.Papers.MacajSiran2010.S5

variable {V : Type*} [Fintype V] [DecidableEq V]
  {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- **Lemma 12 (p=2 row): `a₀(x) = 56` for an involution `σ ≠ 1`.** [done]
Re-exports `Section02.Lemma2.lem2_involution_a0`. -/
theorem lem12_p2_a0_56 (hΓ : IsMoore57 Γ) (σ : Equiv.Perm V)
    (hAut : ∀ v w, Γ.Adj v w ↔ Γ.Adj (σ v) (σ w))
    (hpow : σ ^ 2 = 1) (hne : σ ≠ 1) :
    fixedVertexCount σ = 56 :=
  Moore57.Papers.MacajSiran2010.S2.lem2_involution_a0 hΓ σ hpow hne hAut

/-- **Lemma 12 (p=2 row, a₁): `a₁(x) = 112` for an involution `σ ≠ 1`.** [done]
Re-exports `Section02.Lemma2.lem2_involution_a1`. -/
theorem lem12_p2_a1_112 (hΓ : IsMoore57 Γ) (σ : Equiv.Perm V)
    (hAut : ∀ v w, Γ.Adj v w ↔ Γ.Adj (σ v) (σ w))
    (hpow : σ ^ 2 = 1) (hne : σ ≠ 1) :
    adjacentMovedCount Γ σ = 112 :=
  Moore57.Papers.MacajSiran2010.S2.lem2_involution_a1 hΓ σ hpow hne hAut

/-- **Lemma 12 (p=19 row): `a₀(x) = 1` for an order-19 automorphism.** -/
theorem lem12_p19_a0_one (hΓ : IsMoore57 Γ) (σ : Equiv.Perm V)
    (hAut : ∀ v w, Γ.Adj v w ↔ Γ.Adj (σ v) (σ w))
    (hpow : σ ^ 19 = 1) (hne : σ ≠ 1) :
    fixedVertexCount σ = 1 :=
  order19_aut_fixedVertexCount_eq_one hΓ σ hAut hpow hne

/-- **Lemma 12 (p=11 row): `a₀(x) = 5` for an order-11 automorphism.** -/
theorem lem12_p11_a0_five (hΓ : IsMoore57 Γ) (σ : Equiv.Perm V)
    (hAut : ∀ v w, Γ.Adj v w ↔ Γ.Adj (σ v) (σ w))
    (hpow : σ ^ 11 = 1) (hne : σ ≠ 1) :
    fixedVertexCount σ = 5 :=
  aut_order_eleven_fixedVertexCount_eq_five hΓ σ hAut hpow hne

/-- **Lemma 12 (p=3 row, `a₁` part): any order-3 graph automorphism has
`a₁ = 0` on Moore57.** [done]

Paper argument (§5, p=3 starred row): if `a₁(σ) > 0`, then some vertex
`v` satisfies `v ~ σ v`.  Applying the graph-automorphism hypothesis
twice yields `σ v ~ σ² v` and `σ² v ~ σ³ v = v` (using `σ ^ 3 = 1`),
so `v`, `σ v`, `σ² v` form a triangle — impossible in Moore57
(parameter `λ = 0`).

This is half of the starred-case no-go (`lem12_no_p3_a0_one`); the
other half is the character-theoretic constraint `a₁ = 27 + 45k > 0`
when `a₀ = 1`, which depends on Proposition 2 and remains deferred. -/
theorem lem12_p3_a1_eq_zero (hΓ : IsMoore57 Γ) (σ : Equiv.Perm V)
    (hAut : ∀ a b : V, Γ.Adj a b ↔ Γ.Adj (σ a) (σ b))
    (hpow : σ ^ 3 = 1) :
    adjacentMovedCount Γ σ = 0 := by
  classical
  by_contra hne_zero
  have hpos : 0 < adjacentMovedCount Γ σ := Nat.pos_of_ne_zero hne_zero
  unfold adjacentMovedCount at hpos
  obtain ⟨v, hv_mem⟩ := Finset.card_pos.mp hpos
  rw [Finset.mem_filter] at hv_mem
  have hv : Γ.Adj v (σ v) := hv_mem.2
  -- σ v ~ σ² v.
  have h_σv_σ2v : Γ.Adj (σ v) (σ (σ v)) := (hAut v (σ v)).mp hv
  -- σ³ v = v (from σ ^ 3 = 1).
  have h_σ3v : σ (σ (σ v)) = v := by
    have h_apply : (σ ^ 3 : Equiv.Perm V) v = v := by
      rw [hpow]; rfl
    have h_expand : (σ ^ 3 : Equiv.Perm V) v = σ (σ (σ v)) := by
      simp [pow_succ, Equiv.Perm.mul_apply]
    rw [h_expand] at h_apply
    exact h_apply
  -- σ² v ~ σ³ v = v.
  have h_σ2v_v : Γ.Adj (σ (σ v)) v := by
    have h := (hAut (σ v) (σ (σ v))).mp h_σv_σ2v
    rwa [h_σ3v] at h
  -- Triangle v – σv – σ²v – v contradicts Moore57's no-triangle.
  exact hΓ.no_triangle hv h_σv_σ2v h_σ2v_v

/-- **Lemma 12 (prime-order `(a₀, a₁, χ₁)` table — full statement).** [deferred-heavy]
The full 17-row classification of admissible `(p, a₀, a₁, χ₁)` tuples. -/
theorem lem12_prime_table (hΓ : IsMoore57 Γ) (x : Equiv.Perm V)
    (hx : ∀ a b, Γ.Adj a b ↔ Γ.Adj (x a) (x b))
    (p : ℕ) (hp : p.Prime) (hxp : x ^ p = 1) :
    True := by trivial

/-- **Lemma 12 (starred row `p = 3, a₀ = 1` cannot occur).** [done]

For any order-3 graph automorphism `σ` of a Moore57 graph,
`a₀(σ) = 1` leads to a contradiction.

Proof (mod-15 character-theoretic):
1. `aut_pow_prime_E7_trace_int` (with `p = 3`): `tr(E₇·P_σ) ∈ ℤ`.
2. `lem3_a1_mod_15` with that integer: `a₁ ≡ 7·a₀ + 5 (mod 15)`.
3. With `a₀ = 1`: `a₁ ≡ 12 (mod 15)`.
4. `lem12_p3_a1_eq_zero` (no-triangle, geometric): `a₁ = 0`.
5. `0 ≡ 12 (mod 15)` is false; contradiction. -/
theorem lem12_no_p3_a0_one
    (hΓ : IsMoore57 Γ) (σ : Equiv.Perm V)
    (hAut : ∀ a b : V, Γ.Adj a b ↔ Γ.Adj (σ a) (σ b))
    (hpow : σ ^ 3 = 1)
    (h_a0 : fixedVertexCount σ = 1) :
    False := by
  -- Step 1: trace is an integer.
  obtain ⟨z, hz⟩ := Moore57.aut_pow_prime_E7_trace_int hΓ σ hAut 3 hpow
  -- Step 2: a₁ ≡ 7·a₀ + 5 (mod 15).
  have h_mod := Moore57.Papers.MacajSiran2010.S2.lem3_a1_mod_15 hΓ σ hAut hz
  -- Step 3: with a₀ = 1, a₁ ≡ 12 (mod 15).
  rw [h_a0] at h_mod
  -- h_mod : a₁ ≡ 7 * 1 + 5 = 12 (mod 15)
  -- Step 4: a₁ = 0.
  have h_a1 := lem12_p3_a1_eq_zero hΓ σ hAut hpow
  -- Step 5: combine for contradiction.
  rw [h_a1] at h_mod
  -- h_mod : (0 : ℤ) ≡ 7 * 1 + 5 [ZMOD 15] = 12 (mod 15)
  unfold Int.ModEq at h_mod
  omega

/-- **Lemma 12 (conditional, starred row `p = 3, a₀ = 1`): geometric step
plus character constraint forces False.** [done]

Conditional paper-faithful contradiction: given an order-3 graph
automorphism `σ` and the (deferred) character-theoretic lower bound
`a₁(σ) ≥ 27` for the case `a₀(σ) = 1`, combine with the geometric
`lem12_p3_a1_eq_zero` (any order-3 aut has `a₁ = 0`) to derive False
by omega.

The character constraint `a₁ ∈ {27 + 45k}` (so `a₁ ≥ 27`) is the
remaining deferred-heavy piece (depends on Proposition 2). -/
theorem lem12_no_p3_a0_one_conditional
    (hΓ : IsMoore57 Γ) (σ : Equiv.Perm V)
    (hAut : ∀ a b : V, Γ.Adj a b ↔ Γ.Adj (σ a) (σ b))
    (hpow : σ ^ 3 = 1)
    (h_a1_ge : 27 ≤ adjacentMovedCount Γ σ) :
    False := by
  have h0 := lem12_p3_a1_eq_zero hΓ σ hAut hpow
  omega

/-- **Lemma 12 (p=7 starred row): if `Fix(σ)` contains the closed
neighbourhood of some vertex, then `a₁(σ) = 0`.** [done]

Geometric core of the `p = 7, a₀ = 58` starred case (and more
generally, any case where the star center `c` and all of `N(c)` are
fixed).  The proof uses Moore57 diameter 2:

* If `v ~ σv` with `v ≠ c` and `v ∉ N(c)`, then `v` is at distance 2
  from `c`, so the Moore57 `μ = 1` axiom gives a unique common
  neighbour `b ∈ N(v) ∩ N(c)`.
* `b ∈ N(c) ⊆ Fix(σ)` gives `σ b = b`.
* Applying `σ` to `v ~ b` yields `σv ~ b`.
* `v`, `σv`, `b` form a triangle, contradicting Moore57's `λ = 0`.

The case `v ∈ Fix(σ)` is ruled out by graph irreflexivity (`v ~ σv = v`
impossible).

For the `p = 7, a₀ = 58` row specifically, `a₀ = 58 = 2 + 7·8` and
`Fix(σ)` is a star with center `c` and `57` leaves filling `N(c)`,
which satisfies the hypothesis. -/
theorem lem12_a1_zero_of_closed_neighbourhood_fixed
    (hΓ : IsMoore57 Γ) (σ : Equiv.Perm V)
    (hAut : ∀ a b : V, Γ.Adj a b ↔ Γ.Adj (σ a) (σ b))
    (c : V)
    (h_fix_center : σ c = c)
    (h_fix_neighbours : ∀ v ∈ Γ.neighborSet c, σ v = v) :
    adjacentMovedCount Γ σ = 0 := by
  classical
  by_contra hne_zero
  have hpos : 0 < adjacentMovedCount Γ σ := Nat.pos_of_ne_zero hne_zero
  unfold adjacentMovedCount at hpos
  obtain ⟨v, hv_mem⟩ := Finset.card_pos.mp hpos
  rw [Finset.mem_filter] at hv_mem
  have hv : Γ.Adj v (σ v) := hv_mem.2
  -- v ≠ σv (else irrefl).
  have hv_ne_σv : v ≠ σ v := by
    intro h
    have hv' : Γ.Adj v v := by rw [← h] at hv; exact hv
    exact Γ.irrefl hv'
  -- v ≠ c (else σv = σc = c = v).
  have hv_ne_c : v ≠ c := by
    intro hc
    apply hv_ne_σv
    rw [hc, h_fix_center]
  -- v ∉ N(c) (else σv = v).
  have hv_not_adj_c : ¬ Γ.Adj v c := by
    intro h_adj_vc
    have hv_in_Nc : v ∈ Γ.neighborSet c := by
      rw [SimpleGraph.mem_neighborSet]
      exact h_adj_vc.symm
    exact hv_ne_σv (h_fix_neighbours v hv_in_Nc).symm
  -- Moore57 μ = 1: get a common neighbour b of v and c.
  have hμ : Fintype.card (Γ.commonNeighbors v c) = 1 :=
    hΓ.of_not_adj hv_ne_c hv_not_adj_c
  have h_card_pos : 0 < Fintype.card (Γ.commonNeighbors v c) := by
    rw [hμ]; decide
  have hne_subtype : Nonempty (Γ.commonNeighbors v c) :=
    Fintype.card_pos_iff.mp h_card_pos
  obtain ⟨⟨b, hb⟩⟩ := hne_subtype
  rw [SimpleGraph.mem_commonNeighbors] at hb
  obtain ⟨hvb, hcb⟩ := hb
  -- b ∈ N(c), so σ b = b.
  have hσb : σ b = b := by
    apply h_fix_neighbours
    rw [SimpleGraph.mem_neighborSet]
    exact hcb
  -- Apply σ to v ~ b: σv ~ σb = b.
  have hσvb : Γ.Adj (σ v) b := by
    have := (hAut v b).mp hvb
    rw [hσb] at this
    exact this
  -- Triangle v ~ σv, σv ~ b, b ~ v.
  exact hΓ.no_triangle hv hσvb hvb.symm

/-- **Lemma 12 (p=5 row) via FixedData dispatch.** [done]

Given an order-5 graph automorphism σ and a FixedData dispatch over the
three Lem 4 cases for p=5 (empty / pentagon / HS), conclude
`a₀(σ) ∈ {0, 5, 50}` matching the Lem 12 p=5 row.

Note: Lem 4 case 4 (pentagon p ∈ {5, 11}) gives a₀ = 5; case 6 (HS p = 5)
gives a₀ = 50; case 1 (empty p ∈ {5, 13}) gives a₀ = 0.  The full Lem 12
p=5 row would say "exactly these three values occur"; the dispatch
hypothesis is the deferred-heavy fix-shape classification (Lem 4 unified).

FixedData are bundled `Type`s, so the dispatch hypothesis uses
`Nonempty (...)` wrappers to live in `Prop`. -/
theorem lem12_p5_a0_dispatch
    (σ : Equiv.Perm V)
    (h_case : Nonempty (EmptyFixedData σ) ∨ Nonempty (C5FixedData Γ σ) ∨
              Nonempty (HSFixedData Γ σ)) :
    fixedVertexCount σ = 0 ∨ fixedVertexCount σ = 5 ∨
      fixedVertexCount σ = 50 := by
  rcases h_case with h0 | h5 | h50
  · obtain ⟨h⟩ := h0; left; exact h.fixedVertexCount_eq_zero
  · obtain ⟨h⟩ := h5; right; left; exact h.fixedVertexCount_eq_5
  · obtain ⟨h⟩ := h50; right; right; exact h.fixedVertexCount_eq_50

/-- **Lemma 12 (p=13 row) via EmptyFixedData.** [done]

For order 13, Lem 4 forces case 1 (empty fix) — the only case
consistent with `p = 13` is case 1 (p ∈ {5, 13}).  Given the
geometric `EmptyFixedData σ` (which encodes empty fix), `a₀(σ) = 0`.

The deferred piece is showing `EmptyFixedData σ` is the unique
applicable case for `p = 13`. -/
theorem lem12_p13_a0_zero_from_emptyFixedData
    (σ : Equiv.Perm V)
    (h : EmptyFixedData σ) :
    fixedVertexCount σ = 0 :=
  h.fixedVertexCount_eq_zero

/-- **Lemma 12 (p=3 row, a₀ = 10) via PetersenFixedData.** [done]

Non-starred Lem 12 p=3 row: a₀ = 10 (Petersen fix).  Given
`PetersenFixedData Γ σ`, `a₀(σ) = 10`. -/
theorem lem12_p3_a0_ten_from_petersenFixedData
    (σ : Equiv.Perm V)
    (h : PetersenFixedData Γ σ) :
    fixedVertexCount σ = 10 :=
  h.fixedVertexCount_eq_10

/-- **Lemma 12 (p=7 row, a₀ = 2) via SingletonFixedData (lone fix vertex).**
[done]

Lem 12 p=7 starred row has a₀ = 58 (closed neighbourhood fixed).  The
non-starred a₀ = 2 case corresponds to a "lone fix + leaf" (star with
one leaf), where `|N(a) ∩ Fix(σ)| = 1`.  Given `SingletonFixedData σ`
(only one σ-fixed vertex), `a₀ = 1`.  This isn't precisely the p=7 row
since `a₀ = 1` is the Lem 4 case (2) p ∈ {3, 19} not p=7. -/
theorem lem12_a0_one_from_singletonFixedData
    (σ : Equiv.Perm V)
    (h : SingletonFixedData σ) :
    fixedVertexCount σ = 1 :=
  h.fixedVertexCount_eq_one

/-- **Lemma 12 (corollary, starred row `p = 7, a₀ = 58` cannot occur).** [deferred-heavy]

The geometric `a₁ = 0` consequence is fully formalised in
`lem12_a1_zero_of_closed_neighbourhood_fixed`.  Combining this with
the character-theoretic `a₁ ∈ {21 + 105k : k ∈ ℕ}` (from
Proposition 2, deferred) yields the contradiction. -/
theorem lem12_no_p7_a0_58 (hΓ : IsMoore57 Γ) : True := by trivial

/-- **Lemma 12 (conditional, starred row `p = 7, a₀ = 58`): closed
neighbourhood geometric step plus character constraint forces False.** [done]

Conditional paper-faithful contradiction: given a graph automorphism
`σ` fixing some vertex `c` and all of its 57 neighbours (the geometric
content of `a₀(σ) = 58 = 1 + 57`), and the (deferred) character-
theoretic lower bound `a₁(σ) ≥ 21` for this row, combine with the
geometric `lem12_a1_zero_of_closed_neighbourhood_fixed` (closed-nbhd
fix ⟹ `a₁ = 0`) to derive False by omega.

The character constraint `a₁ ∈ {21 + 105k}` (so `a₁ ≥ 21`) is the
remaining deferred-heavy piece (depends on Proposition 2). -/
theorem lem12_no_p7_a0_58_conditional
    (hΓ : IsMoore57 Γ) (σ : Equiv.Perm V)
    (hAut : ∀ a b : V, Γ.Adj a b ↔ Γ.Adj (σ a) (σ b))
    (c : V) (hc : σ c = c)
    (h_nbhd : ∀ v ∈ Γ.neighborSet c, σ v = v)
    (h_a1_ge : 21 ≤ adjacentMovedCount Γ σ) :
    False := by
  have h0 := lem12_a1_zero_of_closed_neighbourhood_fixed hΓ σ hAut c hc h_nbhd
  omega

end Moore57.Papers.MacajSiran2010.S5
