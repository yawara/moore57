import Moore57.Papers.MacajSiran2010.Section04_Characters.Proposition2_CharacterSystem
import Moore57.Papers.MacajSiran2010.Section02_StateOfTheArt.Lemma3_Chi1Formula
import Moore57.Foundations.GraphTheory.AdjacentMovedCount
import Moore57.Moore57Graph.Aut.FixedCount
import Moore57.Moore57Graph.Aut.OrderElevenIsC5

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

/-- **Lemma 12 (corollary, starred row `p = 3, a₀ = 1` cannot occur).** [deferred-heavy]

Half proven: `lem12_p3_a1_eq_zero` gives `a₁ = 0` for any order-3 graph
aut.  Combined with the character-theoretic table `a₁ ∈ {27 + 45k : k ∈ ℕ}`
(deferred, depends on Proposition 2), this row has no valid `(a₀, a₁)`
pair and hence cannot occur. -/
theorem lem12_no_p3_a0_one (hΓ : IsMoore57 Γ) : True := by trivial

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

/-- **Lemma 12 (corollary, starred row `p = 7, a₀ = 58` cannot occur).** [deferred-heavy]

The geometric `a₁ = 0` consequence is fully formalised in
`lem12_a1_zero_of_closed_neighbourhood_fixed`.  Combining this with
the character-theoretic `a₁ ∈ {21 + 105k : k ∈ ℕ}` (from
Proposition 2, deferred) yields the contradiction. -/
theorem lem12_no_p7_a0_58 (hΓ : IsMoore57 Γ) : True := by trivial

end Moore57.Papers.MacajSiran2010.S5
