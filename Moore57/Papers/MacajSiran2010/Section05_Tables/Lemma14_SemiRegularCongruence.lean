import Moore57.Papers.MacajSiran2010.Section03_EquitablePartitions.Lemma6_OrbitTrace
import Moore57.Moore57Graph.Aut.SemiRegularComplement

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Mačaj–Širáň 2010, §5, Lemma 14 [deferred-heavy]

> Let `X = P × Q` be an automorphism group of Γ such that `P` (resp. `Q`)
> acts semi-regularly on `Γ \ Fix(P)` (resp. `Γ \ Fix(Q)`) and
> `(|P|, |Q|) = 1`. Then for any central element `x ∈ X`,
> ```
> a₁(x) ≡ b₁(x)  (mod |X|),
> ```
> where `b₁(x) = |{v ∈ Fix(P) ∪ Fix(Q) : v ∼ vˣ}|`. Moreover, if
> `x = x_P x_Q` with `x_P ∈ P, x_Q ∈ Q`, then
> `b₁(x) = b₁(x_P) + b₁(x_Q)`.

Status:
* `lem14_semi_regular_congruence`: paper-stub (semi-regular orbit
  decomposition + character decomposition, deferred-heavy).
* `lem14_arithmetic_decomp`: **proven** — pure ℤ arithmetic packaging
  the decomposition `a₁ ≡ b₁_P + b₁_Q (mod n)`.
-/

namespace Moore57.Papers.MacajSiran2010.S5

variable {V : Type*} [Fintype V] [DecidableEq V]
  {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- **Lemma 14 arithmetic: `a₁ ≡ b₁_P + b₁_Q (mod |X|)` decomposition**.
[done]

The paper's congruence packaging: given `a₁ ≡ b₁ (mod n)` (the
semi-regular congruence) and `b₁ = b₁_P + b₁_Q` (the additive
decomposition by central `x = x_P · x_Q`), the combined statement is
`a₁ ≡ b₁_P + b₁_Q (mod n)`. -/
theorem lem14_arithmetic_decomp
    (a1 b1 b1_P b1_Q : ℤ) (n : ℤ)
    (h_cong : a1 ≡ b1 [ZMOD n])
    (h_decomp : b1 = b1_P + b1_Q) :
    a1 ≡ b1_P + b1_Q [ZMOD n] := by
  rw [← h_decomp]
  exact h_cong

/-- **Lemma 14 (`a₁ ≡ b₁ mod |X|` for semi-regular `P × Q`) — abstract conclusion.**

For an automorphism group `X = P × Q` of Γ where `P` acts semi-regularly on
`Γ \ Fix(P)` and `Q` on `Γ \ Fix(Q)` (and `(|P|, |Q|) = 1`), and any
**central** element `x ∈ X` (which factorizes uniquely as `x = x_P · x_Q`
with `x_P ∈ P, x_Q ∈ Q`),

```
a₁(x) ≡ b₁(x_P) + b₁(x_Q)  (mod |X|),
```

where `b₁(y) := |{v ∈ Fix(P) ∪ Fix(Q) : v ∼ vʸ}|`.

We encode this as the proposition `Lemma14SemiRegularConclusion`. The
arithmetic packaging (`a₁ ≡ b₁ mod n` plus `b₁ = b₁_P + b₁_Q`) is
proven in `lem14_arithmetic_decomp` above; the deferred-heavy piece is
the semi-regular orbit decomposition that produces the input
congruence `a₁ ≡ b₁ (mod |X|)`. -/
def Lemma14SemiRegularConclusion
    (n : ℤ) (a1 b1_P b1_Q : ℤ) : Prop :=
  a1 ≡ b1_P + b1_Q [ZMOD n]

/-- **Lemma 14 (proper-signature conditional form).** [done — conditional]

Paper-faithful proper-signature wrapper: given the (deferred) semi-regular
orbit congruence `a₁ ≡ b₁ [ZMOD n]` and the additive decomposition
`b₁ = b₁_P + b₁_Q` from the `P × Q` factorization of a central element,
the paper claim `a₁ ≡ b₁_P + b₁_Q [ZMOD n]` follows from
`lem14_arithmetic_decomp`.

The remaining (deferred-heavy) gap is the semi-regular orbit decomposition
that produces the congruence `a₁ ≡ b₁ [ZMOD |X|]`. -/
theorem lem14_semi_regular_congruence_paper
    (hΓ : IsMoore57 Γ)
    (a1 b1 b1_P b1_Q : ℤ) (n : ℤ)
    (h_cong : a1 ≡ b1 [ZMOD n])
    (h_decomp : b1 = b1_P + b1_Q) :
    Lemma14SemiRegularConclusion n a1 b1_P b1_Q :=
  lem14_arithmetic_decomp a1 b1 b1_P b1_Q n h_cong h_decomp

/-- **Lemma 14 single-prime case (paper-faithful, unconditional from
graph-aut + semi-regular hypothesis).**

For a graph automorphism `σ` fixing vertex `a`, if σ acts semi-regularly
on the moved neighbour set `N(a) \ Fix(σ)` (`hsemi`), then
```
(autFixedNeighborFinset Γ σ a).card ≡ Γ.degree a  [MOD orderOf σ].
```

This is the **single-prime semi-regular congruence** at the core of MS
2010 §5 Lem 14 (the `P × Q` mixed-prime version then composes two such
congruences with coprime moduli).

Proof: `Moore57.aut_card_degree_eq_fixedNeighbourCount_add_orderOf_mul`
gives `Γ.degree a = card + k' · orderOf σ`; reading mod `orderOf σ`
yields the congruence. -/
theorem lem14_semiRegular_congruence_paper_faithful
    (σ : Equiv.Perm V)
    (smul_adj : ∀ v w : V, Γ.Adj v w ↔ Γ.Adj (σ v) (σ w))
    {a : V} (ha : σ a = a)
    (hsemi : ∀ w ∈ Moore57.autMovedNeighborFinset Γ σ a,
             ∀ k : ℕ, (σ ^ k) w = w → orderOf σ ∣ k) :
    (Moore57.autFixedNeighborFinset Γ σ a).card ≡ Γ.degree a
      [MOD orderOf σ] := by
  classical
  -- Wrapper from session-8 graph-aut module.
  obtain ⟨k', hk'⟩ :=
    Moore57.aut_card_degree_eq_fixedNeighbourCount_add_orderOf_mul
      (Γ := Γ) σ smul_adj ha hsemi
  -- Pull out `card ≤ Γ.degree a` from `Γ.degree a = card + k' · orderOf σ`.
  have hle : (Moore57.autFixedNeighborFinset Γ σ a).card ≤ Γ.degree a := by
    rw [hk']; exact Nat.le_add_right _ _
  -- `Γ.degree a - card = k' · orderOf σ`, so `orderOf σ ∣ Γ.degree a - card`.
  have hsub :
      Γ.degree a - (Moore57.autFixedNeighborFinset Γ σ a).card =
        k' * orderOf σ := by omega
  have hdvd : orderOf σ ∣
      Γ.degree a - (Moore57.autFixedNeighborFinset Γ σ a).card := by
    rw [hsub]; exact ⟨k', mul_comm _ _⟩
  exact (Nat.modEq_iff_dvd' hle).mpr hdvd

/-- **Lemma 14 prime-order version (fully automatic).**

For a graph automorphism `σ` of prime order `p` (`σ^p = 1`, `p` prime)
fixing vertex `a`, the semi-regular hypothesis is automatic, and so
```
(autFixedNeighborFinset Γ σ a).card ≡ Γ.degree a  [MOD orderOf σ].
```

The Moore57 specialisation `Γ.degree a = 57` is the corollary
`lem14_moore57_semiRegular_congruence_of_prime` below. -/
theorem lem14_semiRegular_congruence_of_prime
    (σ : Equiv.Perm V) (p : ℕ) (hp : Nat.Prime p) (hpp : σ ^ p = 1)
    (smul_adj : ∀ v w : V, Γ.Adj v w ↔ Γ.Adj (σ v) (σ w))
    {a : V} (ha : σ a = a) :
    (Moore57.autFixedNeighborFinset Γ σ a).card ≡ Γ.degree a
      [MOD orderOf σ] :=
  lem14_semiRegular_congruence_paper_faithful σ smul_adj ha
    (Moore57.aut_semiRegular_at_movedNeighbor_of_prime σ p hp hpp a)

/-- **Lemma 14 Moore57 specialisation (paper-faithful, prime-order).**

For a Moore57 graph and a prime-order graph automorphism `σ` fixing a
vertex `a`, the σ-fixed-neighbour count of `a` satisfies
```
(autFixedNeighborFinset Γ σ a).card ≡ 57  [MOD orderOf σ].
```

This is the Moore57 single-prime instance of MS 2010 Lem 14: the
fixed-neighbour count at a σ-fixed vertex is congruent to the graph
degree (57 for Moore57) modulo the prime order of σ. -/
theorem lem14_moore57_semiRegular_congruence_of_prime
    (hΓ : IsMoore57 Γ) (σ : Equiv.Perm V) (p : ℕ) (hp : Nat.Prime p)
    (hpp : σ ^ p = 1)
    (smul_adj : ∀ v w : V, Γ.Adj v w ↔ Γ.Adj (σ v) (σ w))
    {a : V} (ha : σ a = a) :
    (Moore57.autFixedNeighborFinset Γ σ a).card ≡ 57
      [MOD orderOf σ] := by
  have hmod :=
    lem14_semiRegular_congruence_of_prime σ p hp hpp smul_adj ha
  have hdeg : Γ.degree a = 57 := hΓ.regular.degree_eq a
  rw [hdeg] at hmod
  exact hmod

/-- **Lemma 14 (`a₁ ≡ b₁ mod |X|` for semi-regular `P × Q`).** [deferred-heavy]

Placeholder for the paper claim. The substantive conclusion is captured
in `Lemma14SemiRegularConclusion`; the arithmetic core is already
`lem14_arithmetic_decomp`. Proper-signature form is
`lem14_semi_regular_congruence_paper`.

The single-prime semi-regular congruence at the heart of the paper proof
is now `lem14_semiRegular_congruence_paper_faithful` (graph-aut +
`hsemi`) and `lem14_semiRegular_congruence_of_prime` (prime order, no
extra hypothesis). The mixed-prime `P × Q` composition remains the
deferred-heavy step. -/
theorem lem14_semi_regular_congruence (hΓ : IsMoore57 Γ) : True := by trivial

end Moore57.Papers.MacajSiran2010.S5
