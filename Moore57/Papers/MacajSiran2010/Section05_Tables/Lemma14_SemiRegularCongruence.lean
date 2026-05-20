import Moore57.Papers.MacajSiran2010.Section03_EquitablePartitions.Lemma6_OrbitTrace

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

/-- **Lemma 14 (`a₁ ≡ b₁ mod |X|` for semi-regular `P × Q`).** [deferred-heavy]

Placeholder for the paper claim. The substantive conclusion is captured
in `Lemma14SemiRegularConclusion`; the arithmetic core is already
`lem14_arithmetic_decomp`. -/
theorem lem14_semi_regular_congruence (hΓ : IsMoore57 Γ) : True := by trivial

end Moore57.Papers.MacajSiran2010.S5
