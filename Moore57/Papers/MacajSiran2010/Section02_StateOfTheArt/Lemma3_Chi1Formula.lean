import Moore57.D19OnMoore57.HigmanTrace.Congruence

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Mačaj–Širáň 2010, §2, Lemma 3 [skeleton]

> For any `x ∈ X`,
> ```
> χ₁(x) = (1/15)(8 a₀(x) + a₁(x) − 65),
> a₁(x) ≡ 7 a₀(x) + 5  (mod 15).
> ```

The congruence is the key tool used throughout §5 to constrain `a₁`. Proof:
follows directly from Theorem 1 and integrality of `χ₁(x)`.
-/

namespace Moore57.Papers.MacajSiran2010.S2

variable {V : Type*} [Fintype V] [DecidableEq V]
  {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- **Lemma 3 (χ₁ formula).** [skeleton] -/
theorem lem3_chi1_formula (hΓ : IsMoore57 Γ) (x : Equiv.Perm V)
    (hx : ∀ a b, Γ.Adj a b ↔ Γ.Adj (x a) (x b)) :
    True := by
  trivial

/-- **Lemma 3 (mod-15 congruence).** [skeleton] -/
theorem lem3_a1_mod_15 (hΓ : IsMoore57 Γ) (x : Equiv.Perm V)
    (hx : ∀ a b, Γ.Adj a b ↔ Γ.Adj (x a) (x b)) :
    True := by
  trivial

end Moore57.Papers.MacajSiran2010.S2
