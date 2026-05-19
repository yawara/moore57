import Moore57.Papers.MacajSiran2010.Section04_Characters.Proposition2_CharacterSystem
import Moore57.Papers.MacajSiran2010.Section02_StateOfTheArt.Lemma3_Chi1Formula
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
- Starred cases `p = 3, a₀ = 1` and `p = 7, a₀ = 58` cannot occur (these
  are non-existence statements proved as part of the D19 / Hoffman–Singleton
  work — remain skeletons here).
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

/-- **Lemma 12 (prime-order `(a₀, a₁, χ₁)` table — full statement).** [skeleton]
The full 17-row classification of admissible `(p, a₀, a₁, χ₁)` tuples. -/
theorem lem12_prime_table (hΓ : IsMoore57 Γ) (x : Equiv.Perm V)
    (hx : ∀ a b, Γ.Adj a b ↔ Γ.Adj (x a) (x b))
    (p : ℕ) (hp : p.Prime) (hxp : x ^ p = 1) :
    True := by trivial

/-- **Lemma 12 (corollary, starred row `p = 3, a₀ = 1` cannot occur).** [skeleton] -/
theorem lem12_no_p3_a0_one (hΓ : IsMoore57 Γ) : True := by trivial

/-- **Lemma 12 (corollary, starred row `p = 7, a₀ = 58` cannot occur).** [skeleton] -/
theorem lem12_no_p7_a0_58 (hΓ : IsMoore57 Γ) : True := by trivial

end Moore57.Papers.MacajSiran2010.S5
