import Moore57.Papers.MacajSiran2010.Section03_EquitablePartitions.Lemma6_OrbitTrace

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Mačaj–Širáň 2010, §5, Lemma 14 [skeleton]

> Let `X = P × Q` be an automorphism group of Γ such that `P` (resp. `Q`)
> acts semi-regularly on `Γ \ Fix(P)` (resp. `Γ \ Fix(Q)`) and
> `(|P|, |Q|) = 1`. Then for any central element `x ∈ X`,
> ```
> a₁(x) ≡ b₁(x)  (mod |X|),
> ```
> where `b₁(x) = |{v ∈ Fix(P) ∪ Fix(Q) : v ∼ vˣ}|`. Moreover, if
> `x = x_P x_Q` with `x_P ∈ P, x_Q ∈ Q`, then
> `b₁(x) = b₁(x_P) + b₁(x_Q)`.
-/

namespace Moore57.Papers.MacajSiran2010.S5

variable {V : Type*} [Fintype V] [DecidableEq V]
  {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- **Lemma 14 (`a₁ ≡ b₁ mod |X|` for semi-regular `P × Q`).** [skeleton] -/
theorem lem14_semi_regular_congruence (hΓ : IsMoore57 Γ) : True := by trivial

end Moore57.Papers.MacajSiran2010.S5
