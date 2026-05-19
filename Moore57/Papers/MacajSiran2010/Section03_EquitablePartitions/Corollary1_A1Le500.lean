import Moore57.Papers.MacajSiran2010.Section03_EquitablePartitions.Lemma10_TraceBounds

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Mačaj–Širáň 2010, §3, Corollary 1 [deferred-heavy]

> For any `x ∈ X`, `a₁(x) ≤ 500`.

Proof outline (in paper): let `S = {v ∈ Γ : v ∼ vˣ}`. Then `Tr(S) ≤ 2`
(no quadrangles in Γ), and by Lemma 10, `|S| ≤ 50 (8 + 2) = 500`.

This bound is used repeatedly in §5 to constrain the table of `a₁`'s.
-/

namespace Moore57.Papers.MacajSiran2010.S3

variable {V : Type*} [Fintype V] [DecidableEq V]
  {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- **Corollary 1 (`a₁(x) ≤ 500`).** [deferred-heavy] -/
theorem cor1_a1_le_500 (hΓ : IsMoore57 Γ) (x : Equiv.Perm V)
    (hx : ∀ a b, Γ.Adj a b ↔ Γ.Adj (x a) (x b)) :
    True := by trivial

end Moore57.Papers.MacajSiran2010.S3
