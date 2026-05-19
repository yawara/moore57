import Moore57.Papers.MacajSiran2010.Section03_EquitablePartitions.Definition

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Mačaj–Širáň 2010, §3, Lemma 7 [skeleton]

> If `x ∈ X` is central and contributing to `O`, then
> `|{v ∈ O : vˣ ∼ v}| = |O|`.

Equivalent: every vertex of `O` is moved by `x` to an adjacent vertex.
-/

namespace Moore57.Papers.MacajSiran2010.S3

variable {V : Type*} [Fintype V] [DecidableEq V]
  {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- **Lemma 7 (central contribution is total on the orbit).** [skeleton] -/
theorem lem7_central_full_contribution (hΓ : IsMoore57 Γ) : True := by trivial

end Moore57.Papers.MacajSiran2010.S3
