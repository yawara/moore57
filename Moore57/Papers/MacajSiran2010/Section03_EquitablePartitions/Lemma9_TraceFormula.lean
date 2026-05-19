import Moore57.Papers.MacajSiran2010.Section03_EquitablePartitions.Definition

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Mačaj–Širáň 2010, §3, Lemma 9 [deferred-heavy]

> (1) Let `O` be an orbit of `X` and let `v ∈ O`. Then
> ```
> Tr(O) = |{x ∈ X : v ∼ vˣ}| · |O| / |X|.
> ```
>
> (2) ```
> |X| · Tr(X) = |{(x, v) ∈ X × Γ : v ∼ vˣ}| = Σ_{x ∈ X} a₁(x).
> ```
-/

namespace Moore57.Papers.MacajSiran2010.S3

variable {V : Type*} [Fintype V] [DecidableEq V]
  {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- **Lemma 9 (1) (orbit trace formula).** [deferred-heavy] -/
theorem lem9_orbit_trace_formula (hΓ : IsMoore57 Γ) : True := by trivial

/-- **Lemma 9 (2) (`|X| · Tr(X) = Σ_x a₁(x)`).** [deferred-heavy] -/
theorem lem9_global_trace_formula (hΓ : IsMoore57 Γ) : True := by trivial

end Moore57.Papers.MacajSiran2010.S3
