import Moore57.Papers.MacajSiran2010.Section03_EquitablePartitions.Definition

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Mačaj–Širáň 2010, §3, Lemma 6 [skeleton]

> Let `O` be an orbit of `X` and let `x ∈ X` contribute to `O` (i.e., for
> some `v ∈ O`, `vˣ ∼ v`). Then
>
> (1) `x⁻¹` contributes to `O`;
>
> (2) if `|X|` is odd, then `Tr(X)` is even;
>
> (3) if `x` is central in `X`, then `Tr(O) ≤ 2`;
>
> (4) `Tr(O)² < |O|`.

`Tr(O)` is the average degree of the subgraph induced by `O`.
-/

namespace Moore57.Papers.MacajSiran2010.S3

variable {V : Type*} [Fintype V] [DecidableEq V]
  {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- **Lemma 6 (1) (inverse also contributes).** [skeleton] -/
theorem lem6_inverse_contributes (hΓ : IsMoore57 Γ) : True := by trivial

/-- **Lemma 6 (2) (odd `|X|` ⇒ `Tr(X)` even).** [skeleton] -/
theorem lem6_trace_even_of_odd_order (hΓ : IsMoore57 Γ) : True := by trivial

/-- **Lemma 6 (3) (central ⇒ `Tr(O) ≤ 2`).** [skeleton] -/
theorem lem6_central_trace_le_two (hΓ : IsMoore57 Γ) : True := by trivial

/-- **Lemma 6 (4) (`Tr(O)² < |O|`).** [skeleton] -/
theorem lem6_trace_sq_lt_size (hΓ : IsMoore57 Γ) : True := by trivial

end Moore57.Papers.MacajSiran2010.S3
