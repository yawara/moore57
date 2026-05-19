import Moore57.Papers.MacajSiran2010.Section03_EquitablePartitions.Definition

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Mačaj–Širáň 2010, §3, Lemma 10 [deferred-heavy]

> For any `S ⊆ V(Γ)`,
> ```
> −8 + |S|/50 ≤ Tr(S) ≤ 7 + |S|/65.
> ```

Proof outline (in paper): use Mohar's edge-cut inequality
`(57 − 7) · |S|(3250 − |S|) / 3250 ≤ e(S, Γ \ S) ≤ (57 + 8) · …`
and rearrange via `e(S, Γ \ S) = |S|(57 − Tr(S))`.
-/

namespace Moore57.Papers.MacajSiran2010.S3

variable {V : Type*} [Fintype V] [DecidableEq V]
  {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- **Lemma 10 (spectral trace bounds).** [deferred-heavy] -/
theorem lem10_trace_bounds (hΓ : IsMoore57 Γ) : True := by trivial

end Moore57.Papers.MacajSiran2010.S3
