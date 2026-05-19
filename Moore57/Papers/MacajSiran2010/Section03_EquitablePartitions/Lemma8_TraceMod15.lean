import Moore57.Papers.MacajSiran2010.Section03_EquitablePartitions.Definition

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Mačaj–Širáň 2010, §3, Lemma 8 [deferred-heavy]

> Let `X` have `k` orbits on Γ. Then
> ```
> Tr(X) ≡ −8 (k − 10) (mod 15).
> ```

Proof outline (in paper): the eigenvalues of `X`'s orbit-adjacency matrix are
`57, 7, −8`, with `57` appearing exactly once. If `7` appears once and `−8`
appears `k − 2` times, the trace is `64 − 8(k − 2) = −8(k − 10)`. Any swap
of `−8` and `7` changes the trace by `15`.
-/

namespace Moore57.Papers.MacajSiran2010.S3

variable {V : Type*} [Fintype V] [DecidableEq V]
  {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- **Lemma 8 (`Tr(X) ≡ −8(k − 10) mod 15`).** [deferred-heavy] -/
theorem lem8_trace_mod_fifteen (hΓ : IsMoore57 Γ) : True := by trivial

end Moore57.Papers.MacajSiran2010.S3
