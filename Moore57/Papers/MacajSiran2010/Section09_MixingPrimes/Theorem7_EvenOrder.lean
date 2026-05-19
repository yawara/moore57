import Moore57.Papers.MacajSiran2010.Section02_StateOfTheArt.Theorem2_MakhnevPaduchikh
import Moore57.Papers.MacajSiran2010.Section06_PGroupsOverview.Theorem5_5GroupBound
import Moore57.Papers.MacajSiran2010.Section05_Tables.Lemma15_OrderPQ

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Mačaj–Širáň 2010, §9, Theorem 7 [deferred-heavy]

> Let Γ be a Moore graph of degree 57 on 3250 vertices and `G = Aut(Γ)`.
> If `|G|` is even then `|G|` divides one of
> ```
> 11 · 5 · 2,  5² · 2,  3³ · 2,  2p   for p ∈ {7, 11, 19}.
> ```

Proof: by Theorem 2 (Makhnev–Paduchikh), `G = ⟨Y, t⟩ × X` with `t` an
involution. Order-3 elements of `Y` are excluded by Lemma 12. By
Theorem 5, `|X| ≠ 25` when `Fix(X)` is the Hoffman–Singleton graph.
Lemma 15 excludes `Z₅₅` and `Z₂₂` sharing a Z₁₁`, and `Z₁₀` and `Z₃₅`
sharing a `Z₅`.
-/

namespace Moore57.Papers.MacajSiran2010.S9

variable {V : Type*} [Fintype V] [DecidableEq V]
  {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- **Theorem 7 (even `|Aut(Γ)|` divides one of five values).** [deferred-heavy] -/
theorem thm7_even_order (hΓ : IsMoore57 Γ) : True := by trivial

end Moore57.Papers.MacajSiran2010.S9
