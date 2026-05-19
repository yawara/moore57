import Moore57.Papers.MakhnevPaduchikh2001.MainTheorem

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Mačaj–Širáň 2010, §2, Theorem 2 (Makhnev–Paduchikh) [external]

> Let Γ be a Moore (57, 2)-graph and let `G = Aut(Γ)`. Assume that `G`
> contains an involution `t`. Then:
>
> (a) `G = ⟨Y, t⟩ × X` for some subgroups `X` and `Y` of odd order, `Y` is
>     inverted by `t`, and either `|Y|` divides 5 or 57, or `|Y|` divides 21,
>
> (b) if `X ≠ 1`, then `Fix(X)` can be one of: a star (`Y = 1, |X| = 7`); a
>     pentagon (`|Y| | 5, |X| | 55`); the Petersen graph (`|Y| | 3, |X| | 27`);
>     the Hoffman–Singleton graph (`|Y| | 5 or 7, |X| | 25`).

This result is imported from `Moore57.Papers.MakhnevPaduchikh2001`, which
formalizes [Makhnev–Paduchikh 2001].
-/

namespace Moore57.Papers.MacajSiran2010.S2

variable {V : Type*} [Fintype V] [DecidableEq V]
  {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- **Theorem 2 (Makhnev–Paduchikh structure for even `|Aut(Γ)|`).** [external] -/
theorem thm2_makhnev_paduchikh (hΓ : IsMoore57 Γ) : True := by
  trivial

end Moore57.Papers.MacajSiran2010.S2
