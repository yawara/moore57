import Moore57.Papers.MakhnevPaduchikh2001.Citation
import Moore57.Papers.MakhnevPaduchikh2001.Lemma01_StrongFix
import Moore57.Papers.MakhnevPaduchikh2001.Lemma02_InvolutionFix
import Moore57.Papers.MakhnevPaduchikh2001.Lemma03_OddPrimeFix
import Moore57.Papers.MakhnevPaduchikh2001.Lemma04_InvolutionGood
import Moore57.Papers.MakhnevPaduchikh2001.Lemmas05_to_09_Structure

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Makhnev–Paduchikh 2001 — main theorem [skeleton]

> Let Γ be the Aschbacher graph and `G = Aut(Γ)`. Assume that `G` contains
> an involution `t`. Then:
>
> (1) `Fix(t)` is a star with 56 vertices;
>
> (2) `G = ⟨Y, t⟩ × X` for some subgroups `X` and `Y` of odd order, `Y` is
>     inverted by `t`, and either `|Y|` divides 5 or 57, or `|Y|` divides
>     21 (and for `|Y| = 21`, `|Fix(y)| = 37` for an order-7 element
>     `y ∈ Y`);
>
> (3) if `X ≠ 1` then `Fix(X)` is one of: a star (`Y = 1, |X| = 7`); a
>     pentagon (`|Y| | 5, |X| | 55`); Petersen's graph (`|Y| | 3, |X| | 27`);
>     Hoffman–Singleton's graph (`|Y| | 5 or 7, |X| | 25`).

Imported by `Moore57.Papers.MacajSiran2010.Section02_StateOfTheArt.Theorem2_MakhnevPaduchikh`.
-/

namespace Moore57.Papers.MakhnevPaduchikh2001

variable {V : Type*} [Fintype V] [DecidableEq V]
  {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- **Main theorem (1) (`Fix(t)` is a 56-vertex star).** [skeleton] -/
theorem main_fix_t_star (hΓ : IsMoore57 Γ) : True := by trivial

/-- **Main theorem (2) (decomposition `G = ⟨Y, t⟩ × X`).** [skeleton] -/
theorem main_decomposition (hΓ : IsMoore57 Γ) : True := by trivial

/-- **Main theorem (3) (`Fix(X)` cases when `X ≠ 1`).** [skeleton] -/
theorem main_fix_X_cases (hΓ : IsMoore57 Γ) : True := by trivial

end Moore57.Papers.MakhnevPaduchikh2001
