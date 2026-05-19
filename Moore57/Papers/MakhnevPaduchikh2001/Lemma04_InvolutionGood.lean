import Moore57.Papers.MakhnevPaduchikh2001.Lemma02_InvolutionFix

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Makhnev–Paduchikh 2001, Lemma 4 [skeleton]

> Every involution of `G` is "good" (in particular, every involution of
> `G` is an odd permutation; consequently `G = O(G) ⟨t⟩` for any
> involution `t`).

Used heavily downstream to obtain the `G = ⟨Y, t⟩ × X` decomposition in
the main theorem.
-/

namespace Moore57.Papers.MakhnevPaduchikh2001

variable {V : Type*} [Fintype V] [DecidableEq V]
  {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- **Lemma 4 (involutions are good / odd).** [skeleton] -/
theorem lem4_involution_good (hΓ : IsMoore57 Γ) : True := by trivial

end Moore57.Papers.MakhnevPaduchikh2001
