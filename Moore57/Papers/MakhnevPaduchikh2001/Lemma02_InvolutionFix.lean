import Moore57.Moore57Graph.Aut.InvolutionCandidates
import Moore57.Moore57Graph.Aut.InvolutionFixIsK155

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Makhnev–Paduchikh 2001, Lemma 2 [wrap candidate]

> Let Γ be a Moore graph of valence `k ≥ 3` and `t` an involution of
> `Aut(Γ)`. Then `Fix(t)` is a star centered at some vertex `a`.

This is the bedrock fact used downstream by Mačaj–Širáň as
"involution fixes a 56-vertex star". The Moore57 codebase already has a
formalization in `Moore57.Moore57Graph.Aut.InvolutionFixIsK155`.
-/

namespace Moore57.Papers.MakhnevPaduchikh2001

variable {V : Type*} [Fintype V] [DecidableEq V]
  {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- **Lemma 2 (involution fixes a star).** [skeleton] -/
theorem lem2_involution_fix_star (hΓ : IsMoore57 Γ) : True := by trivial

end Moore57.Papers.MakhnevPaduchikh2001
