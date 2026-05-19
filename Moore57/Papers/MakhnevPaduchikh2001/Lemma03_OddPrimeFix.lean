import Moore57.Moore57Graph.Moore57Definition

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Makhnev–Paduchikh 2001, Lemma 3 [skeleton]

> Let `X` be a subgroup of odd prime order in `G = Aut(Γ)`. Then `Fix(X)`
> is one of: empty, a singleton, a star, a pentagon, the Petersen graph,
> or the Hoffman–Singleton graph; in each case, the prime divides a
> specific bound (cf. Mačaj–Širáň, Lemma 4 — that is the same statement).
-/

namespace Moore57.Papers.MakhnevPaduchikh2001

variable {V : Type*} [Fintype V] [DecidableEq V]
  {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- **Lemma 3 (odd-prime-order Fix structure).** [skeleton] -/
theorem lem3_odd_prime_fix (hΓ : IsMoore57 Γ) : True := by trivial

end Moore57.Papers.MakhnevPaduchikh2001
