import Moore57.Moore57Graph.Moore57Definition

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Aschbacher 1971, Lemma 1.1 [skeleton]

> Let `𝒢` be a triangle-free, irreflexive 1-system with `d(A, B) ≤ 2` for
> all `A, B ∈ ℰ`. Then `𝒢` is either regular or a star.

This is the structural backbone behind both Mačaj–Širáň 2010 Lemma 1 and
Makhnev–Paduchikh 2001 Lemma 1: any strong (λ = 0, μ = 1) graph with all
pairs at distance ≤ 2 is either regular (Moore graph candidate, valence
∈ {2, 3, 7, 57} by Lemma 1.3) or a star.

This is not specific to Moore57; the statement is over a general graph.
-/

namespace Moore57.Papers.Aschbacher1971

variable {V : Type*} [Fintype V] [DecidableEq V]
  {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- **Lemma 1.1 (regular-or-star dichotomy).** [skeleton] -/
theorem lem1_1_regular_or_star : True := by trivial

end Moore57.Papers.Aschbacher1971
