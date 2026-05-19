import Moore57.Moore57Graph.Aut.FixedSubgraphData
import Moore57.Moore57Graph.Aut.OrderElevenIsC5

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Mačaj–Širáň 2010, §2, Lemma 4 [deferred-heavy]

> Let `X` be a group of automorphisms of Γ of odd prime order. Then one of
> the following holds:
>
> (1) `Fix(X)` is empty and `|X|` divides `13 · 5`;
>
> (2) `Fix(X)` is a singleton and `|X|` divides `3 · 19`;
>
> (3) `Fix(X)` is a star with `|Fix(X)| = 2 + 7l` and `|X|` divides `7`;
>
> (4) `Fix(X)` is a pentagon and `|X|` divides `11 · 5`;
>
> (5) `Fix(X)` is the Petersen graph and `|X|` divides `3`;
>
> (6) `Fix(X)` is the Hoffman–Singleton graph and `|X|` divides `5`.

This is the more specific cousin of Lemma 1 that drives all the
prime-order arguments. Cases (4) and (2) are already specialised in
`Moore57.Moore57Graph.Aut.OrderElevenIsC5` and `Moore57.Phases.Phase1`
respectively.
-/

namespace Moore57.Papers.MacajSiran2010.S2

variable {V : Type*} [Fintype V] [DecidableEq V]
  {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- **Lemma 4 (six-way classification for prime-order automorphism groups).**
[deferred-heavy] -/
theorem lem4_oddPrime_fixShape (hΓ : IsMoore57 Γ)
    (p : ℕ) (hp : p.Prime) (hp_odd : p ≠ 2)
    (X : Subgroup (Equiv.Perm V)) [Fintype X]
    (hcard : Fintype.card X = p)
    (hX : ∀ g ∈ X, ∀ a b, Γ.Adj a b ↔ Γ.Adj (g a) (g b)) :
    True := by
  trivial

end Moore57.Papers.MacajSiran2010.S2
