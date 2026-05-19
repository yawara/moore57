import Moore57.Papers.MacajSiran2010.Section08_Theorem5Proof.Proposition3_HSFixBound
import Moore57.Papers.MacajSiran2010.Section08_Theorem5Proof.Proposition4_SG625Excluded
import Moore57.Papers.MacajSiran2010.Section08_Theorem5Proof.Proposition5_OrbitSize125
import Moore57.Papers.MacajSiran2010.Section06_PGroupsOverview.Theorem5_5GroupBound

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Mačaj–Širáň 2010, §8, Theorem 5 (full proof) [skeleton]

> Let `X` be a group of automorphisms of Γ of order a power of 5. Then one
> of the following holds:
>
> (1) `Fix(X)` is the Hoffman–Singleton graph and `|X|` divides `5`;
>
> (2) `Fix(X)` is a pentagon and `|X|` divides `25`;
>
> (3) `Fix(X)` is empty and `|X|` divides `125`.

Proof structure:
- (1) from Proposition 3.
- (2) follows from (1) in much the same way as in Lemma 18.
- (3) by demonstrating non-existence of |X| = 625 via Lemma 22 +
  Proposition 4 (case smallest orbit 25) and Proposition 5
  (case smallest orbit 125).
-/

namespace Moore57.Papers.MacajSiran2010.S8

variable {V : Type*} [Fintype V] [DecidableEq V]
  {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- **Theorem 5 (full 5-group classification).** [skeleton] -/
theorem thm5_final (hΓ : IsMoore57 Γ) : True := by trivial

end Moore57.Papers.MacajSiran2010.S8
