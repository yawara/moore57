import Moore57.Moore57Graph.Moore57Definition

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Cameron Ch.3 §3.12 — Wielandt's theorem

**Theorem 3.25** (Wielandt 1956). Let `p` be a prime, `G` a primitive
permutation group of degree `2p` which is not 2-transitive. Then
`p = 2s² + 2s + 1` for some positive integer `s`, and `G` has rank 3
with subdegrees `1, s(2s + 1), (s + 1)(2s + 1)`.

In particular `p = 5` is the only known prime where a non-2-transitive
primitive group of degree `2p` exists (the Petersen graph case, `s = 1`).
Whether other `s` produce examples is an open problem.

Tangential to Moore57. [skeleton]
-/

namespace Moore57.Papers.CameronCh3

/-- **Theorem 3.25 (Wielandt, primitive degree-`2p` non-2-transitive ⇒ rank 3).** [skeleton] -/
theorem theorem3_25_wielandt : True := by trivial

end Moore57.Papers.CameronCh3
