import Moore57.Moore57Graph.Moore57Definition

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Cameron Ch.3 §3.6 — The Hoffman–Singleton graph

Constructive existence of the unique Moore graph of diameter 2 and
valency 7. Vertex set: the 35 three-subsets of `{1, …, 7}` plus 15
projective planes on `{1, …, 7}` (one of two `A_7`-orbits). Two 3-sets
joined iff disjoint; a 3-set joined to a plane iff it is a line of the
plane; two planes never joined.

Cameron's construction uses GAP/GRAPE and verifies:

* `n = (7 choose 3) + 15 = 35 + 15 = 50`.
* Valency 7.
* Diameter 2.
* Aut(HS) has index-2 simple subgroup `PSU(3, 5²)`.
* From the HS graph, the Higman–Sims sporadic simple group is
  constructed (via cocliques of size 15).

For Moore57 this section is orthogonal — included for completeness.
[out-of-scope — Moore57 non-existence does not depend on the existence
of the Hoffman-Singleton graph; only on numerical constraints.]
-/

namespace Moore57.Papers.CameronCh3

/-- **Hoffman–Singleton graph (existence + uniqueness).** [out-of-scope]

Constructive existence (Robertson's 1969 explicit construction) is
intentionally NOT formalised here: it does not feed into any Moore57
non-existence chain. -/
theorem hoffman_singleton_existence : True := by trivial

end Moore57.Papers.CameronCh3
