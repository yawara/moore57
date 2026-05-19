import Moore57.Moore57Graph.Moore57Definition

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Cameron Ch.3 §3.2 — Algebraic theory

**Theorem 3.2.** The basis algebra of a coherent configuration is a
direct sum of complete matrix algebras over `ℂ`. In the group case, the
degrees are the multiplicities of the irreducible constituents of the
permutation character.

**Corollary 3.3.** The basis algebra of a coherent configuration arising
from a permutation group `G` is commutative iff the permutation
character of `G` is multiplicity-free.

**Theorem 3.4.** Define the *intersection matrices* `P_j` by
`(P_j)_{s,t} = p_{tj}^s`. Their `ℂ`-span is an algebra (the *intersection
algebra*), and `A_i ↦ P_i` extends to a `ℂ`-algebra isomorphism from
the basis algebra. Identity: `Σ_s p_{ij}^s p_{sk}^u = Σ_t p_{jk}^t p_{it}^u`
(associative law of matrix multiplication, picture in Figure 3.1).

[skeleton]
-/

namespace Moore57.Papers.CameronCh3

/-- **Theorem 3.2 (Wedderburn decomposition).** [skeleton] -/
theorem theorem3_2_wedderburn : True := by trivial

/-- **Corollary 3.3 (commutativity ⇔ multiplicity-free).** [skeleton] -/
theorem cor3_3_commutative_iff_mult_free : True := by trivial

/-- **Theorem 3.4 (basis ≃ intersection algebra).** [skeleton] -/
theorem theorem3_4_basis_intersection_iso : True := by trivial

end Moore57.Papers.CameronCh3
