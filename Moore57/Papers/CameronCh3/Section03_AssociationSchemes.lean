import Moore57.Moore57Graph.Moore57Definition

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Cameron Ch.3 §3.3 — Association schemes

A *commutative association scheme* is a coherent configuration whose
basis matrices commute. A *symmetric association scheme* is one whose
basis matrices are symmetric (which implies commutative).

**Theorem 3.5.** Let `G` be a permutation group with character `π`.

* (a) The coherent configuration of `G` is a commutative association
  scheme iff `π` is multiplicity-free.
* (b) Symmetric iff `π` is multiplicity-free with all irreducible
  constituents of Frobenius–Schur indicator `+1`.

In an association scheme, condition (CC2) is strengthened to:

* (CC2†) The diagonal is a single relation in `𝓡`.

(Renumbering convention: `0, …, r−1` with `R_0` the diagonal.)

**Examples.** Hamming scheme `H(n, q)`, Johnson scheme `J(v, k)`.

**Distance-regular graphs.** A connected graph `Γ` is *distance-regular*
if for each `0 ≤ i ≤ d` (= diameter) there are constants `c_i, a_i, b_i`
such that for `d(x, y) = i`, the number of neighbours of `y` at distance
`i − 1, i, i + 1` from `x` are `c_i, a_i, b_i` respectively.

**Theorem 3.6.**

* (a) A distance-transitive graph is distance-regular.
* (b) A distance-regular graph yields a symmetric association scheme via
  `R_i = {(x, y) : d(x, y) = i}`.

For Moore57 (diameter 2): if it exists, the relations
`{R_0 = Δ_Ω, R_1 = adjacency, R_2 = non-adjacency}` form a symmetric
association scheme (a strongly regular one — §3.5).

[out-of-scope — Moore57's SRG framework gives this structure directly
via `IsSRGWith`; the general association-scheme infrastructure is not
needed for Moore57 non-existence.]
-/

namespace Moore57.Papers.CameronCh3

/-- **Definition: association scheme** (commutative / symmetric variants). [out-of-scope] -/
def IsAssociationScheme : True := trivial

/-- **Theorem 3.5(a) (commutative ⇔ multiplicity-free).** [out-of-scope] -/
theorem theorem3_5a_comm_iff_mult_free : True := by trivial

/-- **Theorem 3.5(b) (symmetric ⇔ all FS index +1).** [out-of-scope] -/
theorem theorem3_5b_symm_iff_fs_pos : True := by trivial

/-- **Theorem 3.6 (distance-regular ⇒ scheme).** [out-of-scope] -/
theorem theorem3_6_distance_regular_scheme : True := by trivial

/-- **Theorem 3.7 (parameter monotonicity, `c_i / b_i` chains).** [out-of-scope] -/
theorem theorem3_7_param_monotonic : True := by trivial

end Moore57.Papers.CameronCh3
