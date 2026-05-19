import Moore57.Moore57Graph.Moore57Definition

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Cameron Ch.3 §3.8 — Valency bounds

**Theorem 3.14.** Let `G` be a primitive permutation group of rank `r`,
with `G_a`-orbit of size `k > 1`. Then `n ≤ k((k − 1)^{r−1} − 1)/(k − 2)`
(or `2r − 1` if `k = 2`). The bound is attained by undirected orbital
graphs corresponding to Moore graphs / dihedral groups / Hoffman–Singleton /
Petersen.

**Theorem 3.15** (Bannai–Ito + Damerell). There is no Moore graph with
diameter and valency both greater than 2.

**Theorem 3.16** (equality cases).

* (a) `r = 2`: 2-transitive.
* (b) `k = 2`: dihedral of prime degree.
* (c) `r = 3, k = 3`: `S_5` or `A_5` (degree 10, Petersen).
* (d) `r = 3, k = 7`: `PΣU(3, 5²)` or `PSU(3, 5²)` (degree 50,
  Hoffman–Singleton).

(The would-be `r = 3, k = 57, n = 3250` case is what Cameron §3.7
Theorem 3.13 rules out — already proven downstream as
`MacajSiran2010.S2.cor_lem2_no_vertex_transitive_aut`.)

[out-of-scope — these theorems generalise away from the specific
Moore57 setting; they are not needed for the Moore57 non-existence
chain (Cameron §3.5–3.7 + Higman 1964 §6 suffice).]
-/

namespace Moore57.Papers.CameronCh3

/-- **Theorem 3.14 (valency bound).** [out-of-scope] -/
theorem theorem3_14_valency_bound : True := by trivial

/-- **Theorem 3.15 (Bannai–Ito–Damerell: no Moore graph with diameter > 2
and valency > 2).** [out-of-scope] -/
theorem theorem3_15_no_higher_moore : True := by trivial

/-- **Theorem 3.16 (equality cases of the valency bound).** [out-of-scope] -/
theorem theorem3_16_equality_cases : True := by trivial

end Moore57.Papers.CameronCh3
