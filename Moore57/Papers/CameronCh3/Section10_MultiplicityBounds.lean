import Moore57.Moore57Graph.Moore57Definition

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Cameron Ch.3 §3.10 — Multiplicity bounds

**Theorem 3.20.** If a primitive `G` has a non-principal real
irreducible constituent with degree `f` and multiplicity 1, then
`|Ω| ≤ (f + s − 1 choose s) + (f + s − 2 choose s − 1)` where `s = r − 1`.

**Theorem 3.21** (Delsarte–Goethals–Seidel). For `A` on the unit sphere
in `ℝ^f` with at most `s` distinct inner products,
`|A| ≤ (f + s − 1 choose s) + (f + s − 2 choose s − 1)`.

**Krein conditions.**
`E_i ∘ E_j = (1/n) Σ_k q_{ij}^k E_k` (Hadamard product); `q_{ij}^k` are
the Krein parameters.

**Theorem 3.22.** Krein parameters of a symmetric association scheme are
real numbers in `[0, 1]`.

[skeleton]
-/

namespace Moore57.Papers.CameronCh3

/-- **Theorem 3.20 (multiplicity bound).** [skeleton] -/
theorem theorem3_20_mult_bound : True := by trivial

/-- **Theorem 3.21 (Delsarte–Goethals–Seidel sphere bound).** [skeleton] -/
theorem theorem3_21_DGS_sphere : True := by trivial

/-- **Theorem 3.22 (Krein parameters in `[0, 1]`).** [skeleton] -/
theorem theorem3_22_krein_in_unit_interval : True := by trivial

end Moore57.Papers.CameronCh3
