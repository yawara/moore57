import Moore57.Moore57Graph.Moore57Definition

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Cameron Ch.3 §3.4 — Algebra of association schemes

The basis algebra (= Bose–Mesner algebra) of an association scheme is
commutative semisimple, hence the basis matrices are simultaneously
diagonalisable. Common eigenspaces `W_0, W_1, …, W_{r−1}` are mutually
orthogonal with `W_0 = ⟨𝟙⟩` (since each `A_i` has constant row/column
sum `n_i = p^0_{ii}`).

Let `E_j` be the orthogonal projection onto `W_j`. Spectral
decomposition: `A_i = Σ_j π_j(A_i) E_j`. Write `π_j(A_i) = P_i(j)` for
`0 ≤ i, j ≤ r − 1`.

**Theorem 3.8 (multiplicities `f_j`).** For common left/right eigenvectors
`u_j, v_j` (normalised at index 0): `f_j = n / Σ_i (u_j)_i (v_j)_i`.

**Theorem 3.9.** The first and second eigenmatrices satisfy
`P Q = Q P = n I`.

**Integrality condition.** The multiplicities `f_j` are positive
integers — a powerful necessary condition on parameters.

**Theorem 3.10 (Frame's condition).**
For a scheme with `n` points, `s` classes, valencies `n_i`, multiplicities
`f_j`, the quantity
`F = n · Π n_i / Π f_j`
is an integer, and a square if all eigenvalues are rational. In
particular `F` is a square if all `f_i` are distinct.

For distance-regular graphs: the minimal polynomial of `A_1` is
`(x − a_d) f_d(x) − b_{d−1} f_{d−1}(x)` where `f_i` are the recurrence
polynomials. Eigenvalues of `A_1` are its roots; idempotents `E` for each
eigenvalue `θ` give multiplicities via `Trace`.

[out-of-scope — replaced by Moore57's explicit E57/E7/EMinus8
spectral decomposition (`Moore57Graph/E7Matrix/SpectralDecomposition`).]
-/

namespace Moore57.Papers.CameronCh3

/-- **Theorem 3.8 (multiplicity formula).** [out-of-scope] -/
theorem theorem3_8_multiplicity_formula : True := by trivial

/-- **Theorem 3.9 (`P Q = Q P = n I`).** [out-of-scope] -/
theorem theorem3_9_PQ_eq_nI : True := by trivial

/-- **Theorem 3.10 (Frame's condition).** [out-of-scope]

The general Frame quantity `F = n · ∏ n_i / ∏ f_j` is integer; for
rational eigenvalues it is a square. -/
theorem theorem3_10_frame_condition : True := by trivial

/-- **Theorem 3.10 (Moore57 instance).**

For Moore57 the Frame quantity is
`F = 3250 · 1 · 57 · 3192 / (1 · 1729 · 1520) = 225 = 15²`.

This is verified by a pure-arithmetic identity
`3250 · 57 · 3192 = 225 · 1729 · 1520`.  The square form `225 = 15²` is
expected because all Moore57 eigenvalues `(57, 7, −8)` are integers
(Cameron's "rational eigenvalues" hypothesis).

The valencies `(n₀, n₁, n₂) = (1, 57, 3192)` are
`1` (self-loop relation), `57` (adjacency), `3192 = 3250 − 1 − 57`
(non-adjacency).  The multiplicities `(f₀, f₁, f₂) = (1, 1729, 1520)`
are the eigenspace dimensions: `1` (trivial), `1729` (eigenvalue `7`),
`1520` (eigenvalue `−8`).  These come from the proven
`Tr(E_57) = 1`, `Tr(E_7) = 1729`, `Tr(E_-8) = 1520`. -/
theorem theorem3_10_frame_condition_moore57 :
    3250 * (1 * 57 * 3192) = 225 * (1 * 1729 * 1520) := by decide

/-- **Theorem 3.10 (Moore57 Frame is a perfect square).** `225 = 15²`. -/
theorem theorem3_10_frame_moore57_is_square :
    (225 : ℕ) = 15 ^ 2 := by decide

end Moore57.Papers.CameronCh3
