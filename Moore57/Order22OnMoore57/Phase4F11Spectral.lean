import Moore57.Order22OnMoore57.Phase3FourCycleBound
import Moore57.Order22OnMoore57.Phase4F11OrbitKernel
import Moore57.Order22OnMoore57.TraceNumber
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.LinearAlgebra.Trace
import Mathlib.LinearAlgebra.Projection
import Mathlib.LinearAlgebra.Semisimple
import Mathlib.LinearAlgebra.Eigenspace.Semisimple
import Mathlib.LinearAlgebra.Eigenspace.Zero
import Mathlib.FieldTheory.Separable

/-!
# Phase 4 F_11 spectral decomposition

Moore57 隣接行列 A の F_11 上スペクトル分解.

## 数値背景

A は ℚ 上の固有値 57, 7, -8 (重複度 1, 1729, 1520).
F_11 上では: 57 ≡ 2, 7 ≡ 7, -8 ≡ 3 (mod 11). 全て distinct.

⟹ V_F_11 = V_2 ⊕ V_7 ⊕ V_3 (eigenspace decomposition).

Lagrange projections (over F_11):
* E_2 = 9 (A - 7I)(A - 3I)  (5⁻¹ = 9 mod 11)
* E_7 = 5 (A - 2I)(A - 3I)  (20⁻¹ = 5 mod 11)
* E_3 = 8 (A - 2I)(A - 7I)  (-4⁻¹ = 8 mod 11)

性質:
* E_λ² = E_λ (idempotent).
* E_λ · E_μ = 0 for λ ≠ μ.
* E_2 + E_7 + E_3 = I.
* A = 2 E_2 + 7 E_7 + 3 E_3.
* dim V_λ = mult of λ in F_11 charpoly (= 1, 1729, 1520 mod 11 同じ).

## σ-equivariance

`A · σ = σ · A` から各 E_λ も σ と可換, V_λ は σ-invariant.

## 戦略 outline

V_λ 内で `(σ|V_λ - I)^{11} = 0` (Frobenius char 11) で nilpotent.
Jordan monotonicity + Step 3.4 analogue で a^{F_11}_λ + 10 k_λ = dim V_λ.

V_2: dim 1, a_2 = 1, k_2 = 0.
V_7: dim 1729, 11 a^{F_11}_7 ≥ 1729 (l_7 ≥ 0 + a^{F_11}_7 ≡ 1729 ≡ 9 mod 10).
V_3: dim 1520, 11 a^{F_11}_3 ≥ 1520 ⟹ a^{F_11}_3 ≥ 140 (mult of 10).

Kernel monotonicity (ℤ → F_11): a_λ ≤ a^{F_11}_λ.
Sum: a_2 + a_7 + a_3 = 300 = a^{F_11}_2 + a^{F_11}_7 + a^{F_11}_3.
⟹ 各 a_λ = a^{F_11}_λ (pigeonhole).

a^{F_11}_3 ≥ 140 + a^{F_11}_7 = 299 - a^{F_11}_3 ≤ 159
⟹ a_7 = a^{F_11}_7 ≤ 159.

Phase 3 candidates a_7 ∈ {159, 169, 179, 189} と組み合わせ a_7 = 159.

## 現状

本ファイルは scaffold. 主要 sorry:
* `a7_le_160_via_F11_spectral_proof`: 上の chain を Lean 化.

実装規模: ~400-500 行 (spectral projections, σ-equivariance, restricted
Jordan, kernel monotonicity, final synthesis).
-/

namespace Moore57

namespace Order22ActsOnMoore57

open Matrix

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-! ## F_11 上の A の cubic equation `(A-2)(A-7)(A-3) = 0`

`IsMoore57.adjMatrix_sq_eq` (over ℚ: A^2 = 56 I - A + J) を F_11 へ reduce.
Mod 11: 56 ≡ 1, so `A^2 = I - A + J` over F_11.

更に `A · J = 57 J ≡ 2 J` から A^3 を計算し,
`(A - 2)(A - 7)(A - 3) = A^3 + 10 A^2 + 8 A + 2 I = 0` (mod 11) を得る. -/

/-- F_11 上の全 1 行列. -/
noncomputable def allOnesMatrixF11 (V : Type*) : Matrix V V (ZMod 11) :=
  Matrix.of fun _ _ => (1 : ZMod 11)

/-- F_11 上 `A^2 = I - A + J` (Moore57 + char 11; 56 ≡ 1 mod 11). -/
theorem adjMatrixF11_sq_eq (hΓ : IsMoore57 Γ) :
    adjMatrixF11 Γ ^ 2 = (1 : Matrix V V (ZMod 11)) - adjMatrixF11 Γ +
      allOnesMatrixF11 V := by
  classical
  unfold adjMatrixF11 allOnesMatrixF11
  have h_srg : Γ.adjMatrix (ZMod 11) ^ 2 =
      (57 : ℕ) • (1 : Matrix V V (ZMod 11)) +
      (0 : ℕ) • Γ.adjMatrix (ZMod 11) +
      (1 : ℕ) • Γᶜ.adjMatrix (ZMod 11) := hΓ.matrix_eq
  rw [h_srg]
  ext v w
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply,
    SimpleGraph.adjMatrix_apply, SimpleGraph.compl_adj, Matrix.one_apply,
    Matrix.of_apply]
  by_cases hvw : v = w
  · subst w
    simp
    decide
  · by_cases hadj : Γ.Adj v w
    · simp [hvw, hadj]
    · simp [hvw, hadj]

/-- F_11 上 `A · J = 2 J` (regularity 57 ≡ 2 mod 11). -/
theorem adjMatrixF11_mul_allOnes (hΓ : IsMoore57 Γ) :
    adjMatrixF11 Γ * allOnesMatrixF11 V = (2 : ZMod 11) • allOnesMatrixF11 V := by
  classical
  ext v w
  unfold adjMatrixF11 allOnesMatrixF11
  rw [SimpleGraph.adjMatrix_mul_apply]
  simp only [Matrix.of_apply, Matrix.smul_apply, smul_eq_mul, mul_one]
  rw [Finset.sum_const, nsmul_eq_mul, mul_one,
      SimpleGraph.card_neighborFinset_eq_degree, hΓ.regular v]
  decide

/-- F_11 上 `J · A = 2 J` (regularity の双対形). -/
theorem allOnes_mul_adjMatrixF11 (hΓ : IsMoore57 Γ) :
    allOnesMatrixF11 V * adjMatrixF11 Γ = (2 : ZMod 11) • allOnesMatrixF11 V := by
  classical
  ext v w
  unfold adjMatrixF11 allOnesMatrixF11
  rw [SimpleGraph.mul_adjMatrix_apply]
  simp only [Matrix.of_apply, Matrix.smul_apply, smul_eq_mul, mul_one]
  rw [Finset.sum_const, nsmul_eq_mul, mul_one,
      SimpleGraph.card_neighborFinset_eq_degree, hΓ.regular w]
  decide

/-- F_11 上 `J · J = 5 J` (|V| = 3250 ≡ 5 mod 11). -/
theorem allOnes_mul_allOnes (hΓ : IsMoore57 Γ) :
    allOnesMatrixF11 V * allOnesMatrixF11 V = (5 : ZMod 11) • allOnesMatrixF11 V := by
  classical
  ext v w
  unfold allOnesMatrixF11
  rw [Matrix.mul_apply]
  simp only [Matrix.of_apply, Matrix.smul_apply, smul_eq_mul, mul_one]
  rw [Finset.sum_const, nsmul_eq_mul, mul_one, Finset.card_univ, hΓ.card]
  decide

/-- F_11 上 `(A - 2 I)(A - 7 I)(A - 3 I) = 0` (Q charpoly mod 11 factorization).

戦略: `match_scalars` で matrix 方程式を A, 1, J の係数比較に還元し,
ZMod 11 数値計算は `decide` で閉じる. -/
theorem adjMatrixF11_cubic_eq_zero (hΓ : IsMoore57 Γ) :
    (adjMatrixF11 Γ - (2 : ZMod 11) • 1) *
    (adjMatrixF11 Γ - (7 : ZMod 11) • 1) *
    (adjMatrixF11 Γ - (3 : ZMod 11) • 1) = 0 := by
  classical
  set A := adjMatrixF11 Γ with hAdef
  set J := allOnesMatrixF11 V with hJdef
  have hsq : A * A = 1 - A + J := by
    rw [show A * A = A ^ 2 from (sq A).symm, adjMatrixF11_sq_eq hΓ]
  have hAJ : A * J = (2 : ZMod 11) • J := adjMatrixF11_mul_allOnes hΓ
  have hJA : J * A = (2 : ZMod 11) • J := allOnes_mul_adjMatrixF11 hΓ
  -- Stage 1: A * (A * A) = 2•A - 1 + J を計算
  have hA_AA : A * (A * A) = (2 : ZMod 11) • A - 1 + J := by
    rw [hsq, mul_add, mul_sub, mul_one, hAJ, hsq]
    match_scalars <;> decide
  -- Stage 2: (A - 2•1)(A - 7•1) を展開, A*A を hsq で消す.
  -- LHS = A*A - 7•A - 2•A + 14•1 = (1 - A + J) - 7•A - 2•A + 14•1
  -- ZMod 11 で 4•1 + A + J になる
  have hMN : (A - (2 : ZMod 11) • 1) * (A - (7 : ZMod 11) • 1) =
      (4 : ZMod 11) • (1 : Matrix V V (ZMod 11)) + A + J := by
    rw [sub_mul, mul_sub, mul_sub,
        show A * ((7 : ZMod 11) • (1 : Matrix V V (ZMod 11))) = (7 : ZMod 11) • A from by
          rw [mul_smul_comm, mul_one],
        show ((2 : ZMod 11) • (1 : Matrix V V (ZMod 11))) * A = (2 : ZMod 11) • A from by
          rw [smul_mul_assoc, one_mul],
        show ((2 : ZMod 11) • (1 : Matrix V V (ZMod 11))) * ((7 : ZMod 11) • 1)
            = ((2 : ZMod 11) * 7) • (1 : Matrix V V (ZMod 11)) from by
          rw [smul_mul_assoc, one_mul, smul_smul],
        hsq]
    match_scalars <;> decide
  -- Stage 3: (4•1 + A + J)(A - 3•1) = 0
  -- LHS = 4•A - 12•1 + A*A - 3•A + J*A - 3•J
  --     = 4•A - 12•1 + (1 - A + J) - 3•A + 2•J - 3•J
  --     = (4 - 1 - 3)•A + (-12 + 1)•1 + (1 + 2 - 3)•J
  --     = 0•A + (-11)•1 + 0•J = 0 in ZMod 11
  rw [hMN, add_mul, add_mul, mul_sub, mul_sub, mul_sub,
      show ((4 : ZMod 11) • (1 : Matrix V V (ZMod 11))) * A = (4 : ZMod 11) • A from by
        rw [smul_mul_assoc, one_mul],
      show ((4 : ZMod 11) • (1 : Matrix V V (ZMod 11))) * ((3 : ZMod 11) • 1)
          = ((4 : ZMod 11) * 3) • (1 : Matrix V V (ZMod 11)) from by
        rw [smul_mul_assoc, one_mul, smul_smul],
      show A * ((3 : ZMod 11) • (1 : Matrix V V (ZMod 11))) = (3 : ZMod 11) • A from by
        rw [mul_smul_comm, mul_one],
      show J * ((3 : ZMod 11) • (1 : Matrix V V (ZMod 11))) = (3 : ZMod 11) • J from by
        rw [mul_smul_comm, mul_one],
      hsq, hJA]
  match_scalars <;> decide

/-! ## F_11 spectral projections (Lagrange interpolation) -/

/-- F_11 上の E_2 = 9 (A - 7I)(A - 3I). -/
noncomputable def E2MatrixF11 (Γ : SimpleGraph V) [DecidableRel Γ.Adj] :
    Matrix V V (ZMod 11) :=
  (9 : ZMod 11) • ((adjMatrixF11 Γ - (7 : ZMod 11) • 1) *
                   (adjMatrixF11 Γ - (3 : ZMod 11) • 1))

/-- F_11 上の E_7 = 5 (A - 2I)(A - 3I). -/
noncomputable def E7MatrixF11 (Γ : SimpleGraph V) [DecidableRel Γ.Adj] :
    Matrix V V (ZMod 11) :=
  (5 : ZMod 11) • ((adjMatrixF11 Γ - (2 : ZMod 11) • 1) *
                   (adjMatrixF11 Γ - (3 : ZMod 11) • 1))

/-- F_11 上の E_3 = 8 (A - 2I)(A - 7I). -/
noncomputable def E3MatrixF11 (Γ : SimpleGraph V) [DecidableRel Γ.Adj] :
    Matrix V V (ZMod 11) :=
  (8 : ZMod 11) • ((adjMatrixF11 Γ - (2 : ZMod 11) • 1) *
                   (adjMatrixF11 Γ - (7 : ZMod 11) • 1))

/-! ## E_λ algebraic identities -/

/-- E_2 + E_7 + E_3 = I (Lagrange completeness over F_11).

多項式 `9 (X - 7)(X - 3) + 5 (X - 2)(X - 3) + 8 (X - 2)(X - 7) = 1` の
F_11 [X] 上の等式が, X = A の matrix algebra 評価で恒等的に成り立つ.
hsq 不要 (純粋多項式恒等式). -/
theorem ELambda_sum_eq_one :
    E2MatrixF11 Γ + E7MatrixF11 Γ + E3MatrixF11 Γ = 1 := by
  classical
  unfold E2MatrixF11 E7MatrixF11 E3MatrixF11
  set A := adjMatrixF11 Γ
  simp only [sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, smul_smul, one_mul, mul_one,
             smul_sub]
  match_scalars <;> decide

/-- `A = 2 E_2 + 7 E_7 + 3 E_3` (eigenvalue decomposition over F_11).

多項式 `2·9(X-7)(X-3) + 7·5(X-2)(X-3) + 3·8(X-2)(X-7) = X` の F_11 [X] 上恒等式.
hsq 不要. -/
theorem ELambda_decomp_A :
    (2 : ZMod 11) • E2MatrixF11 Γ + (7 : ZMod 11) • E7MatrixF11 Γ
      + (3 : ZMod 11) • E3MatrixF11 Γ = adjMatrixF11 Γ := by
  classical
  unfold E2MatrixF11 E7MatrixF11 E3MatrixF11
  set A := adjMatrixF11 Γ
  simp only [sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, smul_smul, one_mul, mul_one,
             smul_sub]
  match_scalars <;> decide

/-- F_11 上 `E_2 = 9 J` (V_2 は constant vector subspace = span J の 1 次元).

実は (A - 7)(A - 3) = A^2 - 10 A + 21 を hsq で展開すると 22 - 11 A + J = J (mod 11).
よって E_2 = 9 (A - 7)(A - 3) = 9 J. -/
theorem E2_eq_nine_smul_allOnes (hΓ : IsMoore57 Γ) :
    E2MatrixF11 Γ = (9 : ZMod 11) • allOnesMatrixF11 V := by
  classical
  unfold E2MatrixF11
  set A := adjMatrixF11 Γ
  set J := allOnesMatrixF11 V
  have hsq : A * A = 1 - A + J := by
    rw [show A * A = A ^ 2 from (sq A).symm, adjMatrixF11_sq_eq hΓ]
  simp only [sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, smul_smul, one_mul, mul_one,
             smul_sub]
  rw [hsq]
  match_scalars <;> decide

/-- F_11 上 E_2 が idempotent: `E_2 · E_2 = E_2`.

E_2 = 9 J + J · J = 5 J ⟹ E_2 · E_2 = 81 · J · J = 81 · 5 J = 405 J = 9 J = E_2 (mod 11). -/
theorem E2_idempotent (hΓ : IsMoore57 Γ) :
    E2MatrixF11 Γ * E2MatrixF11 Γ = E2MatrixF11 Γ := by
  classical
  rw [E2_eq_nine_smul_allOnes hΓ, smul_mul_assoc, mul_smul_comm,
      allOnes_mul_allOnes hΓ, smul_smul, smul_smul,
      show ((9 : ZMod 11) * 9 * 5) = 9 from by decide]

/-- F_11 上 `J · (A - 2 • I) = 0`: 固有値 2 のため J が右から (A - 2I) を消す. -/
theorem allOnes_mul_A_sub_two (hΓ : IsMoore57 Γ) :
    allOnesMatrixF11 V * (adjMatrixF11 Γ - (2 : ZMod 11) • 1) = 0 := by
  rw [mul_sub, allOnes_mul_adjMatrixF11 hΓ, mul_smul_comm, mul_one, sub_self]

/-- F_11 上 `(A - 2 • I) · J = 0` (双対形). -/
theorem A_sub_two_mul_allOnes (hΓ : IsMoore57 Γ) :
    (adjMatrixF11 Γ - (2 : ZMod 11) • 1) * allOnesMatrixF11 V = 0 := by
  rw [sub_mul, adjMatrixF11_mul_allOnes hΓ, smul_mul_assoc, one_mul, sub_self]

/-- Orthogonality: `E_2 · E_7 = 0`.

E_2 = 9 J, E_7 = 5 (A - 2)(A - 3). J · (A - 2) = 0 から E_2 · E_7 = 0. -/
theorem E2_mul_E7_eq_zero (hΓ : IsMoore57 Γ) :
    E2MatrixF11 Γ * E7MatrixF11 Γ = 0 := by
  classical
  rw [E2_eq_nine_smul_allOnes hΓ]
  unfold E7MatrixF11
  rw [smul_mul_assoc, mul_smul_comm, smul_smul, ← mul_assoc,
      allOnes_mul_A_sub_two hΓ, zero_mul, smul_zero]

/-- Orthogonality: `E_2 · E_3 = 0`. -/
theorem E2_mul_E3_eq_zero (hΓ : IsMoore57 Γ) :
    E2MatrixF11 Γ * E3MatrixF11 Γ = 0 := by
  classical
  rw [E2_eq_nine_smul_allOnes hΓ]
  unfold E3MatrixF11
  rw [smul_mul_assoc, mul_smul_comm, smul_smul, ← mul_assoc,
      allOnes_mul_A_sub_two hΓ, zero_mul, smul_zero]

/-- Orthogonality: `E_7 · E_2 = 0`.

(A - 3) · J = -J ⟹ (A - 2)(A - 3) · J = (A - 2)(-J) = -((A - 2) · J) = 0. -/
theorem E7_mul_E2_eq_zero (hΓ : IsMoore57 Γ) :
    E7MatrixF11 Γ * E2MatrixF11 Γ = 0 := by
  classical
  rw [E2_eq_nine_smul_allOnes hΓ]
  unfold E7MatrixF11
  rw [smul_mul_assoc, mul_smul_comm, smul_smul, mul_assoc]
  have h1 : (adjMatrixF11 Γ - (3 : ZMod 11) • 1) * allOnesMatrixF11 V
          = ((2 : ZMod 11) - 3) • allOnesMatrixF11 V := by
    rw [sub_mul, adjMatrixF11_mul_allOnes hΓ, smul_mul_assoc, one_mul, ← sub_smul]
  rw [h1, mul_smul_comm, A_sub_two_mul_allOnes hΓ, smul_zero, smul_zero]

/-- Orthogonality: `E_3 · E_2 = 0`.

(A - 7) · J = -5 J ⟹ (A - 2)(A - 7) · J = (A - 2)(-5 J) = -5 · ((A - 2) · J) = 0. -/
theorem E3_mul_E2_eq_zero (hΓ : IsMoore57 Γ) :
    E3MatrixF11 Γ * E2MatrixF11 Γ = 0 := by
  classical
  rw [E2_eq_nine_smul_allOnes hΓ]
  unfold E3MatrixF11
  rw [smul_mul_assoc, mul_smul_comm, smul_smul, mul_assoc]
  have h1 : (adjMatrixF11 Γ - (7 : ZMod 11) • 1) * allOnesMatrixF11 V
          = ((2 : ZMod 11) - 7) • allOnesMatrixF11 V := by
    rw [sub_mul, adjMatrixF11_mul_allOnes hΓ, smul_mul_assoc, one_mul, ← sub_smul]
  rw [h1, mul_smul_comm, A_sub_two_mul_allOnes hΓ, smul_zero, smul_zero]

/-- F_11 上 `E_7 = 2 • 1 + 3 • A + 5 • J` (closed form). -/
theorem E7_eq_closed (hΓ : IsMoore57 Γ) :
    E7MatrixF11 Γ = (2 : ZMod 11) • (1 : Matrix V V (ZMod 11))
        + (3 : ZMod 11) • adjMatrixF11 Γ + (5 : ZMod 11) • allOnesMatrixF11 V := by
  classical
  unfold E7MatrixF11
  set A := adjMatrixF11 Γ
  set J := allOnesMatrixF11 V
  have hsq : A * A = 1 - A + J := by
    rw [show A * A = A ^ 2 from (sq A).symm, adjMatrixF11_sq_eq hΓ]
  simp only [sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, smul_smul, one_mul, mul_one,
             smul_sub]
  rw [hsq]
  match_scalars <;> decide

/-- F_11 上 `E_3 = 10 • 1 + 8 • A + 8 • J` (closed form). -/
theorem E3_eq_closed (hΓ : IsMoore57 Γ) :
    E3MatrixF11 Γ = (10 : ZMod 11) • (1 : Matrix V V (ZMod 11))
        + (8 : ZMod 11) • adjMatrixF11 Γ + (8 : ZMod 11) • allOnesMatrixF11 V := by
  classical
  unfold E3MatrixF11
  set A := adjMatrixF11 Γ
  set J := allOnesMatrixF11 V
  have hsq : A * A = 1 - A + J := by
    rw [show A * A = A ^ 2 from (sq A).symm, adjMatrixF11_sq_eq hΓ]
  simp only [sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, smul_smul, one_mul, mul_one,
             smul_sub]
  rw [hsq]
  match_scalars <;> decide

/-- F_11 上 E_7 idempotent: `E_7 · E_7 = E_7`. -/
theorem E7_idempotent (hΓ : IsMoore57 Γ) :
    E7MatrixF11 Γ * E7MatrixF11 Γ = E7MatrixF11 Γ := by
  classical
  rw [E7_eq_closed hΓ]
  set A := adjMatrixF11 Γ
  set J := allOnesMatrixF11 V
  have hsq : A * A = 1 - A + J := by
    rw [show A * A = A ^ 2 from (sq A).symm, adjMatrixF11_sq_eq hΓ]
  have hAJ : A * J = (2 : ZMod 11) • J := adjMatrixF11_mul_allOnes hΓ
  have hJA : J * A = (2 : ZMod 11) • J := allOnes_mul_adjMatrixF11 hΓ
  have hJJ : J * J = (5 : ZMod 11) • J := allOnes_mul_allOnes hΓ
  simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, smul_smul, one_mul, mul_one]
  rw [hsq, hAJ, hJA, hJJ]
  match_scalars <;> decide

/-- F_11 上 E_3 idempotent: `E_3 · E_3 = E_3`. -/
theorem E3_idempotent (hΓ : IsMoore57 Γ) :
    E3MatrixF11 Γ * E3MatrixF11 Γ = E3MatrixF11 Γ := by
  classical
  rw [E3_eq_closed hΓ]
  set A := adjMatrixF11 Γ
  set J := allOnesMatrixF11 V
  have hsq : A * A = 1 - A + J := by
    rw [show A * A = A ^ 2 from (sq A).symm, adjMatrixF11_sq_eq hΓ]
  have hAJ : A * J = (2 : ZMod 11) • J := adjMatrixF11_mul_allOnes hΓ
  have hJA : J * A = (2 : ZMod 11) • J := allOnes_mul_adjMatrixF11 hΓ
  have hJJ : J * J = (5 : ZMod 11) • J := allOnes_mul_allOnes hΓ
  simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, smul_smul, one_mul, mul_one]
  rw [hsq, hAJ, hJA, hJJ]
  match_scalars <;> decide

/-- Orthogonality: `E_7 · E_3 = 0`. -/
theorem E7_mul_E3_eq_zero (hΓ : IsMoore57 Γ) :
    E7MatrixF11 Γ * E3MatrixF11 Γ = 0 := by
  classical
  rw [E7_eq_closed hΓ, E3_eq_closed hΓ]
  set A := adjMatrixF11 Γ
  set J := allOnesMatrixF11 V
  have hsq : A * A = 1 - A + J := by
    rw [show A * A = A ^ 2 from (sq A).symm, adjMatrixF11_sq_eq hΓ]
  have hAJ : A * J = (2 : ZMod 11) • J := adjMatrixF11_mul_allOnes hΓ
  have hJA : J * A = (2 : ZMod 11) • J := allOnes_mul_adjMatrixF11 hΓ
  have hJJ : J * J = (5 : ZMod 11) • J := allOnes_mul_allOnes hΓ
  simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, smul_smul, one_mul, mul_one]
  rw [hsq, hAJ, hJA, hJJ]
  match_scalars <;> decide

/-- Orthogonality: `E_3 · E_7 = 0`. -/
theorem E3_mul_E7_eq_zero (hΓ : IsMoore57 Γ) :
    E3MatrixF11 Γ * E7MatrixF11 Γ = 0 := by
  classical
  rw [E7_eq_closed hΓ, E3_eq_closed hΓ]
  set A := adjMatrixF11 Γ
  set J := allOnesMatrixF11 V
  have hsq : A * A = 1 - A + J := by
    rw [show A * A = A ^ 2 from (sq A).symm, adjMatrixF11_sq_eq hΓ]
  have hAJ : A * J = (2 : ZMod 11) • J := adjMatrixF11_mul_allOnes hΓ
  have hJA : J * A = (2 : ZMod 11) • J := allOnes_mul_adjMatrixF11 hΓ
  have hJJ : J * J = (5 : ZMod 11) • J := allOnes_mul_allOnes hΓ
  simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, smul_smul, one_mul, mul_one]
  rw [hsq, hAJ, hJA, hJJ]
  match_scalars <;> decide

/-! ## σ-equivariance of E_λ -/

/-- F_11 上 `P_σ · J = J`: 置換行列が全 1 行列を保つ. -/
theorem permMatrixF11_mul_allOnes (σ : Equiv.Perm V) :
    permMatrixF11 σ * allOnesMatrixF11 V = allOnesMatrixF11 V := by
  classical
  ext v w
  unfold allOnesMatrixF11
  rw [permMatrixF11_mul_apply]
  simp [Matrix.of_apply]

/-- F_11 上 `J · P_σ = J` (双対形). -/
theorem allOnes_mul_permMatrixF11 (σ : Equiv.Perm V) :
    allOnesMatrixF11 V * permMatrixF11 σ = allOnesMatrixF11 V := by
  classical
  ext v w
  unfold allOnesMatrixF11
  rw [mul_permMatrixF11_apply]
  simp [Matrix.of_apply]

/-- F_11 上 `E_2` が σ と可換. E_2 = 9 J, J commutes with P_σ. -/
theorem E2_commute_permMatrixF11 (hΓ : IsMoore57 Γ) (σ : Equiv.Perm V) :
    E2MatrixF11 Γ * permMatrixF11 σ = permMatrixF11 σ * E2MatrixF11 Γ := by
  classical
  rw [E2_eq_nine_smul_allOnes hΓ, smul_mul_assoc, mul_smul_comm,
      allOnes_mul_permMatrixF11, permMatrixF11_mul_allOnes]

/-- F_11 上 `E_7` が σ と可換. closed form 経由. -/
theorem E7_commute_permMatrixF11 (hΓ : IsMoore57 Γ)
    (σ : Equiv.Perm V) (hσ : ∀ v w : V, Γ.Adj v w ↔ Γ.Adj (σ v) (σ w)) :
    E7MatrixF11 Γ * permMatrixF11 σ = permMatrixF11 σ * E7MatrixF11 Γ := by
  classical
  rw [E7_eq_closed hΓ]
  rw [add_mul, add_mul, mul_add, mul_add, smul_mul_assoc, smul_mul_assoc, smul_mul_assoc,
      mul_smul_comm, mul_smul_comm, mul_smul_comm,
      adjMatrixF11_mul_permMatrixF11_eq_permMatrixF11_mul_adjMatrixF11 Γ σ hσ,
      one_mul, mul_one, permMatrixF11_mul_allOnes, allOnes_mul_permMatrixF11]

/-- F_11 上 `E_3` が σ と可換. -/
theorem E3_commute_permMatrixF11 (hΓ : IsMoore57 Γ)
    (σ : Equiv.Perm V) (hσ : ∀ v w : V, Γ.Adj v w ↔ Γ.Adj (σ v) (σ w)) :
    E3MatrixF11 Γ * permMatrixF11 σ = permMatrixF11 σ * E3MatrixF11 Γ := by
  classical
  rw [E3_eq_closed hΓ]
  rw [add_mul, add_mul, mul_add, mul_add, smul_mul_assoc, smul_mul_assoc, smul_mul_assoc,
      mul_smul_comm, mul_smul_comm, mul_smul_comm,
      adjMatrixF11_mul_permMatrixF11_eq_permMatrixF11_mul_adjMatrixF11 Γ σ hσ,
      one_mul, mul_one, permMatrixF11_mul_allOnes, allOnes_mul_permMatrixF11]

/-! ## Phase D-C: σ-trace computations over F_11

`trace(E_λ · P_σ)` over F_11 を closed forms 経由で計算.
結果: (1, 2, 2). Krull-Schmidt 構造 (Phase D-B 完成後) 経由で
これらが `l_λ + 11 k_λ ≡ l_λ (mod 11) = dim V_λ mod 11` であることが分かる.

要素別の helper:
- `trace(P_σ) = fixedVertexCount σ` (over F_11): #Fix σ.
- `trace(A · P_σ) = adjacentMovedCount Γ σ` (over F_11): T_1 mod 11 = 0.
- `trace(J · P_σ) = |V|` (over F_11): 3250 mod 11 = 5.
-/

/-- F_11 上 `trace(P_σ) = fixedVertexCount σ`. -/
theorem trace_permMatrixF11_eq_fixedVertexCount (σ : Equiv.Perm V) :
    Matrix.trace (permMatrixF11 σ) = (Moore57.fixedVertexCount σ : ZMod 11) := by
  classical
  rw [Matrix.trace]
  calc
    ∑ v : V, Matrix.diag (permMatrixF11 σ) v
        = ∑ v : V, if σ v = v then (1 : ZMod 11) else 0 := by
          refine Finset.sum_congr rfl ?_
          intro v _
          have h := mul_permMatrixF11_apply (M := (1 : Matrix V V (ZMod 11))) σ v v
          simpa [Matrix.diag, Matrix.one_mul, Matrix.one_apply, eq_comm] using h
    _ = (Moore57.fixedVertexCount σ : ZMod 11) := by
          simp [Moore57.fixedVertexCount]

/-- F_11 上 `trace(A · P_σ) = adjacentMovedCount Γ σ`. -/
theorem trace_adjMatrixF11_mul_permMatrixF11_eq_adjacentMovedCount
    (Γ : SimpleGraph V) [DecidableRel Γ.Adj] (σ : Equiv.Perm V) :
    Matrix.trace (adjMatrixF11 Γ * permMatrixF11 σ) =
      (Moore57.adjacentMovedCount Γ σ : ZMod 11) := by
  classical
  rw [Matrix.trace]
  calc
    ∑ v : V, Matrix.diag (adjMatrixF11 Γ * permMatrixF11 σ) v
        = ∑ v : V, if Γ.Adj v (σ v) then (1 : ZMod 11) else 0 := by
          refine Finset.sum_congr rfl ?_
          intro v _
          change (adjMatrixF11 Γ * permMatrixF11 σ) v v =
            if Γ.Adj v (σ v) then (1 : ZMod 11) else 0
          rw [mul_permMatrixF11_apply]
          unfold adjMatrixF11
          rw [SimpleGraph.adjMatrix_apply]
    _ = (Moore57.adjacentMovedCount Γ σ : ZMod 11) := by
          simp [Moore57.adjacentMovedCount]

/-- F_11 上 `trace(J · P_σ) = |V|`. -/
theorem trace_allOnesMatrixF11_mul_permMatrixF11
    (σ : Equiv.Perm V) :
    Matrix.trace (allOnesMatrixF11 V * permMatrixF11 σ) =
      (Fintype.card V : ZMod 11) := by
  classical
  rw [Matrix.trace]
  calc
    ∑ v : V, Matrix.diag (allOnesMatrixF11 V * permMatrixF11 σ) v
        = ∑ _v : V, (1 : ZMod 11) := by
          refine Finset.sum_congr rfl ?_
          intro v _
          change (allOnesMatrixF11 V * permMatrixF11 σ) v v = 1
          rw [allOnes_mul_permMatrixF11]
          unfold allOnesMatrixF11
          simp [Matrix.of_apply]
    _ = (Fintype.card V : ZMod 11) := by
          rw [Finset.sum_const, Finset.card_univ]
          simp

/-! ### σ-trace specializations to Order22 -/

/-- F_11 上 `trace(P_σ) = 5` (since #Fix σ = 5 by `σ_fix`). -/
theorem trace_permMatrixF11_σ_eq_five (h : Order22ActsOnMoore57 V Γ) :
    Matrix.trace (permMatrixF11 h.σ) = (5 : ZMod 11) := by
  rw [trace_permMatrixF11_eq_fixedVertexCount, h.fixedVertexCount_σ_eq_five]
  rfl

/-- F_11 上 `trace(A · P_σ) = 0` (since T_1 = 11n ≡ 0 mod 11). -/
theorem trace_adjMatrixF11_mul_permMatrixF11_σ_eq_zero
    (h : Order22ActsOnMoore57 V Γ) :
    Matrix.trace (adjMatrixF11 Γ * permMatrixF11 h.σ) = (0 : ZMod 11) := by
  rw [trace_adjMatrixF11_mul_permMatrixF11_eq_adjacentMovedCount]
  -- adjacentMovedCount Γ σ = T_1 = 11 * traceNumber.
  have h_T1 : Moore57.adjacentMovedCount Γ h.σ = 11 * h.traceNumber := by
    show (Finset.univ.filter (fun v : V => Γ.Adj v (h.σ v))).card = 11 * h.traceNumber
    have h_Tk1 : h.Tk 1 = 11 * h.traceNumber :=
      h.Tk_eq_eleven_mul_traceNumber (le_refl _) (by omega)
    have h_Tk_def : h.Tk 1 = (Finset.univ.filter (fun x : V => Γ.Adj x ((h.σ ^ 1) x))).card := rfl
    rw [pow_one] at h_Tk_def
    rw [← h_Tk_def, h_Tk1]
  rw [h_T1]
  push_cast
  rw [show (11 : ZMod 11) = 0 from by decide]
  ring

/-- F_11 上 `trace(J · P_σ) = 5` (|V| = 3250 ≡ 5 mod 11). -/
theorem trace_allOnesMatrixF11_mul_permMatrixF11_σ_eq_five
    (h : Order22ActsOnMoore57 V Γ) :
    Matrix.trace (allOnesMatrixF11 V * permMatrixF11 h.σ) = (5 : ZMod 11) := by
  rw [trace_allOnesMatrixF11_mul_permMatrixF11, h.isMoore.card]
  decide

/-! ### trace(E_λ · P_σ) over F_11 -/

/-- F_11 上 `trace(E_2 · P_σ) = 1`. E_2 = 9·J ⟹ trace = 9·5 = 1. -/
theorem trace_E2MatrixF11_mul_permMatrixF11_σ_eq_one
    (h : Order22ActsOnMoore57 V Γ) :
    Matrix.trace (E2MatrixF11 Γ * permMatrixF11 h.σ) = (1 : ZMod 11) := by
  rw [E2_eq_nine_smul_allOnes h.isMoore, Matrix.smul_mul, Matrix.trace_smul,
      trace_allOnesMatrixF11_mul_permMatrixF11_σ_eq_five h]
  decide

/-- F_11 上 `trace(E_7 · P_σ) = 2`. E_7 = 2·I + 3·A + 5·J ⟹ trace = 2·5 + 3·0 + 5·5 = 2 mod 11. -/
theorem trace_E7MatrixF11_mul_permMatrixF11_σ_eq_two
    (h : Order22ActsOnMoore57 V Γ) :
    Matrix.trace (E7MatrixF11 Γ * permMatrixF11 h.σ) = (2 : ZMod 11) := by
  rw [E7_eq_closed h.isMoore]
  rw [add_mul, add_mul, smul_mul_assoc, smul_mul_assoc, smul_mul_assoc, one_mul]
  rw [Matrix.trace_add, Matrix.trace_add, Matrix.trace_smul, Matrix.trace_smul,
      Matrix.trace_smul]
  rw [trace_permMatrixF11_σ_eq_five h,
      trace_adjMatrixF11_mul_permMatrixF11_σ_eq_zero h,
      trace_allOnesMatrixF11_mul_permMatrixF11_σ_eq_five h]
  decide

/-- F_11 上 `trace(E_3 · P_σ) = 2`. E_3 = 10·I + 8·A + 8·J ⟹ trace = 10·5 + 8·0 + 8·5 = 2 mod 11. -/
theorem trace_E3MatrixF11_mul_permMatrixF11_σ_eq_two
    (h : Order22ActsOnMoore57 V Γ) :
    Matrix.trace (E3MatrixF11 Γ * permMatrixF11 h.σ) = (2 : ZMod 11) := by
  rw [E3_eq_closed h.isMoore]
  rw [add_mul, add_mul, smul_mul_assoc, smul_mul_assoc, smul_mul_assoc, one_mul]
  rw [Matrix.trace_add, Matrix.trace_add, Matrix.trace_smul, Matrix.trace_smul,
      Matrix.trace_smul]
  rw [trace_permMatrixF11_σ_eq_five h,
      trace_adjMatrixF11_mul_permMatrixF11_σ_eq_zero h,
      trace_allOnesMatrixF11_mul_permMatrixF11_σ_eq_five h]
  decide

/-! ## F_11 modular rep theory: V_λ 部分空間 -/

/-- F_11 上の `V_2 := range E_2`. -/
noncomputable def V2Submodule (Γ : SimpleGraph V) [DecidableRel Γ.Adj] :
    Submodule (ZMod 11) (V → ZMod 11) :=
  (E2MatrixF11 Γ).toLin'.range

/-- F_11 上の `V_7 := range E_7`. -/
noncomputable def V7Submodule (Γ : SimpleGraph V) [DecidableRel Γ.Adj] :
    Submodule (ZMod 11) (V → ZMod 11) :=
  (E7MatrixF11 Γ).toLin'.range

/-- F_11 上の `V_3 := range E_3`. -/
noncomputable def V3Submodule (Γ : SimpleGraph V) [DecidableRel Γ.Adj] :
    Submodule (ZMod 11) (V → ZMod 11) :=
  (E3MatrixF11 Γ).toLin'.range

/-! ### Step 1: V_2 ⊆ ker(T_F11), V_2 σ-fixed -/

/-- `P_σ · E_2 = E_2`: E_2 = 9·J で J は σ で不変. -/
theorem permMatrixF11_mul_E2_eq_E2 (hΓ : IsMoore57 Γ) (σ : Equiv.Perm V) :
    permMatrixF11 σ * E2MatrixF11 Γ = E2MatrixF11 Γ := by
  rw [E2_eq_nine_smul_allOnes hΓ, mul_smul_comm, permMatrixF11_mul_allOnes]

/-- `V_2 ⊆ ker(T_F11)`: V_2 = span(1_V) は σ-fixed. -/
theorem V2Submodule_le_ker_T_F11 (h : Order22ActsOnMoore57 V Γ) :
    V2Submodule Γ ≤ LinearMap.ker (T_F11 h) := by
  classical
  intro f hf
  rw [V2Submodule, LinearMap.mem_range] at hf
  obtain ⟨g, hg⟩ := hf
  rw [LinearMap.mem_ker, T_F11_def, ← hg]
  -- Goal: ((P_σ - 1).toLin') ((E_2).toLin' g) = 0
  have h_mat : (permMatrixF11 h.σ - 1) * E2MatrixF11 Γ = 0 := by
    rw [sub_mul, one_mul, permMatrixF11_mul_E2_eq_E2 h.isMoore, sub_self]
  show ((permMatrixF11 h.σ - 1 : Matrix V V (ZMod 11)).toLin')
       ((E2MatrixF11 Γ).toLin' g) = 0
  rw [show ((permMatrixF11 h.σ - 1 : Matrix V V (ZMod 11)).toLin')
        ((E2MatrixF11 Γ).toLin' g) =
      ((permMatrixF11 h.σ - 1 : Matrix V V (ZMod 11)) * E2MatrixF11 Γ).toLin' g from by
        rw [Matrix.toLin'_mul]; rfl]
  rw [h_mat]
  simp

/-- `a^{F_11}_2 := dim(V_2 ∩ ker(T_F11))`.
V_2 ⊆ ker(T_F11) より = dim V_2. -/
theorem aF11_lambda_two_eq_dim_V2 (h : Order22ActsOnMoore57 V Γ) :
    Module.finrank (ZMod 11)
        (V2Submodule Γ ⊓ LinearMap.ker (T_F11 h) :
          Submodule (ZMod 11) (V → ZMod 11)) =
      Module.finrank (ZMod 11) (V2Submodule Γ) := by
  classical
  have h_eq : (V2Submodule Γ ⊓ LinearMap.ker (T_F11 h) :
                Submodule (ZMod 11) (V → ZMod 11)) = V2Submodule Γ :=
    inf_eq_left.mpr (V2Submodule_le_ker_T_F11 h)
  rw [h_eq]

/-! ### Step 2: V_λ σ-invariance (E_λ と P_σ の可換性から) -/

/-- V_λ は σ-不変 (E_λ ∘ P_σ = P_σ ∘ E_λ から). -/
theorem V7Submodule_invariant_permMatrixF11 (h : Order22ActsOnMoore57 V Γ) :
    ∀ f ∈ V7Submodule Γ, (permMatrixF11 h.σ).toLin' f ∈ V7Submodule Γ := by
  classical
  intro f hf
  rw [V7Submodule, LinearMap.mem_range] at hf ⊢
  obtain ⟨g, hg⟩ := hf
  refine ⟨(permMatrixF11 h.σ).toLin' g, ?_⟩
  rw [← hg]
  show ((E7MatrixF11 Γ).toLin') ((permMatrixF11 h.σ).toLin' g) =
       ((permMatrixF11 h.σ).toLin') ((E7MatrixF11 Γ).toLin' g)
  rw [show ((E7MatrixF11 Γ).toLin') ((permMatrixF11 h.σ).toLin' g) =
        (E7MatrixF11 Γ * permMatrixF11 h.σ).toLin' g from by
        rw [Matrix.toLin'_mul]; rfl]
  rw [show ((permMatrixF11 h.σ).toLin') ((E7MatrixF11 Γ).toLin' g) =
        (permMatrixF11 h.σ * E7MatrixF11 Γ).toLin' g from by
        rw [Matrix.toLin'_mul]; rfl]
  rw [E7_commute_permMatrixF11 h.isMoore h.σ h.σ_aut]

/-- V_3 は σ-不変. -/
theorem V3Submodule_invariant_permMatrixF11 (h : Order22ActsOnMoore57 V Γ) :
    ∀ f ∈ V3Submodule Γ, (permMatrixF11 h.σ).toLin' f ∈ V3Submodule Γ := by
  classical
  intro f hf
  rw [V3Submodule, LinearMap.mem_range] at hf ⊢
  obtain ⟨g, hg⟩ := hf
  refine ⟨(permMatrixF11 h.σ).toLin' g, ?_⟩
  rw [← hg]
  show ((E3MatrixF11 Γ).toLin') ((permMatrixF11 h.σ).toLin' g) =
       ((permMatrixF11 h.σ).toLin') ((E3MatrixF11 Γ).toLin' g)
  rw [show ((E3MatrixF11 Γ).toLin') ((permMatrixF11 h.σ).toLin' g) =
        (E3MatrixF11 Γ * permMatrixF11 h.σ).toLin' g from by
        rw [Matrix.toLin'_mul]; rfl]
  rw [show ((permMatrixF11 h.σ).toLin') ((E3MatrixF11 Γ).toLin' g) =
        (permMatrixF11 h.σ * E3MatrixF11 Γ).toLin' g from by
        rw [Matrix.toLin'_mul]; rfl]
  rw [E3_commute_permMatrixF11 h.isMoore h.σ h.σ_aut]

/-! ### E_λ は ker(T_F11) を保つ (σ と可換 ⟹ ker(σ - I) preservation) -/

/-- 一般形: P_σ と可換な行列 E は ker T_F11 を保存. -/
private theorem _commute_preserves_ker_T_F11 (h : Order22ActsOnMoore57 V Γ)
    (E : Matrix V V (ZMod 11))
    (hE : E * permMatrixF11 h.σ = permMatrixF11 h.σ * E) :
    ∀ v ∈ LinearMap.ker (T_F11 h), E.toLin' v ∈ LinearMap.ker (T_F11 h) := by
  intro v hv
  rw [LinearMap.mem_ker, T_F11_def] at hv ⊢
  show ((permMatrixF11 h.σ - 1 : Matrix V V (ZMod 11)).toLin') (E.toLin' v) = 0
  calc ((permMatrixF11 h.σ - 1 : Matrix V V (ZMod 11)).toLin') (E.toLin' v)
      = ((permMatrixF11 h.σ - 1) * E).toLin' v := by
          rw [Matrix.toLin'_mul]; rfl
    _ = (E * (permMatrixF11 h.σ - 1)).toLin' v := by
          rw [sub_mul, one_mul, mul_sub, mul_one, ← hE]
    _ = E.toLin' ((permMatrixF11 h.σ - 1 : Matrix V V (ZMod 11)).toLin' v) := by
          rw [Matrix.toLin'_mul]; rfl
    _ = E.toLin' 0 := by rw [hv]
    _ = 0 := map_zero _

/-- `E_2` は ker T_F11 を保つ. -/
theorem E2_preserves_ker_T_F11 (h : Order22ActsOnMoore57 V Γ) :
    ∀ v ∈ LinearMap.ker (T_F11 h),
      (E2MatrixF11 Γ).toLin' v ∈ LinearMap.ker (T_F11 h) :=
  _commute_preserves_ker_T_F11 h (E2MatrixF11 Γ)
    (E2_commute_permMatrixF11 h.isMoore h.σ)

/-- `E_7` は ker T_F11 を保つ. -/
theorem E7_preserves_ker_T_F11 (h : Order22ActsOnMoore57 V Γ) :
    ∀ v ∈ LinearMap.ker (T_F11 h),
      (E7MatrixF11 Γ).toLin' v ∈ LinearMap.ker (T_F11 h) :=
  _commute_preserves_ker_T_F11 h (E7MatrixF11 Γ)
    (E7_commute_permMatrixF11 h.isMoore h.σ h.σ_aut)

/-- `E_3` は ker T_F11 を保つ. -/
theorem E3_preserves_ker_T_F11 (h : Order22ActsOnMoore57 V Γ) :
    ∀ v ∈ LinearMap.ker (T_F11 h),
      (E3MatrixF11 Γ).toLin' v ∈ LinearMap.ker (T_F11 h) :=
  _commute_preserves_ker_T_F11 h (E3MatrixF11 Γ)
    (E3_commute_permMatrixF11 h.isMoore h.σ h.σ_aut)

/-- `A` は ker T_F11 を保つ (A と σ が可換). -/
theorem adjMatrixF11_preserves_ker_T_F11 (h : Order22ActsOnMoore57 V Γ) :
    ∀ v ∈ LinearMap.ker (T_F11 h),
      (adjMatrixF11 Γ).toLin' v ∈ LinearMap.ker (T_F11 h) :=
  _commute_preserves_ker_T_F11 h (adjMatrixF11 Γ)
    (adjMatrixF11_commute_permMatrixF11_σ h)

/-- `A` restricted to `ker T_F11`. -/
noncomputable def adjMatrixF11_restrict_ker_T (h : Order22ActsOnMoore57 V Γ) :
    LinearMap.ker (T_F11 h) →ₗ[ZMod 11] LinearMap.ker (T_F11 h) :=
  ((adjMatrixF11 Γ).toLin').restrict h.adjMatrixF11_preserves_ker_T_F11

/-- `E_2` restricted to `ker T_F11`. -/
noncomputable def E2_restrict_ker_T (h : Order22ActsOnMoore57 V Γ) :
    LinearMap.ker (T_F11 h) →ₗ[ZMod 11] LinearMap.ker (T_F11 h) :=
  ((E2MatrixF11 Γ).toLin').restrict h.E2_preserves_ker_T_F11

/-- `E_7` restricted to `ker T_F11`. -/
noncomputable def E7_restrict_ker_T (h : Order22ActsOnMoore57 V Γ) :
    LinearMap.ker (T_F11 h) →ₗ[ZMod 11] LinearMap.ker (T_F11 h) :=
  ((E7MatrixF11 Γ).toLin').restrict h.E7_preserves_ker_T_F11

/-- `E_3` restricted to `ker T_F11`. -/
noncomputable def E3_restrict_ker_T (h : Order22ActsOnMoore57 V Γ) :
    LinearMap.ker (T_F11 h) →ₗ[ZMod 11] LinearMap.ker (T_F11 h) :=
  ((E3MatrixF11 Γ).toLin').restrict h.E3_preserves_ker_T_F11

/-! ### V_λ ⊓ V_μ = ⊥ (E_λ idempotent + orthogonality より)

V_2, V_7, V_3 は pairwise disjoint な submodule. -/

/-- 一般形: E idempotent + E·F = 0 ⟹ range E ⊓ range F = ⊥. -/
private theorem _matrix_range_disjoint_of_idem_orth
    (E F : Matrix V V (ZMod 11))
    (h_E_idem : E * E = E)
    (h_EF_orth : E * F = 0) :
    E.toLin'.range ⊓ F.toLin'.range = (⊥ : Submodule (ZMod 11) (V → ZMod 11)) := by
  classical
  apply le_antisymm _ bot_le
  intro v hv
  rw [Submodule.mem_inf] at hv
  obtain ⟨hv_E, hv_F⟩ := hv
  obtain ⟨u_E, hu_E⟩ := LinearMap.mem_range.mp hv_E
  obtain ⟨u_F, hu_F⟩ := LinearMap.mem_range.mp hv_F
  have h_Ev_eq_v : E.toLin' v = v := by
    rw [← hu_E]
    show (E.toLin') (E.toLin' u_E) = E.toLin' u_E
    rw [show (E.toLin') (E.toLin' u_E) = (E * E).toLin' u_E from by
        rw [Matrix.toLin'_mul]; rfl, h_E_idem]
  have h_Ev_eq_zero : E.toLin' v = 0 := by
    rw [← hu_F]
    show (E.toLin') (F.toLin' u_F) = 0
    rw [show (E.toLin') (F.toLin' u_F) = (E * F).toLin' u_F from by
        rw [Matrix.toLin'_mul]; rfl, h_EF_orth]
    show (0 : Matrix V V (ZMod 11)).toLin' u_F = 0
    simp
  rw [Submodule.mem_bot]
  exact h_Ev_eq_v.symm.trans h_Ev_eq_zero

/-- `V_2 ⊓ V_7 = ⊥`. -/
theorem V2_inter_V7_eq_bot (hΓ : IsMoore57 Γ) :
    V2Submodule Γ ⊓ V7Submodule Γ = (⊥ : Submodule (ZMod 11) (V → ZMod 11)) :=
  _matrix_range_disjoint_of_idem_orth
    (E2MatrixF11 Γ) (E7MatrixF11 Γ) (E2_idempotent hΓ) (E2_mul_E7_eq_zero hΓ)

/-- `V_2 ⊓ V_3 = ⊥`. -/
theorem V2_inter_V3_eq_bot (hΓ : IsMoore57 Γ) :
    V2Submodule Γ ⊓ V3Submodule Γ = (⊥ : Submodule (ZMod 11) (V → ZMod 11)) :=
  _matrix_range_disjoint_of_idem_orth
    (E2MatrixF11 Γ) (E3MatrixF11 Γ) (E2_idempotent hΓ) (E2_mul_E3_eq_zero hΓ)

/-- `V_7 ⊓ V_3 = ⊥`. -/
theorem V7_inter_V3_eq_bot (hΓ : IsMoore57 Γ) :
    V7Submodule Γ ⊓ V3Submodule Γ = (⊥ : Submodule (ZMod 11) (V → ZMod 11)) :=
  _matrix_range_disjoint_of_idem_orth
    (E7MatrixF11 Γ) (E3MatrixF11 Γ) (E7_idempotent hΓ) (E7_mul_E3_eq_zero hΓ)

/-- E_λ 和分解: v = E_2 v + E_7 v + E_3 v (linear map レベル). -/
theorem ELambda_sum_apply (v : V → ZMod 11) :
    (E2MatrixF11 Γ).toLin' v + (E7MatrixF11 Γ).toLin' v + (E3MatrixF11 Γ).toLin' v = v := by
  classical
  have h_apply : ∀ M N : Matrix V V (ZMod 11),
      (M + N).toLin' v = M.toLin' v + N.toLin' v := fun M N => by
    simp [Matrix.toLin'_apply, Matrix.add_mulVec]
  have h_sum : ((E2MatrixF11 Γ + E7MatrixF11 Γ + E3MatrixF11 Γ).toLin') v =
      (E2MatrixF11 Γ).toLin' v + (E7MatrixF11 Γ).toLin' v + (E3MatrixF11 Γ).toLin' v := by
    rw [h_apply (E2MatrixF11 Γ + E7MatrixF11 Γ) (E3MatrixF11 Γ),
        h_apply (E2MatrixF11 Γ) (E7MatrixF11 Γ)]
  rw [← h_sum, ELambda_sum_eq_one (Γ := Γ)]
  show (1 : Matrix V V (ZMod 11)).toLin' v = v
  rw [Matrix.toLin'_one]; rfl

/-- `V_2 ⊔ V_7 ⊔ V_3 = ⊤`: V_F_11 全体を V_λ で被覆. -/
theorem V2_sup_V7_sup_V3_eq_top :
    V2Submodule Γ ⊔ V7Submodule Γ ⊔ V3Submodule Γ =
      (⊤ : Submodule (ZMod 11) (V → ZMod 11)) := by
  classical
  rw [Submodule.eq_top_iff']
  intro v
  -- v = (E_2 v + E_7 v) + E_3 v
  rw [Submodule.mem_sup]
  refine ⟨(E2MatrixF11 Γ).toLin' v + (E7MatrixF11 Γ).toLin' v, ?_,
          (E3MatrixF11 Γ).toLin' v, ?_, ELambda_sum_apply v⟩
  · -- E_2 v + E_7 v ∈ V_2 ⊔ V_7
    rw [Submodule.mem_sup]
    exact ⟨(E2MatrixF11 Γ).toLin' v, LinearMap.mem_range.mpr ⟨v, rfl⟩,
           (E7MatrixF11 Γ).toLin' v, LinearMap.mem_range.mpr ⟨v, rfl⟩, rfl⟩
  · -- E_3 v ∈ V_3
    exact LinearMap.mem_range.mpr ⟨v, rfl⟩

/-! ### Phase D-B: V_λ は T_F11-invariant (Jordan structure 前準備) -/

/-- T_F11 = P_σ - 1 は V_2 を保つ (P_σ は V_2 invariant). -/
theorem V2_invariant_T_F11 (h : Order22ActsOnMoore57 V Γ) :
    ∀ v ∈ V2Submodule Γ, (T_F11 h) v ∈ V2Submodule Γ := by
  intros v hv
  rw [T_F11_def]
  have h_eq : (((permMatrixF11 h.σ) - 1).toLin') v =
              (permMatrixF11 h.σ).toLin' v - v := by
    show ((permMatrixF11 h.σ) - 1).mulVec v = (permMatrixF11 h.σ).mulVec v - v
    rw [Matrix.sub_mulVec, Matrix.one_mulVec]
  rw [h_eq]
  -- V_2 = span 1 で σ-invariant ⟹ P_σ v ∈ V_2.
  refine Submodule.sub_mem _ ?_ hv
  -- (permMatrixF11 h.σ).toLin' v = P_σ · v ∈ V_2 (V_2 is P_σ-invariant).
  rw [V2Submodule, LinearMap.mem_range] at hv ⊢
  obtain ⟨g, hg⟩ := hv
  refine ⟨(permMatrixF11 h.σ).toLin' g, ?_⟩
  rw [← hg]
  show ((E2MatrixF11 Γ).toLin') ((permMatrixF11 h.σ).toLin' g) =
       ((permMatrixF11 h.σ).toLin') ((E2MatrixF11 Γ).toLin' g)
  rw [show ((E2MatrixF11 Γ).toLin') ((permMatrixF11 h.σ).toLin' g) =
        (E2MatrixF11 Γ * permMatrixF11 h.σ).toLin' g from by
        rw [Matrix.toLin'_mul]; rfl]
  rw [show ((permMatrixF11 h.σ).toLin') ((E2MatrixF11 Γ).toLin' g) =
        (permMatrixF11 h.σ * E2MatrixF11 Γ).toLin' g from by
        rw [Matrix.toLin'_mul]; rfl]
  rw [E2_commute_permMatrixF11 h.isMoore]

/-- T_F11 は V_7 を保つ. -/
theorem V7_invariant_T_F11 (h : Order22ActsOnMoore57 V Γ) :
    ∀ v ∈ V7Submodule Γ, (T_F11 h) v ∈ V7Submodule Γ := by
  intros v hv
  rw [T_F11_def]
  have h_eq : (((permMatrixF11 h.σ) - 1).toLin') v =
              (permMatrixF11 h.σ).toLin' v - v := by
    show ((permMatrixF11 h.σ) - 1).mulVec v = (permMatrixF11 h.σ).mulVec v - v
    rw [Matrix.sub_mulVec, Matrix.one_mulVec]
  rw [h_eq]
  refine Submodule.sub_mem _ ?_ hv
  exact h.V7Submodule_invariant_permMatrixF11 v hv

/-- T_F11 は V_3 を保つ. -/
theorem V3_invariant_T_F11 (h : Order22ActsOnMoore57 V Γ) :
    ∀ v ∈ V3Submodule Γ, (T_F11 h) v ∈ V3Submodule Γ := by
  intros v hv
  rw [T_F11_def]
  have h_eq : (((permMatrixF11 h.σ) - 1).toLin') v =
              (permMatrixF11 h.σ).toLin' v - v := by
    show ((permMatrixF11 h.σ) - 1).mulVec v = (permMatrixF11 h.σ).mulVec v - v
    rw [Matrix.sub_mulVec, Matrix.one_mulVec]
  rw [h_eq]
  refine Submodule.sub_mem _ ?_ hv
  exact h.V3Submodule_invariant_permMatrixF11 v hv

/-- T_F11 restricted to V_2. -/
private noncomputable def T_F11_V2 (h : Order22ActsOnMoore57 V Γ) :
    V2Submodule Γ →ₗ[ZMod 11] V2Submodule Γ :=
  (T_F11 h).restrict (V2_invariant_T_F11 h)

/-- T_F11 restricted to V_7. -/
private noncomputable def T_F11_V7 (h : Order22ActsOnMoore57 V Γ) :
    V7Submodule Γ →ₗ[ZMod 11] V7Submodule Γ :=
  (T_F11 h).restrict (V7_invariant_T_F11 h)

/-- T_F11 restricted to V_3. -/
private noncomputable def T_F11_V3 (h : Order22ActsOnMoore57 V Γ) :
    V3Submodule Γ →ₗ[ZMod 11] V3Submodule Γ :=
  (T_F11 h).restrict (V3_invariant_T_F11 h)

/-- 制限 LinearMap.restrict の n 乗の subtype 対応 (Submodule 制限版).
`(f.restrict h)^j x` の subtype-projection は `f^j` の x.val 適用と一致. -/
private lemma T_F11_V7_pow_val (h : Order22ActsOnMoore57 V Γ) :
    ∀ (j : ℕ) (x : V7Submodule Γ),
    (((T_F11_V7 h)^j) x : V → ZMod 11) =
      ((T_F11 h)^j) ((x : V → ZMod 11)) := by
  intro j
  induction j with
  | zero => intro x; simp
  | succ k ih =>
    intro x
    rw [pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply]
    rw [ih (T_F11_V7 h x)]
    rfl

private lemma T_F11_V2_pow_val (h : Order22ActsOnMoore57 V Γ) :
    ∀ (j : ℕ) (x : V2Submodule Γ),
    (((T_F11_V2 h)^j) x : V → ZMod 11) =
      ((T_F11 h)^j) ((x : V → ZMod 11)) := by
  intro j
  induction j with
  | zero => intro x; simp
  | succ k ih =>
    intro x
    rw [pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply]
    rw [ih (T_F11_V2 h x)]
    rfl

private lemma T_F11_V3_pow_val (h : Order22ActsOnMoore57 V Γ) :
    ∀ (j : ℕ) (x : V3Submodule Γ),
    (((T_F11_V3 h)^j) x : V → ZMod 11) =
      ((T_F11 h)^j) ((x : V → ZMod 11)) := by
  intro j
  induction j with
  | zero => intro x; simp
  | succ k ih =>
    intro x
    rw [pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply]
    rw [ih (T_F11_V3 h x)]
    rfl

/-- ker (T_F11_V7)^j を subtype 経由で V_7 ⊓ ker T_F11^j に対応付け. -/
private lemma map_subtype_ker_T_F11_V7_pow_eq (h : Order22ActsOnMoore57 V Γ) (j : ℕ) :
    Submodule.map (V7Submodule Γ).subtype (LinearMap.ker ((T_F11_V7 h)^j)) =
    V7Submodule Γ ⊓ LinearMap.ker ((T_F11 h)^j) := by
  ext v
  simp only [Submodule.mem_map, LinearMap.mem_ker, Submodule.mem_inf,
             Submodule.coe_subtype]
  constructor
  · rintro ⟨⟨x, hx_mem⟩, hx_ker, hx_eq⟩
    refine ⟨?_, ?_⟩
    · rw [← hx_eq]; exact hx_mem
    · rw [← hx_eq]
      have := T_F11_V7_pow_val h j ⟨x, hx_mem⟩
      rw [hx_ker] at this
      simp at this
      exact this.symm
  · rintro ⟨hv_in, hv_ker⟩
    refine ⟨⟨v, hv_in⟩, ?_, rfl⟩
    apply Subtype.ext
    have := T_F11_V7_pow_val h j ⟨v, hv_in⟩
    rw [this]
    exact hv_ker

private lemma map_subtype_ker_T_F11_V2_pow_eq (h : Order22ActsOnMoore57 V Γ) (j : ℕ) :
    Submodule.map (V2Submodule Γ).subtype (LinearMap.ker ((T_F11_V2 h)^j)) =
    V2Submodule Γ ⊓ LinearMap.ker ((T_F11 h)^j) := by
  ext v
  simp only [Submodule.mem_map, LinearMap.mem_ker, Submodule.mem_inf,
             Submodule.coe_subtype]
  constructor
  · rintro ⟨⟨x, hx_mem⟩, hx_ker, hx_eq⟩
    refine ⟨?_, ?_⟩
    · rw [← hx_eq]; exact hx_mem
    · rw [← hx_eq]
      have := T_F11_V2_pow_val h j ⟨x, hx_mem⟩
      rw [hx_ker] at this
      simp at this
      exact this.symm
  · rintro ⟨hv_in, hv_ker⟩
    refine ⟨⟨v, hv_in⟩, ?_, rfl⟩
    apply Subtype.ext
    have := T_F11_V2_pow_val h j ⟨v, hv_in⟩
    rw [this]
    exact hv_ker

private lemma map_subtype_ker_T_F11_V3_pow_eq (h : Order22ActsOnMoore57 V Γ) (j : ℕ) :
    Submodule.map (V3Submodule Γ).subtype (LinearMap.ker ((T_F11_V3 h)^j)) =
    V3Submodule Γ ⊓ LinearMap.ker ((T_F11 h)^j) := by
  ext v
  simp only [Submodule.mem_map, LinearMap.mem_ker, Submodule.mem_inf,
             Submodule.coe_subtype]
  constructor
  · rintro ⟨⟨x, hx_mem⟩, hx_ker, hx_eq⟩
    refine ⟨?_, ?_⟩
    · rw [← hx_eq]; exact hx_mem
    · rw [← hx_eq]
      have := T_F11_V3_pow_val h j ⟨x, hx_mem⟩
      rw [hx_ker] at this
      simp at this
      exact this.symm
  · rintro ⟨hv_in, hv_ker⟩
    refine ⟨⟨v, hv_in⟩, ?_, rfl⟩
    apply Subtype.ext
    have := T_F11_V3_pow_val h j ⟨v, hv_in⟩
    rw [this]
    exact hv_ker

/-- finrank の対応 (V_λ ⊓ ker T^j) と (ker T_F11_V_λ^j). -/
private lemma finrank_ker_T_F11_V7_pow_eq (h : Order22ActsOnMoore57 V Γ) (j : ℕ) :
    Module.finrank (ZMod 11) (V7Submodule Γ ⊓ LinearMap.ker ((T_F11 h)^j) :
        Submodule (ZMod 11) (V → ZMod 11)) =
    Module.finrank (ZMod 11) (LinearMap.ker ((T_F11_V7 h)^j)) := by
  rw [← map_subtype_ker_T_F11_V7_pow_eq h j]
  exact Submodule.finrank_map_subtype_eq _ _

private lemma finrank_ker_T_F11_V2_pow_eq (h : Order22ActsOnMoore57 V Γ) (j : ℕ) :
    Module.finrank (ZMod 11) (V2Submodule Γ ⊓ LinearMap.ker ((T_F11 h)^j) :
        Submodule (ZMod 11) (V → ZMod 11)) =
    Module.finrank (ZMod 11) (LinearMap.ker ((T_F11_V2 h)^j)) := by
  rw [← map_subtype_ker_T_F11_V2_pow_eq h j]
  exact Submodule.finrank_map_subtype_eq _ _

private lemma finrank_ker_T_F11_V3_pow_eq (h : Order22ActsOnMoore57 V Γ) (j : ℕ) :
    Module.finrank (ZMod 11) (V3Submodule Γ ⊓ LinearMap.ker ((T_F11 h)^j) :
        Submodule (ZMod 11) (V → ZMod 11)) =
    Module.finrank (ZMod 11) (LinearMap.ker ((T_F11_V3 h)^j)) := by
  rw [← map_subtype_ker_T_F11_V3_pow_eq h j]
  exact Submodule.finrank_map_subtype_eq _ _

/-- 一般形: P_σ と可換な行列 E は ker T_F11^j を保つ (各 j). -/
private theorem _commute_preserves_ker_T_F11_pow (h : Order22ActsOnMoore57 V Γ)
    (E : Matrix V V (ZMod 11))
    (hE : E * permMatrixF11 h.σ = permMatrixF11 h.σ * E) (j : ℕ) :
    ∀ v ∈ LinearMap.ker ((T_F11 h)^j), E.toLin' v ∈ LinearMap.ker ((T_F11 h)^j) := by
  -- E commutes with (P_σ - 1) (from commutes with P_σ).
  have h_comm_T : E * (permMatrixF11 h.σ - 1) = (permMatrixF11 h.σ - 1) * E := by
    rw [mul_sub, sub_mul, mul_one, one_mul, hE]
  -- E commutes with (P_σ - 1)^j by induction.
  have h_comm_T_pow : E * ((permMatrixF11 h.σ - 1)^j) =
      ((permMatrixF11 h.σ - 1)^j) * E := by
    induction j with
    | zero => simp
    | succ k ih =>
      rw [pow_succ, ← mul_assoc, ih, mul_assoc, h_comm_T, ← mul_assoc]
  intro v hv
  rw [LinearMap.mem_ker] at hv ⊢
  rw [T_F11_def] at hv ⊢
  rw [show (((permMatrixF11 h.σ) - 1).toLin')^j =
        (((permMatrixF11 h.σ) - 1)^j).toLin' from (Matrix.toLin'_pow _ _).symm] at hv ⊢
  -- Now hv : ((P_σ - 1)^j).toLin' v = 0.
  -- Goal : ((P_σ - 1)^j).toLin' (E.toLin' v) = 0.
  rw [show (((permMatrixF11 h.σ) - 1)^j).toLin' (E.toLin' v) =
        ((((permMatrixF11 h.σ) - 1)^j) * E).toLin' v from by
        rw [Matrix.toLin'_mul]; rfl]
  rw [← h_comm_T_pow]
  show (E * ((permMatrixF11 h.σ - 1)^j)).toLin' v = 0
  rw [show (E * ((permMatrixF11 h.σ - 1)^j)).toLin' v =
        E.toLin' ((((permMatrixF11 h.σ) - 1)^j).toLin' v) from by
        rw [Matrix.toLin'_mul]; rfl]
  rw [hv]; exact map_zero _

private theorem E2_preserves_ker_T_F11_pow (h : Order22ActsOnMoore57 V Γ) (j : ℕ) :
    ∀ v ∈ LinearMap.ker ((T_F11 h)^j),
      (E2MatrixF11 Γ).toLin' v ∈ LinearMap.ker ((T_F11 h)^j) :=
  _commute_preserves_ker_T_F11_pow h (E2MatrixF11 Γ)
    (E2_commute_permMatrixF11 h.isMoore h.σ) j

private theorem E7_preserves_ker_T_F11_pow (h : Order22ActsOnMoore57 V Γ) (j : ℕ) :
    ∀ v ∈ LinearMap.ker ((T_F11 h)^j),
      (E7MatrixF11 Γ).toLin' v ∈ LinearMap.ker ((T_F11 h)^j) :=
  _commute_preserves_ker_T_F11_pow h (E7MatrixF11 Γ)
    (E7_commute_permMatrixF11 h.isMoore h.σ h.σ_aut) j

private theorem E3_preserves_ker_T_F11_pow (h : Order22ActsOnMoore57 V Γ) (j : ℕ) :
    ∀ v ∈ LinearMap.ker ((T_F11 h)^j),
      (E3MatrixF11 Γ).toLin' v ∈ LinearMap.ker ((T_F11 h)^j) :=
  _commute_preserves_ker_T_F11_pow h (E3MatrixF11 Γ)
    (E3_commute_permMatrixF11 h.isMoore h.σ h.σ_aut) j

/-- `ker T_F11^j = (V_2 ⊓ ker T^j) ⊔ (V_7 ⊓ ker T^j) ⊔ (V_3 ⊓ ker T^j)` (各 j). -/
private theorem ker_T_F11_pow_eq_sup_three (h : Order22ActsOnMoore57 V Γ) (j : ℕ) :
    (V2Submodule Γ ⊓ LinearMap.ker ((T_F11 h)^j)) ⊔
      (V7Submodule Γ ⊓ LinearMap.ker ((T_F11 h)^j)) ⊔
      (V3Submodule Γ ⊓ LinearMap.ker ((T_F11 h)^j)) =
    LinearMap.ker ((T_F11 h)^j) := by
  classical
  apply le_antisymm
  · refine sup_le (sup_le inf_le_right inf_le_right) inf_le_right
  · intro v hv
    rw [Submodule.mem_sup]
    refine ⟨(E2MatrixF11 Γ).toLin' v + (E7MatrixF11 Γ).toLin' v, ?_,
            (E3MatrixF11 Γ).toLin' v, ?_, ELambda_sum_apply v⟩
    · rw [Submodule.mem_sup]
      refine ⟨(E2MatrixF11 Γ).toLin' v, ?_, (E7MatrixF11 Γ).toLin' v, ?_, rfl⟩
      · exact Submodule.mem_inf.mpr
          ⟨LinearMap.mem_range.mpr ⟨v, rfl⟩, E2_preserves_ker_T_F11_pow h j v hv⟩
      · exact Submodule.mem_inf.mpr
          ⟨LinearMap.mem_range.mpr ⟨v, rfl⟩, E7_preserves_ker_T_F11_pow h j v hv⟩
    · exact Submodule.mem_inf.mpr
        ⟨LinearMap.mem_range.mpr ⟨v, rfl⟩, E3_preserves_ker_T_F11_pow h j v hv⟩

/-- (V_2 ⊓ ker T^j) ⊓ (V_7 ⊓ ker T^j) = ⊥. -/
private theorem V2kt_inter_V7kt_pow_eq_bot (h : Order22ActsOnMoore57 V Γ) (j : ℕ) :
    (V2Submodule Γ ⊓ LinearMap.ker ((T_F11 h)^j)) ⊓
      (V7Submodule Γ ⊓ LinearMap.ker ((T_F11 h)^j)) =
    (⊥ : Submodule (ZMod 11) (V → ZMod 11)) := by
  classical
  apply le_antisymm _ bot_le
  intro v hv
  rw [Submodule.mem_inf] at hv
  obtain ⟨hv_2, hv_7⟩ := hv
  rw [Submodule.mem_inf] at hv_2 hv_7
  have h_in : v ∈ V2Submodule Γ ⊓ V7Submodule Γ :=
    Submodule.mem_inf.mpr ⟨hv_2.1, hv_7.1⟩
  rw [V2_inter_V7_eq_bot h.isMoore] at h_in
  exact h_in

private theorem V2kt_inter_V3kt_pow_eq_bot (h : Order22ActsOnMoore57 V Γ) (j : ℕ) :
    (V2Submodule Γ ⊓ LinearMap.ker ((T_F11 h)^j)) ⊓
      (V3Submodule Γ ⊓ LinearMap.ker ((T_F11 h)^j)) =
    (⊥ : Submodule (ZMod 11) (V → ZMod 11)) := by
  classical
  apply le_antisymm _ bot_le
  intro v hv
  rw [Submodule.mem_inf] at hv
  obtain ⟨hv_2, hv_3⟩ := hv
  rw [Submodule.mem_inf] at hv_2 hv_3
  have h_in : v ∈ V2Submodule Γ ⊓ V3Submodule Γ :=
    Submodule.mem_inf.mpr ⟨hv_2.1, hv_3.1⟩
  rw [V2_inter_V3_eq_bot h.isMoore] at h_in
  exact h_in

private theorem V7kt_inter_V3kt_pow_eq_bot (h : Order22ActsOnMoore57 V Γ) (j : ℕ) :
    (V7Submodule Γ ⊓ LinearMap.ker ((T_F11 h)^j)) ⊓
      (V3Submodule Γ ⊓ LinearMap.ker ((T_F11 h)^j)) =
    (⊥ : Submodule (ZMod 11) (V → ZMod 11)) := by
  classical
  apply le_antisymm _ bot_le
  intro v hv
  rw [Submodule.mem_inf] at hv
  obtain ⟨hv_7, hv_3⟩ := hv
  rw [Submodule.mem_inf] at hv_7 hv_3
  have h_in : v ∈ V7Submodule Γ ⊓ V3Submodule Γ :=
    Submodule.mem_inf.mpr ⟨hv_7.1, hv_3.1⟩
  rw [V7_inter_V3_eq_bot h.isMoore] at h_in
  exact h_in

private theorem V2kt_sup_V7kt_inter_V3kt_pow_eq_bot
    (h : Order22ActsOnMoore57 V Γ) (j : ℕ) :
    ((V2Submodule Γ ⊓ LinearMap.ker ((T_F11 h)^j)) ⊔
       (V7Submodule Γ ⊓ LinearMap.ker ((T_F11 h)^j))) ⊓
      (V3Submodule Γ ⊓ LinearMap.ker ((T_F11 h)^j)) =
    (⊥ : Submodule (ZMod 11) (V → ZMod 11)) := by
  classical
  apply le_antisymm _ bot_le
  intro v hv
  rw [Submodule.mem_inf] at hv
  obtain ⟨h_sup, hv_3⟩ := hv
  rw [Submodule.mem_sup] at h_sup
  obtain ⟨w_2, hw_2, w_7, hw_7, h_sum⟩ := h_sup
  rw [Submodule.mem_inf] at hw_2 hw_7 hv_3
  obtain ⟨u_3, hu_3⟩ := LinearMap.mem_range.mp hv_3.1
  obtain ⟨u_2, hu_2⟩ := LinearMap.mem_range.mp hw_2.1
  obtain ⟨u_7, hu_7⟩ := LinearMap.mem_range.mp hw_7.1
  have h_E3v_eq_v : (E3MatrixF11 Γ).toLin' v = v := by
    rw [← hu_3]
    show (E3MatrixF11 Γ).toLin' ((E3MatrixF11 Γ).toLin' u_3) = (E3MatrixF11 Γ).toLin' u_3
    rw [show (E3MatrixF11 Γ).toLin' ((E3MatrixF11 Γ).toLin' u_3) =
            (E3MatrixF11 Γ * E3MatrixF11 Γ).toLin' u_3 from by
          rw [Matrix.toLin'_mul]; rfl,
        E3_idempotent h.isMoore]
  have h_E3v_eq_zero : (E3MatrixF11 Γ).toLin' v = 0 := by
    rw [← h_sum, map_add, ← hu_2, ← hu_7]
    show (E3MatrixF11 Γ).toLin' ((E2MatrixF11 Γ).toLin' u_2) +
         (E3MatrixF11 Γ).toLin' ((E7MatrixF11 Γ).toLin' u_7) = 0
    rw [show (E3MatrixF11 Γ).toLin' ((E2MatrixF11 Γ).toLin' u_2) =
            (E3MatrixF11 Γ * E2MatrixF11 Γ).toLin' u_2 from by
          rw [Matrix.toLin'_mul]; rfl,
        show (E3MatrixF11 Γ).toLin' ((E7MatrixF11 Γ).toLin' u_7) =
            (E3MatrixF11 Γ * E7MatrixF11 Γ).toLin' u_7 from by
          rw [Matrix.toLin'_mul]; rfl,
        E3_mul_E2_eq_zero h.isMoore, E3_mul_E7_eq_zero h.isMoore]
    show (0 : Matrix V V (ZMod 11)).toLin' u_2 +
         (0 : Matrix V V (ZMod 11)).toLin' u_7 = 0
    simp
  rw [Submodule.mem_bot]
  exact h_E3v_eq_v.symm.trans h_E3v_eq_zero

/-- finrank(V_λ ⊓ ker T^j) は j について concave (finrank_ker_pow_concave 経由). -/
private theorem finrank_V7_inter_ker_T_F11_pow_concave
    (h : Order22ActsOnMoore57 V Γ) {j : ℕ} (hj : 1 ≤ j) :
    Module.finrank (ZMod 11)
        (V7Submodule Γ ⊓ LinearMap.ker ((T_F11 h)^(j+1)) :
          Submodule (ZMod 11) (V → ZMod 11)) +
      Module.finrank (ZMod 11)
        (V7Submodule Γ ⊓ LinearMap.ker ((T_F11 h)^(j-1)) :
          Submodule (ZMod 11) (V → ZMod 11)) ≤
    2 * Module.finrank (ZMod 11)
        (V7Submodule Γ ⊓ LinearMap.ker ((T_F11 h)^j) :
          Submodule (ZMod 11) (V → ZMod 11)) := by
  rw [finrank_ker_T_F11_V7_pow_eq, finrank_ker_T_F11_V7_pow_eq h j,
      finrank_ker_T_F11_V7_pow_eq h (j-1)]
  exact Moore57.LinearAlgebra.finrank_ker_pow_concave (T_F11_V7 h) hj

private theorem finrank_V2_inter_ker_T_F11_pow_concave
    (h : Order22ActsOnMoore57 V Γ) {j : ℕ} (hj : 1 ≤ j) :
    Module.finrank (ZMod 11)
        (V2Submodule Γ ⊓ LinearMap.ker ((T_F11 h)^(j+1)) :
          Submodule (ZMod 11) (V → ZMod 11)) +
      Module.finrank (ZMod 11)
        (V2Submodule Γ ⊓ LinearMap.ker ((T_F11 h)^(j-1)) :
          Submodule (ZMod 11) (V → ZMod 11)) ≤
    2 * Module.finrank (ZMod 11)
        (V2Submodule Γ ⊓ LinearMap.ker ((T_F11 h)^j) :
          Submodule (ZMod 11) (V → ZMod 11)) := by
  rw [finrank_ker_T_F11_V2_pow_eq, finrank_ker_T_F11_V2_pow_eq h j,
      finrank_ker_T_F11_V2_pow_eq h (j-1)]
  exact Moore57.LinearAlgebra.finrank_ker_pow_concave (T_F11_V2 h) hj

private theorem finrank_V3_inter_ker_T_F11_pow_concave
    (h : Order22ActsOnMoore57 V Γ) {j : ℕ} (hj : 1 ≤ j) :
    Module.finrank (ZMod 11)
        (V3Submodule Γ ⊓ LinearMap.ker ((T_F11 h)^(j+1)) :
          Submodule (ZMod 11) (V → ZMod 11)) +
      Module.finrank (ZMod 11)
        (V3Submodule Γ ⊓ LinearMap.ker ((T_F11 h)^(j-1)) :
          Submodule (ZMod 11) (V → ZMod 11)) ≤
    2 * Module.finrank (ZMod 11)
        (V3Submodule Γ ⊓ LinearMap.ker ((T_F11 h)^j) :
          Submodule (ZMod 11) (V → ZMod 11)) := by
  rw [finrank_ker_T_F11_V3_pow_eq, finrank_ker_T_F11_V3_pow_eq h j,
      finrank_ker_T_F11_V3_pow_eq h (j-1)]
  exact Moore57.LinearAlgebra.finrank_ker_pow_concave (T_F11_V3 h) hj

/-- Σ_λ finrank(V_λ ⊓ ker T^j) = finrank ker T^j. -/
private theorem finrank_sum_V_lambda_inter_ker_T_F11_pow
    (h : Order22ActsOnMoore57 V Γ) (j : ℕ) :
    Module.finrank (ZMod 11)
        (V2Submodule Γ ⊓ LinearMap.ker ((T_F11 h)^j) :
          Submodule (ZMod 11) (V → ZMod 11)) +
      Module.finrank (ZMod 11)
        (V7Submodule Γ ⊓ LinearMap.ker ((T_F11 h)^j) :
          Submodule (ZMod 11) (V → ZMod 11)) +
      Module.finrank (ZMod 11)
        (V3Submodule Γ ⊓ LinearMap.ker ((T_F11 h)^j) :
          Submodule (ZMod 11) (V → ZMod 11)) =
    Module.finrank (ZMod 11) (LinearMap.ker ((T_F11 h)^j)) := by
  classical
  haveI : FiniteDimensional (ZMod 11) (V → ZMod 11) := by infer_instance
  set S_2 := V2Submodule Γ ⊓ LinearMap.ker ((T_F11 h)^j) with hS2_def
  set S_7 := V7Submodule Γ ⊓ LinearMap.ker ((T_F11 h)^j) with hS7_def
  set S_3 := V3Submodule Γ ⊓ LinearMap.ker ((T_F11 h)^j) with hS3_def
  have h_sup_eq : (S_2 ⊔ S_7) ⊔ S_3 = LinearMap.ker ((T_F11 h)^j) :=
    ker_T_F11_pow_eq_sup_three h j
  have h_27_3_disj : (S_2 ⊔ S_7) ⊓ S_3 = ⊥ := V2kt_sup_V7kt_inter_V3kt_pow_eq_bot h j
  have h_27_disj : S_2 ⊓ S_7 = ⊥ := V2kt_inter_V7kt_pow_eq_bot h j
  have h_27_3_finrank : Module.finrank (ZMod 11) ↥((S_2 ⊔ S_7) ⊔ S_3) =
      Module.finrank (ZMod 11) ↥(S_2 ⊔ S_7) + Module.finrank (ZMod 11) ↥S_3 := by
    have h_eq := Submodule.finrank_sup_add_finrank_inf_eq (S_2 ⊔ S_7) S_3
    rw [h_27_3_disj, finrank_bot] at h_eq
    omega
  have h_27_finrank : Module.finrank (ZMod 11) ↥(S_2 ⊔ S_7) =
      Module.finrank (ZMod 11) ↥S_2 + Module.finrank (ZMod 11) ↥S_7 := by
    have h_eq := Submodule.finrank_sup_add_finrank_inf_eq S_2 S_7
    rw [h_27_disj, finrank_bot] at h_eq
    omega
  rw [← h_sup_eq, h_27_3_finrank, h_27_finrank]

/-! ### Linearity forcing: concave summing to linear ⟹ each linear -/

/-- For each λ and j ∈ [2, 10], the concavity inequality is **equality**:
`g_λ(j+1) + g_λ(j-1) = 2 g_λ(j)`.

理由: Σ_λ concavity gives Σ ≤. But Σ g_λ = g_total = 5 + 295j is linear on [1, 11].
For j ∈ [2, 10], g_total(j+1) + g_total(j-1) = 2 g_total(j). So Σ inequality is
equality, hence each individual inequality is equality. -/
private theorem g_V_lambda_linearity_inner_eq
    (h : Order22ActsOnMoore57 V Γ) {j : ℕ}
    (hj_ge : 2 ≤ j) (hj_le : j ≤ 10) :
    -- V_2
    (Module.finrank (ZMod 11)
        (V2Submodule Γ ⊓ LinearMap.ker ((T_F11 h)^(j+1)) :
          Submodule (ZMod 11) (V → ZMod 11)) +
      Module.finrank (ZMod 11)
        (V2Submodule Γ ⊓ LinearMap.ker ((T_F11 h)^(j-1)) :
          Submodule (ZMod 11) (V → ZMod 11)) =
    2 * Module.finrank (ZMod 11)
        (V2Submodule Γ ⊓ LinearMap.ker ((T_F11 h)^j) :
          Submodule (ZMod 11) (V → ZMod 11))) ∧
    -- V_7
    (Module.finrank (ZMod 11)
        (V7Submodule Γ ⊓ LinearMap.ker ((T_F11 h)^(j+1)) :
          Submodule (ZMod 11) (V → ZMod 11)) +
      Module.finrank (ZMod 11)
        (V7Submodule Γ ⊓ LinearMap.ker ((T_F11 h)^(j-1)) :
          Submodule (ZMod 11) (V → ZMod 11)) =
    2 * Module.finrank (ZMod 11)
        (V7Submodule Γ ⊓ LinearMap.ker ((T_F11 h)^j) :
          Submodule (ZMod 11) (V → ZMod 11))) ∧
    -- V_3
    (Module.finrank (ZMod 11)
        (V3Submodule Γ ⊓ LinearMap.ker ((T_F11 h)^(j+1)) :
          Submodule (ZMod 11) (V → ZMod 11)) +
      Module.finrank (ZMod 11)
        (V3Submodule Γ ⊓ LinearMap.ker ((T_F11 h)^(j-1)) :
          Submodule (ZMod 11) (V → ZMod 11)) =
    2 * Module.finrank (ZMod 11)
        (V3Submodule Γ ⊓ LinearMap.ker ((T_F11 h)^j) :
          Submodule (ZMod 11) (V → ZMod 11))) := by
  -- Concavity inequalities.
  have h_concave_2 := finrank_V2_inter_ker_T_F11_pow_concave h (by omega : 1 ≤ j)
  have h_concave_7 := finrank_V7_inter_ker_T_F11_pow_concave h (by omega : 1 ≤ j)
  have h_concave_3 := finrank_V3_inter_ker_T_F11_pow_concave h (by omega : 1 ≤ j)
  -- Σ identities at j+1, j, j-1.
  have h_sum_jp1 := finrank_sum_V_lambda_inter_ker_T_F11_pow h (j+1)
  have h_sum_j := finrank_sum_V_lambda_inter_ker_T_F11_pow h j
  have h_sum_jm1 := finrank_sum_V_lambda_inter_ker_T_F11_pow h (j-1)
  -- g_total(k) = 5 + 295 k for k ∈ [1, 11].
  have h_total_jp1 := h.finrank_ker_T_F11_pow (by omega : 1 ≤ j+1) (by omega : j+1 ≤ 11)
  have h_total_j := h.finrank_ker_T_F11_pow (by omega : 1 ≤ j) (by omega : j ≤ 11)
  have h_total_jm1 := h.finrank_ker_T_F11_pow (by omega : 1 ≤ j-1) (by omega : j-1 ≤ 11)
  -- Combine: Σ (g_λ(j+1) + g_λ(j-1)) ≤ Σ 2 g_λ(j). With Σ = 2 Σ from linear total.
  -- Hence each ≤ becomes =.
  omega

/-- For each λ, `g_λ(j+1) - g_λ(j) = g_λ(j) - g_λ(j-1)` for j ∈ [2, 10]. -/
private theorem g_V7_difference_eq_at_inner
    (h : Order22ActsOnMoore57 V Γ) {j : ℕ}
    (hj_ge : 2 ≤ j) (hj_le : j ≤ 10) :
    Module.finrank (ZMod 11)
        (V7Submodule Γ ⊓ LinearMap.ker ((T_F11 h)^(j+1)) :
          Submodule (ZMod 11) (V → ZMod 11)) -
      Module.finrank (ZMod 11)
        (V7Submodule Γ ⊓ LinearMap.ker ((T_F11 h)^j) :
          Submodule (ZMod 11) (V → ZMod 11)) =
    Module.finrank (ZMod 11)
        (V7Submodule Γ ⊓ LinearMap.ker ((T_F11 h)^j) :
          Submodule (ZMod 11) (V → ZMod 11)) -
      Module.finrank (ZMod 11)
        (V7Submodule Γ ⊓ LinearMap.ker ((T_F11 h)^(j-1)) :
          Submodule (ZMod 11) (V → ZMod 11)) := by
  have ⟨_, h_7, _⟩ := g_V_lambda_linearity_inner_eq h hj_ge hj_le
  omega

private theorem g_V2_difference_eq_at_inner
    (h : Order22ActsOnMoore57 V Γ) {j : ℕ}
    (hj_ge : 2 ≤ j) (hj_le : j ≤ 10) :
    Module.finrank (ZMod 11)
        (V2Submodule Γ ⊓ LinearMap.ker ((T_F11 h)^(j+1)) :
          Submodule (ZMod 11) (V → ZMod 11)) -
      Module.finrank (ZMod 11)
        (V2Submodule Γ ⊓ LinearMap.ker ((T_F11 h)^j) :
          Submodule (ZMod 11) (V → ZMod 11)) =
    Module.finrank (ZMod 11)
        (V2Submodule Γ ⊓ LinearMap.ker ((T_F11 h)^j) :
          Submodule (ZMod 11) (V → ZMod 11)) -
      Module.finrank (ZMod 11)
        (V2Submodule Γ ⊓ LinearMap.ker ((T_F11 h)^(j-1)) :
          Submodule (ZMod 11) (V → ZMod 11)) := by
  have ⟨h_2, _, _⟩ := g_V_lambda_linearity_inner_eq h hj_ge hj_le
  omega

private theorem g_V3_difference_eq_at_inner
    (h : Order22ActsOnMoore57 V Γ) {j : ℕ}
    (hj_ge : 2 ≤ j) (hj_le : j ≤ 10) :
    Module.finrank (ZMod 11)
        (V3Submodule Γ ⊓ LinearMap.ker ((T_F11 h)^(j+1)) :
          Submodule (ZMod 11) (V → ZMod 11)) -
      Module.finrank (ZMod 11)
        (V3Submodule Γ ⊓ LinearMap.ker ((T_F11 h)^j) :
          Submodule (ZMod 11) (V → ZMod 11)) =
    Module.finrank (ZMod 11)
        (V3Submodule Γ ⊓ LinearMap.ker ((T_F11 h)^j) :
          Submodule (ZMod 11) (V → ZMod 11)) -
      Module.finrank (ZMod 11)
        (V3Submodule Γ ⊓ LinearMap.ker ((T_F11 h)^(j-1)) :
          Submodule (ZMod 11) (V → ZMod 11)) := by
  have ⟨_, _, h_3⟩ := g_V_lambda_linearity_inner_eq h hj_ge hj_le
  omega

/-- **Linearity result (additive form)**: For V_7,
`g_λ(j+1) + g_λ(1) = g_λ(j) + g_λ(2)` for j ∈ [1, 10].
これは `g_λ(j+1) - g_λ(j) = g_λ(2) - g_λ(1)` の加法形 (ℕ subtraction 回避). -/
private theorem g_V7_linear_add_form (h : Order22ActsOnMoore57 V Γ) :
    ∀ {j : ℕ}, 1 ≤ j → j ≤ 10 →
    Module.finrank (ZMod 11)
        (V7Submodule Γ ⊓ LinearMap.ker ((T_F11 h)^(j+1)) :
          Submodule (ZMod 11) (V → ZMod 11)) +
      Module.finrank (ZMod 11)
        (V7Submodule Γ ⊓ LinearMap.ker ((T_F11 h)^1) :
          Submodule (ZMod 11) (V → ZMod 11)) =
    Module.finrank (ZMod 11)
        (V7Submodule Γ ⊓ LinearMap.ker ((T_F11 h)^j) :
          Submodule (ZMod 11) (V → ZMod 11)) +
      Module.finrank (ZMod 11)
        (V7Submodule Γ ⊓ LinearMap.ker ((T_F11 h)^2) :
          Submodule (ZMod 11) (V → ZMod 11)) := by
  intro j hj_ge hj_le
  induction j with
  | zero => omega
  | succ k ih =>
    by_cases hk0 : k = 0
    · subst hk0; ring
    · have hk_pos : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hk0
      have hk_le : k ≤ 10 := by omega
      have h_step_all :=
        g_V_lambda_linearity_inner_eq h (by omega : 2 ≤ k+1) (by omega : k+1 ≤ 10)
      have h_idx : k + 1 - 1 = k := by omega
      rw [h_idx] at h_step_all
      have h_ih := ih hk_pos hk_le
      omega

private theorem g_V2_linear_add_form (h : Order22ActsOnMoore57 V Γ) :
    ∀ {j : ℕ}, 1 ≤ j → j ≤ 10 →
    Module.finrank (ZMod 11)
        (V2Submodule Γ ⊓ LinearMap.ker ((T_F11 h)^(j+1)) :
          Submodule (ZMod 11) (V → ZMod 11)) +
      Module.finrank (ZMod 11)
        (V2Submodule Γ ⊓ LinearMap.ker ((T_F11 h)^1) :
          Submodule (ZMod 11) (V → ZMod 11)) =
    Module.finrank (ZMod 11)
        (V2Submodule Γ ⊓ LinearMap.ker ((T_F11 h)^j) :
          Submodule (ZMod 11) (V → ZMod 11)) +
      Module.finrank (ZMod 11)
        (V2Submodule Γ ⊓ LinearMap.ker ((T_F11 h)^2) :
          Submodule (ZMod 11) (V → ZMod 11)) := by
  intro j hj_ge hj_le
  induction j with
  | zero => omega
  | succ k ih =>
    by_cases hk0 : k = 0
    · subst hk0; ring
    · have hk_pos : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hk0
      have hk_le : k ≤ 10 := by omega
      have h_step_all :=
        g_V_lambda_linearity_inner_eq h (by omega : 2 ≤ k+1) (by omega : k+1 ≤ 10)
      have h_idx : k + 1 - 1 = k := by omega
      rw [h_idx] at h_step_all
      have h_ih := ih hk_pos hk_le
      omega

private theorem g_V3_linear_add_form (h : Order22ActsOnMoore57 V Γ) :
    ∀ {j : ℕ}, 1 ≤ j → j ≤ 10 →
    Module.finrank (ZMod 11)
        (V3Submodule Γ ⊓ LinearMap.ker ((T_F11 h)^(j+1)) :
          Submodule (ZMod 11) (V → ZMod 11)) +
      Module.finrank (ZMod 11)
        (V3Submodule Γ ⊓ LinearMap.ker ((T_F11 h)^1) :
          Submodule (ZMod 11) (V → ZMod 11)) =
    Module.finrank (ZMod 11)
        (V3Submodule Γ ⊓ LinearMap.ker ((T_F11 h)^j) :
          Submodule (ZMod 11) (V → ZMod 11)) +
      Module.finrank (ZMod 11)
        (V3Submodule Γ ⊓ LinearMap.ker ((T_F11 h)^2) :
          Submodule (ZMod 11) (V → ZMod 11)) := by
  intro j hj_ge hj_le
  induction j with
  | zero => omega
  | succ k ih =>
    by_cases hk0 : k = 0
    · subst hk0; ring
    · have hk_pos : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hk0
      have hk_le : k ≤ 10 := by omega
      have h_step_all :=
        g_V_lambda_linearity_inner_eq h (by omega : 2 ≤ k+1) (by omega : k+1 ≤ 10)
      have h_idx : k + 1 - 1 = k := by omega
      rw [h_idx] at h_step_all
      have h_ih := ih hk_pos hk_le
      omega

/-! ### dim V_λ relation from linearity at j = 11 -/

/-- `(T_F11 h)^11 = 0` から `ker (T_F11 h)^11 = ⊤`. -/
private theorem ker_T_F11_pow_eleven_eq_top (h : Order22ActsOnMoore57 V Γ) :
    LinearMap.ker ((T_F11 h)^11) = (⊤ : Submodule (ZMod 11) (V → ZMod 11)) := by
  rw [h.T_F11_pow_eleven_eq_zero, LinearMap.ker_zero]

/-- g_λ(11) = dim V_λ for each λ. -/
private theorem g_V7_eleven_eq_dim (h : Order22ActsOnMoore57 V Γ) :
    Module.finrank (ZMod 11) (V7Submodule Γ ⊓ LinearMap.ker ((T_F11 h)^11) :
        Submodule (ZMod 11) (V → ZMod 11)) =
    Module.finrank (ZMod 11) (V7Submodule Γ) := by
  rw [ker_T_F11_pow_eleven_eq_top, inf_top_eq]

private theorem g_V2_eleven_eq_dim (h : Order22ActsOnMoore57 V Γ) :
    Module.finrank (ZMod 11) (V2Submodule Γ ⊓ LinearMap.ker ((T_F11 h)^11) :
        Submodule (ZMod 11) (V → ZMod 11)) =
    Module.finrank (ZMod 11) (V2Submodule Γ) := by
  rw [ker_T_F11_pow_eleven_eq_top, inf_top_eq]

private theorem g_V3_eleven_eq_dim (h : Order22ActsOnMoore57 V Γ) :
    Module.finrank (ZMod 11) (V3Submodule Γ ⊓ LinearMap.ker ((T_F11 h)^11) :
        Submodule (ZMod 11) (V → ZMod 11)) =
    Module.finrank (ZMod 11) (V3Submodule Γ) := by
  rw [ker_T_F11_pow_eleven_eq_top, inf_top_eq]

/-- **Phase D-B main relation** for V_7: `dim V_7 + 9 * a_F11_7 = 10 * g_7(2)`.
すなわち `g_7(11) + 9 g_7(1) = 10 g_7(2)` (linearity at j = 11 via telescoping). -/
private theorem dim_V7_plus_9_aF11_seven_eq_10_g2
    (h : Order22ActsOnMoore57 V Γ) :
    Module.finrank (ZMod 11) (V7Submodule Γ) +
      9 * Module.finrank (ZMod 11)
        (V7Submodule Γ ⊓ LinearMap.ker ((T_F11 h)^1) :
          Submodule (ZMod 11) (V → ZMod 11)) =
    10 * Module.finrank (ZMod 11)
        (V7Submodule Γ ⊓ LinearMap.ker ((T_F11 h)^2) :
          Submodule (ZMod 11) (V → ZMod 11)) := by
  -- 線形性 g(j+1) - g(j) = g(2) - g(1) を ℤ で取り扱う.
  set g : ℕ → ℤ := fun j =>
    (Module.finrank (ZMod 11) (V7Submodule Γ ⊓ LinearMap.ker ((T_F11 h)^j) :
        Submodule (ZMod 11) (V → ZMod 11)) : ℤ) with hg_def
  have h_lin : ∀ {j : ℕ}, 1 ≤ j → j ≤ 10 → g (j+1) + g 1 = g j + g 2 := by
    intro j hj_ge hj_le
    have := g_V7_linear_add_form h hj_ge hj_le
    push_cast [hg_def]
    exact_mod_cast this
  have h_dim : g 11 = (Module.finrank (ZMod 11) (V7Submodule Γ) : ℤ) := by
    push_cast [hg_def]
    exact_mod_cast g_V7_eleven_eq_dim h
  -- Telescope: g 11 = g 1 + 10 * (g 2 - g 1) = 10 g 2 - 9 g 1.
  have h_telescope : g 11 = 10 * g 2 - 9 * g 1 := by
    have h10 := h_lin (show 1 ≤ 10 from by omega) (show 10 ≤ 10 from by omega)
    have h9 := h_lin (show 1 ≤ 9 from by omega) (show 9 ≤ 10 from by omega)
    have h8 := h_lin (show 1 ≤ 8 from by omega) (show 8 ≤ 10 from by omega)
    have h7 := h_lin (show 1 ≤ 7 from by omega) (show 7 ≤ 10 from by omega)
    have h6 := h_lin (show 1 ≤ 6 from by omega) (show 6 ≤ 10 from by omega)
    have h5 := h_lin (show 1 ≤ 5 from by omega) (show 5 ≤ 10 from by omega)
    have h4 := h_lin (show 1 ≤ 4 from by omega) (show 4 ≤ 10 from by omega)
    have h3 := h_lin (show 1 ≤ 3 from by omega) (show 3 ≤ 10 from by omega)
    have h2 := h_lin (show 1 ≤ 2 from by omega) (show 2 ≤ 10 from by omega)
    have h1 := h_lin (show 1 ≤ 1 from by omega) (show 1 ≤ 10 from by omega)
    linarith
  rw [h_dim] at h_telescope
  -- h_telescope: dim V_7 (cast) = 10 g 2 - 9 g 1.
  have h_add : (Module.finrank (ZMod 11) (V7Submodule Γ) : ℤ) +
      9 * g 1 = 10 * g 2 := by linarith
  simp only [hg_def] at h_add
  exact_mod_cast h_add

private theorem dim_V2_plus_9_aF11_two_eq_10_g2
    (h : Order22ActsOnMoore57 V Γ) :
    Module.finrank (ZMod 11) (V2Submodule Γ) +
      9 * Module.finrank (ZMod 11)
        (V2Submodule Γ ⊓ LinearMap.ker ((T_F11 h)^1) :
          Submodule (ZMod 11) (V → ZMod 11)) =
    10 * Module.finrank (ZMod 11)
        (V2Submodule Γ ⊓ LinearMap.ker ((T_F11 h)^2) :
          Submodule (ZMod 11) (V → ZMod 11)) := by
  set g : ℕ → ℤ := fun j =>
    (Module.finrank (ZMod 11) (V2Submodule Γ ⊓ LinearMap.ker ((T_F11 h)^j) :
        Submodule (ZMod 11) (V → ZMod 11)) : ℤ) with hg_def
  have h_lin : ∀ {j : ℕ}, 1 ≤ j → j ≤ 10 → g (j+1) + g 1 = g j + g 2 := by
    intro j hj_ge hj_le
    have := g_V2_linear_add_form h hj_ge hj_le
    push_cast [hg_def]
    exact_mod_cast this
  have h_dim : g 11 = (Module.finrank (ZMod 11) (V2Submodule Γ) : ℤ) := by
    push_cast [hg_def]
    exact_mod_cast g_V2_eleven_eq_dim h
  have h_telescope : g 11 = 10 * g 2 - 9 * g 1 := by
    have h10 := h_lin (show 1 ≤ 10 from by omega) (show 10 ≤ 10 from by omega)
    have h9 := h_lin (show 1 ≤ 9 from by omega) (show 9 ≤ 10 from by omega)
    have h8 := h_lin (show 1 ≤ 8 from by omega) (show 8 ≤ 10 from by omega)
    have h7 := h_lin (show 1 ≤ 7 from by omega) (show 7 ≤ 10 from by omega)
    have h6 := h_lin (show 1 ≤ 6 from by omega) (show 6 ≤ 10 from by omega)
    have h5 := h_lin (show 1 ≤ 5 from by omega) (show 5 ≤ 10 from by omega)
    have h4 := h_lin (show 1 ≤ 4 from by omega) (show 4 ≤ 10 from by omega)
    have h3 := h_lin (show 1 ≤ 3 from by omega) (show 3 ≤ 10 from by omega)
    have h2 := h_lin (show 1 ≤ 2 from by omega) (show 2 ≤ 10 from by omega)
    have h1 := h_lin (show 1 ≤ 1 from by omega) (show 1 ≤ 10 from by omega)
    linarith
  rw [h_dim] at h_telescope
  have h_add : (Module.finrank (ZMod 11) (V2Submodule Γ) : ℤ) +
      9 * g 1 = 10 * g 2 := by linarith
  simp only [hg_def] at h_add
  exact_mod_cast h_add

private theorem dim_V3_plus_9_aF11_three_eq_10_g2
    (h : Order22ActsOnMoore57 V Γ) :
    Module.finrank (ZMod 11) (V3Submodule Γ) +
      9 * Module.finrank (ZMod 11)
        (V3Submodule Γ ⊓ LinearMap.ker ((T_F11 h)^1) :
          Submodule (ZMod 11) (V → ZMod 11)) =
    10 * Module.finrank (ZMod 11)
        (V3Submodule Γ ⊓ LinearMap.ker ((T_F11 h)^2) :
          Submodule (ZMod 11) (V → ZMod 11)) := by
  set g : ℕ → ℤ := fun j =>
    (Module.finrank (ZMod 11) (V3Submodule Γ ⊓ LinearMap.ker ((T_F11 h)^j) :
        Submodule (ZMod 11) (V → ZMod 11)) : ℤ) with hg_def
  have h_lin : ∀ {j : ℕ}, 1 ≤ j → j ≤ 10 → g (j+1) + g 1 = g j + g 2 := by
    intro j hj_ge hj_le
    have := g_V3_linear_add_form h hj_ge hj_le
    push_cast [hg_def]
    exact_mod_cast this
  have h_dim : g 11 = (Module.finrank (ZMod 11) (V3Submodule Γ) : ℤ) := by
    push_cast [hg_def]
    exact_mod_cast g_V3_eleven_eq_dim h
  have h_telescope : g 11 = 10 * g 2 - 9 * g 1 := by
    have h10 := h_lin (show 1 ≤ 10 from by omega) (show 10 ≤ 10 from by omega)
    have h9 := h_lin (show 1 ≤ 9 from by omega) (show 9 ≤ 10 from by omega)
    have h8 := h_lin (show 1 ≤ 8 from by omega) (show 8 ≤ 10 from by omega)
    have h7 := h_lin (show 1 ≤ 7 from by omega) (show 7 ≤ 10 from by omega)
    have h6 := h_lin (show 1 ≤ 6 from by omega) (show 6 ≤ 10 from by omega)
    have h5 := h_lin (show 1 ≤ 5 from by omega) (show 5 ≤ 10 from by omega)
    have h4 := h_lin (show 1 ≤ 4 from by omega) (show 4 ≤ 10 from by omega)
    have h3 := h_lin (show 1 ≤ 3 from by omega) (show 3 ≤ 10 from by omega)
    have h2 := h_lin (show 1 ≤ 2 from by omega) (show 2 ≤ 10 from by omega)
    have h1 := h_lin (show 1 ≤ 1 from by omega) (show 1 ≤ 10 from by omega)
    linarith
  rw [h_dim] at h_telescope
  have h_add : (Module.finrank (ZMod 11) (V3Submodule Γ) : ℤ) +
      9 * g 1 = 10 * g 2 := by linarith
  simp only [hg_def] at h_add
  exact_mod_cast h_add

/-! ### Phase D-A: Σ dim V_λ = 3250 (V_F_11 direct sum) -/

/-- `(V_2 ⊔ V_7) ⊓ V_3 = ⊥` (orthogonality of E_λ). -/
private theorem V2_sup_V7_inter_V3_eq_bot (h : Order22ActsOnMoore57 V Γ) :
    (V2Submodule Γ ⊔ V7Submodule Γ) ⊓ V3Submodule Γ =
    (⊥ : Submodule (ZMod 11) (V → ZMod 11)) := by
  classical
  apply le_antisymm _ bot_le
  intro v hv
  rw [Submodule.mem_inf] at hv
  obtain ⟨h_sup, hv_3⟩ := hv
  rw [Submodule.mem_sup] at h_sup
  obtain ⟨w_2, hw_2, w_7, hw_7, h_sum⟩ := h_sup
  obtain ⟨u_3, hu_3⟩ := LinearMap.mem_range.mp hv_3
  obtain ⟨u_2, hu_2⟩ := LinearMap.mem_range.mp hw_2
  obtain ⟨u_7, hu_7⟩ := LinearMap.mem_range.mp hw_7
  have h_E3v_eq_v : (E3MatrixF11 Γ).toLin' v = v := by
    rw [← hu_3]
    show (E3MatrixF11 Γ).toLin' ((E3MatrixF11 Γ).toLin' u_3) = (E3MatrixF11 Γ).toLin' u_3
    rw [show (E3MatrixF11 Γ).toLin' ((E3MatrixF11 Γ).toLin' u_3) =
            (E3MatrixF11 Γ * E3MatrixF11 Γ).toLin' u_3 from by
          rw [Matrix.toLin'_mul]; rfl,
        E3_idempotent h.isMoore]
  have h_E3v_eq_zero : (E3MatrixF11 Γ).toLin' v = 0 := by
    rw [← h_sum, map_add, ← hu_2, ← hu_7]
    show (E3MatrixF11 Γ).toLin' ((E2MatrixF11 Γ).toLin' u_2) +
         (E3MatrixF11 Γ).toLin' ((E7MatrixF11 Γ).toLin' u_7) = 0
    rw [show (E3MatrixF11 Γ).toLin' ((E2MatrixF11 Γ).toLin' u_2) =
            (E3MatrixF11 Γ * E2MatrixF11 Γ).toLin' u_2 from by
          rw [Matrix.toLin'_mul]; rfl,
        show (E3MatrixF11 Γ).toLin' ((E7MatrixF11 Γ).toLin' u_7) =
            (E3MatrixF11 Γ * E7MatrixF11 Γ).toLin' u_7 from by
          rw [Matrix.toLin'_mul]; rfl,
        E3_mul_E2_eq_zero h.isMoore, E3_mul_E7_eq_zero h.isMoore]
    show (0 : Matrix V V (ZMod 11)).toLin' u_2 +
         (0 : Matrix V V (ZMod 11)).toLin' u_7 = 0
    simp
  rw [Submodule.mem_bot]
  exact h_E3v_eq_v.symm.trans h_E3v_eq_zero

/-- Σ_λ dim V_λ = 3250 over F_11. -/
theorem finrank_sum_V_lambda_eq_3250 (h : Order22ActsOnMoore57 V Γ) :
    Module.finrank (ZMod 11) (V2Submodule Γ) +
      Module.finrank (ZMod 11) (V7Submodule Γ) +
      Module.finrank (ZMod 11) (V3Submodule Γ) =
    Module.finrank (ZMod 11) (V → ZMod 11) := by
  classical
  haveI : FiniteDimensional (ZMod 11) (V → ZMod 11) := by infer_instance
  set S_2 := V2Submodule Γ with hS2_def
  set S_7 := V7Submodule Γ with hS7_def
  set S_3 := V3Submodule Γ with hS3_def
  have h_sup_eq : (S_2 ⊔ S_7) ⊔ S_3 = ⊤ := V2_sup_V7_sup_V3_eq_top
  have h_27_3_disj : (S_2 ⊔ S_7) ⊓ S_3 = ⊥ := V2_sup_V7_inter_V3_eq_bot h
  have h_27_disj : S_2 ⊓ S_7 = ⊥ := V2_inter_V7_eq_bot h.isMoore
  have h_27_3_finrank : Module.finrank (ZMod 11) ↥((S_2 ⊔ S_7) ⊔ S_3) =
      Module.finrank (ZMod 11) ↥(S_2 ⊔ S_7) + Module.finrank (ZMod 11) ↥S_3 := by
    have h_eq := Submodule.finrank_sup_add_finrank_inf_eq (S_2 ⊔ S_7) S_3
    rw [h_27_3_disj, finrank_bot] at h_eq
    omega
  have h_27_finrank : Module.finrank (ZMod 11) ↥(S_2 ⊔ S_7) =
      Module.finrank (ZMod 11) ↥S_2 + Module.finrank (ZMod 11) ↥S_7 := by
    have h_eq := Submodule.finrank_sup_add_finrank_inf_eq S_2 S_7
    rw [h_27_disj, finrank_bot] at h_eq
    omega
  rw [h_sup_eq, finrank_top] at h_27_3_finrank
  omega

/-- `Σ_λ dim V_λ = 3250` (整数値版). -/
theorem finrank_sum_V_lambda_eq_card_V (h : Order22ActsOnMoore57 V Γ) :
    Module.finrank (ZMod 11) (V2Submodule Γ) +
      Module.finrank (ZMod 11) (V7Submodule Γ) +
      Module.finrank (ZMod 11) (V3Submodule Γ) = 3250 := by
  rw [finrank_sum_V_lambda_eq_3250 h]
  rw [show Module.finrank (ZMod 11) (V → ZMod 11) = Fintype.card V from by
    rw [Module.finrank_fintype_fun_eq_card]]
  exact h.isMoore.card

/-! ### ker T_F11 = ⊕_λ (V_λ ⊓ ker T_F11): direct sum decomposition

dim V_λ ∩ ker T_F11 を a^{F_11}_λ と表記.
Σ a^{F_11}_λ = dim ker T_F11 = 300 を導出. -/

/-- `ker T_F11 = (V_2 ⊓ ker T) ⊔ (V_7 ⊓ ker T) ⊔ (V_3 ⊓ ker T)`. -/
theorem ker_T_F11_eq_sup_three (h : Order22ActsOnMoore57 V Γ) :
    (V2Submodule Γ ⊓ LinearMap.ker (T_F11 h)) ⊔
      (V7Submodule Γ ⊓ LinearMap.ker (T_F11 h)) ⊔
      (V3Submodule Γ ⊓ LinearMap.ker (T_F11 h)) =
    LinearMap.ker (T_F11 h) := by
  classical
  apply le_antisymm
  · -- sup ≤ ker T
    refine sup_le (sup_le inf_le_right inf_le_right) inf_le_right
  · -- ker T ≤ sup
    intro v hv
    rw [Submodule.mem_sup]
    refine ⟨(E2MatrixF11 Γ).toLin' v + (E7MatrixF11 Γ).toLin' v, ?_,
            (E3MatrixF11 Γ).toLin' v, ?_, ELambda_sum_apply v⟩
    · -- E_2 v + E_7 v ∈ (V_2 ⊓ ker T) ⊔ (V_7 ⊓ ker T)
      rw [Submodule.mem_sup]
      refine ⟨(E2MatrixF11 Γ).toLin' v, ?_, (E7MatrixF11 Γ).toLin' v, ?_, rfl⟩
      · exact Submodule.mem_inf.mpr
          ⟨LinearMap.mem_range.mpr ⟨v, rfl⟩, E2_preserves_ker_T_F11 h v hv⟩
      · exact Submodule.mem_inf.mpr
          ⟨LinearMap.mem_range.mpr ⟨v, rfl⟩, E7_preserves_ker_T_F11 h v hv⟩
    · -- E_3 v ∈ V_3 ⊓ ker T
      exact Submodule.mem_inf.mpr
        ⟨LinearMap.mem_range.mpr ⟨v, rfl⟩, E3_preserves_ker_T_F11 h v hv⟩

/-- V_λ ⊓ ker T と V_μ ⊓ ker T は disjoint (V_λ ⊓ V_μ = ⊥ から). -/
private theorem V2kt_inter_V7kt_eq_bot (h : Order22ActsOnMoore57 V Γ) :
    (V2Submodule Γ ⊓ LinearMap.ker (T_F11 h)) ⊓
      (V7Submodule Γ ⊓ LinearMap.ker (T_F11 h)) =
    (⊥ : Submodule (ZMod 11) (V → ZMod 11)) := by
  classical
  apply le_antisymm _ bot_le
  intro v hv
  rw [Submodule.mem_inf] at hv
  obtain ⟨hv_2, hv_7⟩ := hv
  rw [Submodule.mem_inf] at hv_2 hv_7
  have h_in : v ∈ V2Submodule Γ ⊓ V7Submodule Γ :=
    Submodule.mem_inf.mpr ⟨hv_2.1, hv_7.1⟩
  rw [V2_inter_V7_eq_bot h.isMoore] at h_in
  exact h_in

private theorem V2kt_inter_V3kt_eq_bot (h : Order22ActsOnMoore57 V Γ) :
    (V2Submodule Γ ⊓ LinearMap.ker (T_F11 h)) ⊓
      (V3Submodule Γ ⊓ LinearMap.ker (T_F11 h)) =
    (⊥ : Submodule (ZMod 11) (V → ZMod 11)) := by
  classical
  apply le_antisymm _ bot_le
  intro v hv
  rw [Submodule.mem_inf] at hv
  obtain ⟨hv_2, hv_3⟩ := hv
  rw [Submodule.mem_inf] at hv_2 hv_3
  have h_in : v ∈ V2Submodule Γ ⊓ V3Submodule Γ :=
    Submodule.mem_inf.mpr ⟨hv_2.1, hv_3.1⟩
  rw [V2_inter_V3_eq_bot h.isMoore] at h_in
  exact h_in

private theorem V7kt_inter_V3kt_eq_bot (h : Order22ActsOnMoore57 V Γ) :
    (V7Submodule Γ ⊓ LinearMap.ker (T_F11 h)) ⊓
      (V3Submodule Γ ⊓ LinearMap.ker (T_F11 h)) =
    (⊥ : Submodule (ZMod 11) (V → ZMod 11)) := by
  classical
  apply le_antisymm _ bot_le
  intro v hv
  rw [Submodule.mem_inf] at hv
  obtain ⟨hv_7, hv_3⟩ := hv
  rw [Submodule.mem_inf] at hv_7 hv_3
  have h_in : v ∈ V7Submodule Γ ⊓ V3Submodule Γ :=
    Submodule.mem_inf.mpr ⟨hv_7.1, hv_3.1⟩
  rw [V7_inter_V3_eq_bot h.isMoore] at h_in
  exact h_in

/-- `((V_2 ⊓ ker T) ⊔ (V_7 ⊓ ker T)) ⊓ (V_3 ⊓ ker T) = ⊥`. -/
private theorem V2kt_sup_V7kt_inter_V3kt_eq_bot (h : Order22ActsOnMoore57 V Γ) :
    ((V2Submodule Γ ⊓ LinearMap.ker (T_F11 h)) ⊔
       (V7Submodule Γ ⊓ LinearMap.ker (T_F11 h))) ⊓
      (V3Submodule Γ ⊓ LinearMap.ker (T_F11 h)) =
    (⊥ : Submodule (ZMod 11) (V → ZMod 11)) := by
  classical
  apply le_antisymm _ bot_le
  intro v hv
  rw [Submodule.mem_inf] at hv
  obtain ⟨h_sup, hv_3⟩ := hv
  rw [Submodule.mem_sup] at h_sup
  obtain ⟨w_2, hw_2, w_7, hw_7, h_sum⟩ := h_sup
  rw [Submodule.mem_inf] at hw_2 hw_7 hv_3
  -- E_3 v = v (v ∈ V_3 idem), E_3 v = E_3 w_2 + E_3 w_7 = 0 + 0 = 0 (orth).
  obtain ⟨u_3, hu_3⟩ := LinearMap.mem_range.mp hv_3.1
  obtain ⟨u_2, hu_2⟩ := LinearMap.mem_range.mp hw_2.1
  obtain ⟨u_7, hu_7⟩ := LinearMap.mem_range.mp hw_7.1
  have h_E3v_eq_v : (E3MatrixF11 Γ).toLin' v = v := by
    rw [← hu_3]
    show (E3MatrixF11 Γ).toLin' ((E3MatrixF11 Γ).toLin' u_3) = (E3MatrixF11 Γ).toLin' u_3
    rw [show (E3MatrixF11 Γ).toLin' ((E3MatrixF11 Γ).toLin' u_3) =
            (E3MatrixF11 Γ * E3MatrixF11 Γ).toLin' u_3 from by
          rw [Matrix.toLin'_mul]; rfl,
        E3_idempotent h.isMoore]
  have h_E3v_eq_zero : (E3MatrixF11 Γ).toLin' v = 0 := by
    rw [← h_sum, map_add, ← hu_2, ← hu_7]
    show (E3MatrixF11 Γ).toLin' ((E2MatrixF11 Γ).toLin' u_2) +
         (E3MatrixF11 Γ).toLin' ((E7MatrixF11 Γ).toLin' u_7) = 0
    rw [show (E3MatrixF11 Γ).toLin' ((E2MatrixF11 Γ).toLin' u_2) =
            (E3MatrixF11 Γ * E2MatrixF11 Γ).toLin' u_2 from by
          rw [Matrix.toLin'_mul]; rfl,
        show (E3MatrixF11 Γ).toLin' ((E7MatrixF11 Γ).toLin' u_7) =
            (E3MatrixF11 Γ * E7MatrixF11 Γ).toLin' u_7 from by
          rw [Matrix.toLin'_mul]; rfl,
        E3_mul_E2_eq_zero h.isMoore, E3_mul_E7_eq_zero h.isMoore]
    show (0 : Matrix V V (ZMod 11)).toLin' u_2 +
         (0 : Matrix V V (ZMod 11)).toLin' u_7 = 0
    simp
  rw [Submodule.mem_bot]
  exact h_E3v_eq_v.symm.trans h_E3v_eq_zero

/-- 行列レベル: E が P_σ と可換なら, (P_σ - 1)^10 と E も可換. -/
private theorem _matrix_pow_ten_commute_of_commute
    (E : Matrix V V (ZMod 11)) (σ : Equiv.Perm V)
    (hE : E * permMatrixF11 σ = permMatrixF11 σ * E) :
    (permMatrixF11 σ - 1)^10 * E = E * (permMatrixF11 σ - 1)^10 := by
  have h_mat_comm : Commute (permMatrixF11 σ - 1) E := by
    show (permMatrixF11 σ - 1) * E = E * (permMatrixF11 σ - 1)
    rw [sub_mul, one_mul, mul_sub, mul_one, hE]
  exact (h_mat_comm.pow_left 10).eq

/-- V_λ (= range E) は T_F11^10 で安定. -/
theorem T_F11_pow_ten_preserves_V_lambda
    (h : Order22ActsOnMoore57 V Γ)
    (E : Matrix V V (ZMod 11))
    (hE : E * permMatrixF11 h.σ = permMatrixF11 h.σ * E) :
    ∀ v ∈ E.toLin'.range, ((T_F11 h)^10) v ∈ E.toLin'.range := by
  intro v hv
  obtain ⟨u, hu⟩ := LinearMap.mem_range.mp hv
  rw [LinearMap.mem_range]
  refine ⟨((T_F11 h)^10) u, ?_⟩
  rw [← hu]
  -- Goal: E.toLin' (T^10 u) = T^10 (E.toLin' u)
  have h_pow_mat : (T_F11 h)^10 = ((permMatrixF11 h.σ - 1)^10).toLin' := by
    rw [T_F11_def, ← Matrix.toLin'_pow]
  rw [h_pow_mat]
  -- Goal: E.toLin' (((P-1)^10).toLin' u) = ((P-1)^10).toLin' (E.toLin' u)
  have hMM : (E * (permMatrixF11 h.σ - 1)^10).toLin' u =
             E.toLin' (((permMatrixF11 h.σ - 1)^10).toLin' u) := by
    rw [Matrix.toLin'_mul]; rfl
  have hNN : ((permMatrixF11 h.σ - 1)^10 * E).toLin' u =
             ((permMatrixF11 h.σ - 1)^10).toLin' (E.toLin' u) := by
    rw [Matrix.toLin'_mul]; rfl
  rw [← hMM, ← hNN, _matrix_pow_ten_commute_of_commute E h.σ hE]

/-- 一般形 helper: T v = 0 ⟹ (T^n) v = 0 for n ≥ 1. -/
private theorem _pow_apply_eq_zero
    {M : Type*} [AddCommGroup M] [Module (ZMod 11) M]
    (T : M →ₗ[ZMod 11] M) (v : M) (h : T v = 0) :
    ∀ n : ℕ, n ≥ 1 → (T^n) v = 0 := by
  intro n hn
  induction n with
  | zero => omega
  | succ k ih =>
    by_cases hk : k = 0
    · subst hk; rw [pow_one]; exact h
    · have hk_pos : k ≥ 1 := Nat.one_le_iff_ne_zero.mpr hk
      have h_ih := ih hk_pos
      rw [pow_succ]
      show (T^k * T) v = 0
      change (T^k) (T v) = 0
      rw [h, map_zero]

/-- V_2 ⊆ ker T_F11 ⟹ T_F11^10 V_2 = 0. -/
theorem T_F11_pow_ten_V2_eq_zero (h : Order22ActsOnMoore57 V Γ) :
    ∀ v ∈ V2Submodule Γ, ((T_F11 h)^10) v = 0 := by
  intro v hv
  have h_ker : v ∈ LinearMap.ker (T_F11 h) := V2Submodule_le_ker_T_F11 h hv
  rw [LinearMap.mem_ker] at h_ker
  exact _pow_apply_eq_zero (T_F11 h) v h_ker 10 (by norm_num)

/-- E と T_F11^10 が可換 (P_σ-commute + Commute.pow_left). -/
private theorem _E_preserves_range_T_F11_pow_ten
    (h : Order22ActsOnMoore57 V Γ)
    (E : Matrix V V (ZMod 11))
    (hE : E * permMatrixF11 h.σ = permMatrixF11 h.σ * E) :
    ∀ v ∈ LinearMap.range ((T_F11 h)^10), E.toLin' v ∈ LinearMap.range ((T_F11 h)^10) := by
  intro v hv
  obtain ⟨u, hu⟩ := LinearMap.mem_range.mp hv
  refine LinearMap.mem_range.mpr ⟨E.toLin' u, ?_⟩
  rw [← hu]
  have h_pow_mat : (T_F11 h)^10 = ((permMatrixF11 h.σ - 1)^10).toLin' := by
    rw [T_F11_def, ← Matrix.toLin'_pow]
  rw [h_pow_mat]
  have hMM : (((permMatrixF11 h.σ - 1)^10) * E).toLin' u =
             ((permMatrixF11 h.σ - 1)^10).toLin' (E.toLin' u) := by
    rw [Matrix.toLin'_mul]; rfl
  have hNN : (E * (permMatrixF11 h.σ - 1)^10).toLin' u =
             E.toLin' (((permMatrixF11 h.σ - 1)^10).toLin' u) := by
    rw [Matrix.toLin'_mul]; rfl
  rw [← hMM, _matrix_pow_ten_commute_of_commute E h.σ hE, hNN]

/-- `Im T_F11^10 ⊆ (V_7 ⊓ Im T_F11^10) ⊔ (V_3 ⊓ Im T_F11^10)`:
V_2 ⊆ ker T_F11 ⟹ V_2 部分は 0. -/
theorem range_T_F11_pow_ten_eq_sup_two (h : Order22ActsOnMoore57 V Γ) :
    (V7Submodule Γ ⊓ LinearMap.range ((T_F11 h)^10)) ⊔
      (V3Submodule Γ ⊓ LinearMap.range ((T_F11 h)^10)) =
    LinearMap.range ((T_F11 h)^10) := by
  classical
  apply le_antisymm
  · refine sup_le inf_le_right inf_le_right
  · intro v hv
    -- E_2 v ∈ V_2 ∩ Im T^10. We show E_2 v = 0 (since V_2 ⊆ ker T, T^10 V_2 = 0).
    obtain ⟨u, hu⟩ := LinearMap.mem_range.mp hv
    have h_E2v_in_V2 : (E2MatrixF11 Γ).toLin' v ∈ V2Submodule Γ :=
      LinearMap.mem_range.mpr ⟨v, rfl⟩
    have h_E2v_in_range : (E2MatrixF11 Γ).toLin' v ∈ LinearMap.range ((T_F11 h)^10) :=
      _E_preserves_range_T_F11_pow_ten h (E2MatrixF11 Γ)
        (E2_commute_permMatrixF11 h.isMoore h.σ) v hv
    have h_E2v_zero : (E2MatrixF11 Γ).toLin' v = 0 := by
      -- E_2 v ∈ V_2 ∩ Im T^10. But V_2 ⊓ Im T^10 ⊆ V_2 ⊓ ker T (via Im T^10 ⊆ ker T).
      -- And V_2 ∩ ker T = V_2 (since V_2 ⊆ ker T). So E_2 v ∈ V_2.
      -- Now E_2 v is also in Im T^10, so E_2 v = T^10 w for some w.
      -- Apply T^10 to E_2 v: T^10 (E_2 v) = 0 (since V_2 ⊆ ker T).
      -- But E_2 v ∈ Im T^10 means E_2 v = T^10 w. So E_2 v = T^10 w and T^10 (E_2 v) = 0.
      -- This doesn't directly give E_2 v = 0 without more work.
      -- Alternative direct approach: E_2 v = E_2 (T^10 u) = T^10 (E_2 u). E_2 u ∈ V_2, so T^10 (E_2 u) = 0.
      rw [← hu]
      have h_E2u_in_V2 : (E2MatrixF11 Γ).toLin' u ∈ V2Submodule Γ :=
        LinearMap.mem_range.mpr ⟨u, rfl⟩
      have h_T10_E2u_zero : ((T_F11 h)^10) ((E2MatrixF11 Γ).toLin' u) = 0 :=
        T_F11_pow_ten_V2_eq_zero h _ h_E2u_in_V2
      -- E_2 (T^10 u) = T^10 (E_2 u) via commute (matrix-level).
      have h_pow_mat : (T_F11 h)^10 = ((permMatrixF11 h.σ - 1)^10).toLin' := by
        rw [T_F11_def, ← Matrix.toLin'_pow]
      have h_comm : (E2MatrixF11 Γ).toLin' (((T_F11 h)^10) u) =
                    ((T_F11 h)^10) ((E2MatrixF11 Γ).toLin' u) := by
        rw [h_pow_mat]
        have hMM : (E2MatrixF11 Γ * (permMatrixF11 h.σ - 1)^10).toLin' u =
                   (E2MatrixF11 Γ).toLin' (((permMatrixF11 h.σ - 1)^10).toLin' u) := by
          rw [Matrix.toLin'_mul]; rfl
        have hNN : (((permMatrixF11 h.σ - 1)^10) * E2MatrixF11 Γ).toLin' u =
                   ((permMatrixF11 h.σ - 1)^10).toLin' ((E2MatrixF11 Γ).toLin' u) := by
          rw [Matrix.toLin'_mul]; rfl
        rw [← hMM, ← _matrix_pow_ten_commute_of_commute (E2MatrixF11 Γ) h.σ
            (E2_commute_permMatrixF11 h.isMoore h.σ), hNN]
      rw [h_comm, h_T10_E2u_zero]
    rw [Submodule.mem_sup]
    refine ⟨(E7MatrixF11 Γ).toLin' v, ?_, (E3MatrixF11 Γ).toLin' v, ?_, ?_⟩
    · exact Submodule.mem_inf.mpr ⟨LinearMap.mem_range.mpr ⟨v, rfl⟩,
        _E_preserves_range_T_F11_pow_ten h (E7MatrixF11 Γ)
          (E7_commute_permMatrixF11 h.isMoore h.σ h.σ_aut) v hv⟩
    · exact Submodule.mem_inf.mpr ⟨LinearMap.mem_range.mpr ⟨v, rfl⟩,
        _E_preserves_range_T_F11_pow_ten h (E3MatrixF11 Γ)
          (E3_commute_permMatrixF11 h.isMoore h.σ h.σ_aut) v hv⟩
    · have h_sum := ELambda_sum_apply (Γ := Γ) v
      rw [h_E2v_zero, zero_add] at h_sum
      exact h_sum

/-- `V_2 ⊓ Im T_F11^10 = ⊥`: V_2 ⊆ ker T_F11 から T^10 を作用させると 0. -/
theorem V2_inter_range_T_F11_pow_ten_eq_bot (h : Order22ActsOnMoore57 V Γ) :
    V2Submodule Γ ⊓ LinearMap.range ((T_F11 h)^10) =
    (⊥ : Submodule (ZMod 11) (V → ZMod 11)) := by
  classical
  apply le_antisymm _ bot_le
  intro v hv
  rw [Submodule.mem_inf] at hv
  obtain ⟨hv_V2, hv_range⟩ := hv
  -- v = E_2 v (since v ∈ V_2 = Im E_2 + E_2 idempotent on its image)
  obtain ⟨u, hu⟩ := LinearMap.mem_range.mp hv_V2
  have h_E2v : (E2MatrixF11 Γ).toLin' v = v := by
    rw [← hu]
    show (E2MatrixF11 Γ).toLin' ((E2MatrixF11 Γ).toLin' u) = (E2MatrixF11 Γ).toLin' u
    rw [show (E2MatrixF11 Γ).toLin' ((E2MatrixF11 Γ).toLin' u) =
          (E2MatrixF11 Γ * E2MatrixF11 Γ).toLin' u from by
          rw [Matrix.toLin'_mul]; rfl,
        E2_idempotent h.isMoore]
  -- v ∈ Im T^10 ⟹ v = T^10 w for some w
  obtain ⟨w, hw⟩ := LinearMap.mem_range.mp hv_range
  -- E_2 v = E_2 (T^10 w) = T^10 (E_2 w). E_2 w ∈ V_2 ⊆ ker T ⟹ T^10 (E_2 w) = 0.
  have h_E2_T10_w_zero : ((T_F11 h)^10) ((E2MatrixF11 Γ).toLin' w) = 0 :=
    T_F11_pow_ten_V2_eq_zero h _ (LinearMap.mem_range.mpr ⟨w, rfl⟩)
  have h_E2v_eq_zero : (E2MatrixF11 Γ).toLin' v = 0 := by
    rw [← hw]
    -- E_2 (T^10 w) = T^10 (E_2 w) via commute.
    have h_pow_mat : (T_F11 h)^10 = ((permMatrixF11 h.σ - 1)^10).toLin' := by
      rw [T_F11_def, ← Matrix.toLin'_pow]
    rw [h_pow_mat]
    have hMM : (E2MatrixF11 Γ * (permMatrixF11 h.σ - 1)^10).toLin' w =
               (E2MatrixF11 Γ).toLin' (((permMatrixF11 h.σ - 1)^10).toLin' w) := by
      rw [Matrix.toLin'_mul]; rfl
    have hNN : (((permMatrixF11 h.σ - 1)^10) * E2MatrixF11 Γ).toLin' w =
               ((permMatrixF11 h.σ - 1)^10).toLin' ((E2MatrixF11 Γ).toLin' w) := by
      rw [Matrix.toLin'_mul]; rfl
    rw [← hMM, ← _matrix_pow_ten_commute_of_commute (E2MatrixF11 Γ) h.σ
        (E2_commute_permMatrixF11 h.isMoore h.σ), hNN]
    rw [← h_pow_mat]
    exact h_E2_T10_w_zero
  rw [Submodule.mem_bot]
  exact h_E2v.symm.trans h_E2v_eq_zero

/-- (V_7 ⊓ Im T^10) ⊓ (V_3 ⊓ Im T^10) = ⊥. -/
private theorem V7range_inter_V3range_eq_bot (h : Order22ActsOnMoore57 V Γ) :
    (V7Submodule Γ ⊓ LinearMap.range ((T_F11 h)^10)) ⊓
      (V3Submodule Γ ⊓ LinearMap.range ((T_F11 h)^10)) =
    (⊥ : Submodule (ZMod 11) (V → ZMod 11)) := by
  classical
  apply le_antisymm _ bot_le
  intro v hv
  rw [Submodule.mem_inf] at hv
  obtain ⟨hv_7, hv_3⟩ := hv
  rw [Submodule.mem_inf] at hv_7 hv_3
  have h_in : v ∈ V7Submodule Γ ⊓ V3Submodule Γ :=
    Submodule.mem_inf.mpr ⟨hv_7.1, hv_3.1⟩
  rw [V7_inter_V3_eq_bot h.isMoore] at h_in
  exact h_in

/-- `Im T_F11^10 ⊆ ker T_F11`: T^11 = 0 から T (T^10 v) = T^11 v = 0. -/
theorem range_T_F11_pow_ten_le_ker_T_F11 (h : Order22ActsOnMoore57 V Γ) :
    LinearMap.range ((T_F11 h)^10) ≤ LinearMap.ker (T_F11 h) := by
  intro v hv
  obtain ⟨u, hu⟩ := LinearMap.mem_range.mp hv
  rw [LinearMap.mem_ker, ← hu]
  show (T_F11 h) (((T_F11 h)^10) u) = 0
  -- T (T^10 u) = T^11 u via pow_succ', and T^11 = 0.
  have h_split : (T_F11 h) (((T_F11 h)^10) u) = ((T_F11 h)^11) u := by
    show ((T_F11 h) * ((T_F11 h)^10)) u = ((T_F11 h)^11) u
    rw [show ((T_F11 h) * ((T_F11 h)^10)) = ((T_F11 h)^11) from
        (pow_succ' (T_F11 h) 10).symm]
  rw [h_split]
  show ((T_F11 h)^11) u = 0
  have h11 := h.T_F11_pow_eleven_eq_zero
  rw [h11]; rfl

/-- `V_λ ⊓ Im T^10 ⊆ V_λ ⊓ ker T` (Im T^10 ⊆ ker T から). -/
theorem V_lambda_inter_range_le_V_lambda_inter_ker
    (h : Order22ActsOnMoore57 V Γ) (W : Submodule (ZMod 11) (V → ZMod 11)) :
    W ⊓ LinearMap.range ((T_F11 h)^10) ≤ W ⊓ LinearMap.ker (T_F11 h) := by
  exact inf_le_inf le_rfl h.range_T_F11_pow_ten_le_ker_T_F11

/-- **Σ k_λ = 295 (over ℕ via direct sum decomp of Im T^10 within V_7 ⊕ V_3)**. -/
theorem k_seven_plus_k_three_eq_295 (h : Order22ActsOnMoore57 V Γ) :
    Module.finrank (ZMod 11)
        (V7Submodule Γ ⊓ LinearMap.range ((T_F11 h)^10) :
          Submodule (ZMod 11) (V → ZMod 11)) +
      Module.finrank (ZMod 11)
        (V3Submodule Γ ⊓ LinearMap.range ((T_F11 h)^10) :
          Submodule (ZMod 11) (V → ZMod 11)) = 295 := by
  classical
  haveI : FiniteDimensional (ZMod 11) (V → ZMod 11) := by infer_instance
  set K_7 := V7Submodule Γ ⊓ LinearMap.range ((T_F11 h)^10) with hK7_def
  set K_3 := V3Submodule Γ ⊓ LinearMap.range ((T_F11 h)^10) with hK3_def
  have h_sup_eq : K_7 ⊔ K_3 = LinearMap.range ((T_F11 h)^10) :=
    h.range_T_F11_pow_ten_eq_sup_two
  have h_73_disj : K_7 ⊓ K_3 = ⊥ := h.V7range_inter_V3range_eq_bot
  have h_finrank : Module.finrank (ZMod 11) ↥(K_7 ⊔ K_3) =
      Module.finrank (ZMod 11) ↥K_7 + Module.finrank (ZMod 11) ↥K_3 := by
    have h_eq := Submodule.finrank_sup_add_finrank_inf_eq K_7 K_3
    rw [h_73_disj, finrank_bot] at h_eq
    omega
  rw [h_sup_eq] at h_finrank
  have h_range_dim : Module.finrank (ZMod 11) ↥(LinearMap.range ((T_F11 h)^10)) = 295 :=
    h.finrank_range_T_F11_pow_ten_eq_295
  omega

/-- **直和分解 dim 公式**:
`a^{F_11}_2 + a^{F_11}_7 + a^{F_11}_3 = 300`. -/
theorem aF11_sum_eq_300 (h : Order22ActsOnMoore57 V Γ) :
    Module.finrank (ZMod 11)
        (V2Submodule Γ ⊓ LinearMap.ker (T_F11 h) :
          Submodule (ZMod 11) (V → ZMod 11)) +
      Module.finrank (ZMod 11)
        (V7Submodule Γ ⊓ LinearMap.ker (T_F11 h) :
          Submodule (ZMod 11) (V → ZMod 11)) +
      Module.finrank (ZMod 11)
        (V3Submodule Γ ⊓ LinearMap.ker (T_F11 h) :
          Submodule (ZMod 11) (V → ZMod 11)) = 300 := by
  classical
  haveI : FiniteDimensional (ZMod 11) (V → ZMod 11) := by infer_instance
  set S_2 := V2Submodule Γ ⊓ LinearMap.ker (T_F11 h) with hS2_def
  set S_7 := V7Submodule Γ ⊓ LinearMap.ker (T_F11 h) with hS7_def
  set S_3 := V3Submodule Γ ⊓ LinearMap.ker (T_F11 h) with hS3_def
  -- (S_2 ⊔ S_7) + S_3 = ker T_F11.
  have h_sup_eq : (S_2 ⊔ S_7) ⊔ S_3 = LinearMap.ker (T_F11 h) :=
    h.ker_T_F11_eq_sup_three
  -- finrank((S_2 ⊔ S_7) ⊔ S_3) = finrank(S_2 ⊔ S_7) + finrank(S_3) (disjoint).
  have h_27_3_disj : (S_2 ⊔ S_7) ⊓ S_3 = ⊥ := h.V2kt_sup_V7kt_inter_V3kt_eq_bot
  have h_27_disj : S_2 ⊓ S_7 = ⊥ := h.V2kt_inter_V7kt_eq_bot
  have h_27_3_finrank : Module.finrank (ZMod 11) ↥((S_2 ⊔ S_7) ⊔ S_3) =
      Module.finrank (ZMod 11) ↥(S_2 ⊔ S_7) + Module.finrank (ZMod 11) ↥S_3 := by
    have h_eq := Submodule.finrank_sup_add_finrank_inf_eq (S_2 ⊔ S_7) S_3
    rw [h_27_3_disj, finrank_bot] at h_eq
    omega
  have h_27_finrank : Module.finrank (ZMod 11) ↥(S_2 ⊔ S_7) =
      Module.finrank (ZMod 11) ↥S_2 + Module.finrank (ZMod 11) ↥S_7 := by
    have h_eq := Submodule.finrank_sup_add_finrank_inf_eq S_2 S_7
    rw [h_27_disj, finrank_bot] at h_eq
    omega
  have h_ker_dim : Module.finrank (ZMod 11) ↥(LinearMap.ker (T_F11 h)) = 300 :=
    h.finrank_ker_T_F11_eq_300
  rw [← h_sup_eq] at h_ker_dim
  rw [h_27_3_finrank, h_27_finrank] at h_ker_dim
  omega

/-! ### A · E_λ = λ · E_λ: V_λ 上 A は scalar λ で作用

A = 2 E_2 + 7 E_7 + 3 E_3 + E_λ orthogonality + idempotency より導出. -/

/-- A · E_2 = 2 · E_2 (V_2 上 A は scalar 2). -/
theorem adjMatrixF11_mul_E2_eq_two_smul_E2 (hΓ : IsMoore57 Γ) :
    adjMatrixF11 Γ * E2MatrixF11 Γ = (2 : ZMod 11) • E2MatrixF11 Γ := by
  classical
  have h_decomp := ELambda_decomp_A (Γ := Γ)
  rw [← h_decomp, add_mul, add_mul, smul_mul_assoc, smul_mul_assoc, smul_mul_assoc,
      E2_idempotent hΓ, E7_mul_E2_eq_zero hΓ, E3_mul_E2_eq_zero hΓ,
      smul_zero, smul_zero, add_zero, add_zero]

/-- A · E_7 = 7 · E_7 (V_7 上 A は scalar 7). -/
theorem adjMatrixF11_mul_E7_eq_seven_smul_E7 (hΓ : IsMoore57 Γ) :
    adjMatrixF11 Γ * E7MatrixF11 Γ = (7 : ZMod 11) • E7MatrixF11 Γ := by
  classical
  have h_decomp := ELambda_decomp_A (Γ := Γ)
  rw [← h_decomp, add_mul, add_mul, smul_mul_assoc, smul_mul_assoc, smul_mul_assoc,
      E2_mul_E7_eq_zero hΓ, E7_idempotent hΓ, E3_mul_E7_eq_zero hΓ,
      smul_zero, smul_zero, zero_add, add_zero]

/-- A · E_3 = 3 · E_3 (V_3 上 A は scalar 3). -/
theorem adjMatrixF11_mul_E3_eq_three_smul_E3 (hΓ : IsMoore57 Γ) :
    adjMatrixF11 Γ * E3MatrixF11 Γ = (3 : ZMod 11) • E3MatrixF11 Γ := by
  classical
  have h_decomp := ELambda_decomp_A (Γ := Γ)
  rw [← h_decomp, add_mul, add_mul, smul_mul_assoc, smul_mul_assoc, smul_mul_assoc,
      E2_mul_E3_eq_zero hΓ, E7_mul_E3_eq_zero hΓ, E3_idempotent hΓ,
      smul_zero, smul_zero, zero_add, zero_add]

/-! ### Phase D-A Step 1: V_λ = ker(A_F11 - λ • 1) eigenspace characterization

A_F11 が `(A-2)(A-7)(A-3) = 0` を満たす (sorry-free)。closed form
`E_7 = 2 I + 3 A + 5 J` と `J · A = 2 J = A · J` (sorry-free) から:

v ∈ ker(A - 7 • 1) ⟹ J·A·v = (J·A)v = 2 J v = J·(A v) = J·(7v) = 7 J v
  ⟹ 5 J v = 0 ⟹ J v = 0.
E_7 v = 2 v + 3 (A v) + 5 (J v) = 2 v + 21 v + 0 = 23 v = v (mod 11).
⟹ v = E_7 v ∈ range E_7 = V_7. -/

theorem V7Submodule_eq_ker_A_sub_seven (h : Order22ActsOnMoore57 V Γ) :
    V7Submodule Γ =
    LinearMap.ker
      ((adjMatrixF11 Γ - (7 : ZMod 11) • (1 : Matrix V V (ZMod 11))).toLin') := by
  classical
  apply le_antisymm
  · -- V_7 ⊆ ker(A - 7 • 1)
    rintro v ⟨w, rfl⟩
    rw [LinearMap.mem_ker]
    have h_mat : (adjMatrixF11 Γ - (7 : ZMod 11) • (1 : Matrix V V (ZMod 11))) *
                  E7MatrixF11 Γ = 0 := by
      rw [sub_mul, smul_mul_assoc, one_mul,
          adjMatrixF11_mul_E7_eq_seven_smul_E7 h.isMoore, sub_self]
    show ((adjMatrixF11 Γ - (7 : ZMod 11) • 1 : Matrix V V (ZMod 11)).toLin')
         ((E7MatrixF11 Γ).toLin' w) = 0
    rw [show ((adjMatrixF11 Γ - (7 : ZMod 11) • 1 : Matrix V V (ZMod 11)).toLin')
            ((E7MatrixF11 Γ).toLin' w) =
            ((adjMatrixF11 Γ - (7 : ZMod 11) • 1) * E7MatrixF11 Γ).toLin' w from by
          rw [Matrix.toLin'_mul]; rfl]
    rw [h_mat]
    simp
  · -- ker(A - 7 • 1) ⊆ V_7
    intro v hv_ker
    rw [LinearMap.mem_ker] at hv_ker
    -- Unfold: (A - 7 • 1).toLin' v = A.mulVec v - 7 • v
    have hA : (adjMatrixF11 Γ).mulVec v = (7 : ZMod 11) • v := by
      have h_unfold :
          ((adjMatrixF11 Γ - (7 : ZMod 11) • (1 : Matrix V V (ZMod 11))).toLin') v =
            (adjMatrixF11 Γ).mulVec v - (7 : ZMod 11) • v := by
        show (adjMatrixF11 Γ - (7 : ZMod 11) • 1).mulVec v = _
        rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec]
      rw [h_unfold] at hv_ker
      exact sub_eq_zero.mp hv_ker
    -- J · v = 0 from J · A = 2 J + A v = 7 v.
    have hJv : (allOnesMatrixF11 V).mulVec v = 0 := by
      have h_J_A : (allOnesMatrixF11 V).mulVec ((adjMatrixF11 Γ).mulVec v) =
                   (2 : ZMod 11) • (allOnesMatrixF11 V).mulVec v := by
        rw [Matrix.mulVec_mulVec, allOnes_mul_adjMatrixF11 h.isMoore,
            Matrix.smul_mulVec]
      have h_J_7 : (allOnesMatrixF11 V).mulVec ((adjMatrixF11 Γ).mulVec v) =
                   (7 : ZMod 11) • (allOnesMatrixF11 V).mulVec v := by
        rw [hA, Matrix.mulVec_smul]
      have h5 : (5 : ZMod 11) • (allOnesMatrixF11 V).mulVec v = 0 := by
        have h_eq : (7 : ZMod 11) • (allOnesMatrixF11 V).mulVec v =
                    (2 : ZMod 11) • (allOnesMatrixF11 V).mulVec v :=
          h_J_7.symm.trans h_J_A
        have : ((7 : ZMod 11) - 2) • (allOnesMatrixF11 V).mulVec v = 0 := by
          rw [sub_smul]
          exact sub_eq_zero.mpr h_eq
        have h57 : ((7 : ZMod 11) - 2) = 5 := by decide
        rw [h57] at this
        exact this
      have h5_ne : (5 : ZMod 11) ≠ 0 := by decide
      rcases smul_eq_zero.mp h5 with h | h
      · exact absurd h h5_ne
      · exact h
    -- Show v = E_7 v ∈ V_7.
    refine ⟨v, ?_⟩
    show (E7MatrixF11 Γ).toLin' v = v
    show (E7MatrixF11 Γ).mulVec v = v
    rw [E7_eq_closed h.isMoore]
    -- E_7 v = (2 I + 3 A + 5 J) v = 2 v + 3 (A v) + 5 (J v) = 2 v + 21 v + 0 = 23 v = v
    rw [Matrix.add_mulVec, Matrix.add_mulVec,
        Matrix.smul_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec,
        Matrix.one_mulVec, hA, hJv]
    rw [smul_zero, add_zero, smul_smul]
    rw [← add_smul]
    have h_eq : ((2 : ZMod 11) + 3 * 7) = 1 := by decide
    rw [h_eq, one_smul]

/-! ### Phase D-A Step 2: A_F11.toLin' is IsSemisimple

`adjMatrixF11_cubic_eq_zero` (sorry-free) + (X-2)(X-7)(X-3) squarefree
⟹ A_F11.toLin' は semisimple. -/

/-- F_11 上の cubic polynomial `(X - 2)(X - 7)(X - 3)` は squarefree (distinct roots). -/
private lemma adjMatrixF11_cubic_polynomial_squarefree :
    Squarefree ((Polynomial.X - Polynomial.C (2 : ZMod 11)) *
                (Polynomial.X - Polynomial.C (7 : ZMod 11)) *
                (Polynomial.X - Polynomial.C (3 : ZMod 11))) := by
  have h27 : IsCoprime (Polynomial.X - Polynomial.C (2 : ZMod 11))
                       (Polynomial.X - Polynomial.C (7 : ZMod 11)) :=
    Polynomial.isCoprime_X_sub_C_of_isUnit_sub
      (by decide : IsUnit ((2 : ZMod 11) - 7))
  have h23 : IsCoprime (Polynomial.X - Polynomial.C (2 : ZMod 11))
                       (Polynomial.X - Polynomial.C (3 : ZMod 11)) :=
    Polynomial.isCoprime_X_sub_C_of_isUnit_sub
      (by decide : IsUnit ((2 : ZMod 11) - 3))
  have h73 : IsCoprime (Polynomial.X - Polynomial.C (7 : ZMod 11))
                       (Polynomial.X - Polynomial.C (3 : ZMod 11)) :=
    Polynomial.isCoprime_X_sub_C_of_isUnit_sub
      (by decide : IsUnit ((7 : ZMod 11) - 3))
  apply Polynomial.Separable.squarefree
  refine Polynomial.Separable.mul ?_ Polynomial.separable_X_sub_C ?_
  · exact Polynomial.Separable.mul Polynomial.separable_X_sub_C
      Polynomial.separable_X_sub_C h27
  · exact h23.mul_left h73

/-- A_F11.toLin' は polynomial `(X-2)(X-7)(X-3)` で annihilate される.
`adjMatrixF11_cubic_eq_zero` の LinearMap-aeval 版. -/
private lemma adjMatrixF11_toLin'_aeval_cubic_eq_zero
    (h : Order22ActsOnMoore57 V Γ) :
    Polynomial.aeval
        ((adjMatrixF11 Γ).toLin' : Module.End (ZMod 11) (V → ZMod 11))
        ((Polynomial.X - Polynomial.C (2 : ZMod 11)) *
         (Polynomial.X - Polynomial.C (7 : ZMod 11)) *
         (Polynomial.X - Polynomial.C (3 : ZMod 11))) = 0 := by
  classical
  simp only [map_mul, map_sub, Polynomial.aeval_X, Polynomial.aeval_C,
             Algebra.algebraMap_eq_smul_one]
  -- 目標: ((A.toLin') - 2 • 1) * ((A.toLin') - 7 • 1) * ((A.toLin') - 3 • 1) = 0
  -- これは matrix product (A-2)(A-7)(A-3) = 0 の toLin' 版.
  have h_mat := adjMatrixF11_cubic_eq_zero h.isMoore
  have h_step :
      ((adjMatrixF11 Γ - (2 : ZMod 11) • 1) *
        (adjMatrixF11 Γ - (7 : ZMod 11) • 1) *
        (adjMatrixF11 Γ - (3 : ZMod 11) • 1)).toLin' = 0 := by
    rw [h_mat]
    exact map_zero _
  rw [Matrix.toLin'_mul, Matrix.toLin'_mul] at h_step
  have h_sub2 : (adjMatrixF11 Γ - (2 : ZMod 11) • 1).toLin' =
                (adjMatrixF11 Γ).toLin' - (2 : ZMod 11) • 1 := by
    rw [map_sub]
    congr 1
    rw [map_smul, Matrix.toLin'_one, ← Module.End.one_eq_id]
  have h_sub7 : (adjMatrixF11 Γ - (7 : ZMod 11) • 1).toLin' =
                (adjMatrixF11 Γ).toLin' - (7 : ZMod 11) • 1 := by
    rw [map_sub]
    congr 1
    rw [map_smul, Matrix.toLin'_one, ← Module.End.one_eq_id]
  have h_sub3 : (adjMatrixF11 Γ - (3 : ZMod 11) • 1).toLin' =
                (adjMatrixF11 Γ).toLin' - (3 : ZMod 11) • 1 := by
    rw [map_sub]
    congr 1
    rw [map_smul, Matrix.toLin'_one, ← Module.End.one_eq_id]
  rw [h_sub2, h_sub7, h_sub3] at h_step
  exact h_step

/-- A_F11.toLin' は semisimple (squarefree minpoly via cubic). -/
theorem adjMatrixF11_toLin'_isSemisimple (h : Order22ActsOnMoore57 V Γ) :
    Module.End.IsSemisimple
      ((adjMatrixF11 Γ).toLin' : Module.End (ZMod 11) (V → ZMod 11)) :=
  Module.End.isSemisimple_of_squarefree_aeval_eq_zero
    adjMatrixF11_cubic_polynomial_squarefree
    (adjMatrixF11_toLin'_aeval_cubic_eq_zero h)

/-! ### Phase D-A Step 3: V_λ = maxGenEigenspace λ (via Semisimple) -/

/-- `V_7 = maxGenEigenspace 7` の identification (semisimple via Step 1, 2). -/
theorem V7Submodule_eq_maxGenEigenspace (h : Order22ActsOnMoore57 V Γ) :
    V7Submodule Γ =
    Module.End.maxGenEigenspace
      ((adjMatrixF11 Γ).toLin' : Module.End (ZMod 11) (V → ZMod 11))
      (7 : ZMod 11) := by
  -- maxGenEigenspace = eigenspace (via Semisimple).
  rw [(adjMatrixF11_toLin'_isSemisimple h).isFinitelySemisimple.maxGenEigenspace_eq_eigenspace]
  -- eigenspace = ker(f - μ • 1).
  rw [Module.End.eigenspace_def]
  -- Bridge ker((A - 7 • 1).toLin') = ker(A.toLin' - 7 • 1).
  rw [V7Submodule_eq_ker_A_sub_seven h]
  congr 1
  rw [map_sub, map_smul, Matrix.toLin'_one, ← Module.End.one_eq_id]

/-! ### Phase D-A Step 4: finrank V_7 = A_F11.toLin'.charpoly.rootMultiplicity 7

`finrank_maxGenEigenspace_eq` (sorry-free Mathlib): finrank maxGenEigenspace = rootMultiplicity. -/

/-- `dim V_7 = A_F11.toLin'.charpoly.rootMultiplicity 7`. -/
theorem finrank_V7Submodule_eq_rootMultiplicity (h : Order22ActsOnMoore57 V Γ) :
    Module.finrank (ZMod 11) (V7Submodule Γ) =
    ((adjMatrixF11 Γ).toLin' :
      Module.End (ZMod 11) (V → ZMod 11)).charpoly.rootMultiplicity (7 : ZMod 11) := by
  rw [V7Submodule_eq_maxGenEigenspace h]
  exact LinearMap.finrank_maxGenEigenspace_eq _ _

/-! ### Phase D-A Step 5: adjMatrixF11 を ℤ-adj の reduction として識別

`(adjMatrixF11 Γ) = (Γ.adjMatrix ℤ).map (Int.castRingHom)`.
`Matrix.charpoly_map` で charpoly も同様に reduce する. -/

/-- F_11 adjacency は ℤ-adjacency の Int.cast による reduction. -/
private lemma adjMatrixF11_eq_intCast_map :
    (adjMatrixF11 Γ) = (Γ.adjMatrix ℤ).map (Int.castRingHom (ZMod 11)) := by
  classical
  ext v w
  show (Γ.adjMatrix (ZMod 11)) v w =
       Int.castRingHom (ZMod 11) ((Γ.adjMatrix ℤ) v w)
  simp only [SimpleGraph.adjMatrix_apply, eq_intCast]
  by_cases h : Γ.Adj v w
  · simp [h]
  · simp [h]

/-- F_11-charpoly は ℤ-charpoly の reduction. -/
theorem adjMatrixF11_charpoly_eq_intCast_map :
    (adjMatrixF11 Γ).charpoly =
    (Γ.adjMatrix ℤ).charpoly.map (Int.castRingHom (ZMod 11)) := by
  rw [adjMatrixF11_eq_intCast_map]
  exact Matrix.charpoly_map _ _

/-- ℚ-charpoly は ℤ-charpoly の reduction. -/
theorem adjMatrix_ℚ_charpoly_eq_intCast_map :
    (Γ.adjMatrix ℚ).charpoly =
    (Γ.adjMatrix ℤ).charpoly.map (Int.castRingHom ℚ) := by
  classical
  have h_eq : (Γ.adjMatrix ℚ) = (Γ.adjMatrix ℤ).map (Int.castRingHom ℚ) := by
    ext v w
    show (Γ.adjMatrix ℚ) v w =
         Int.castRingHom ℚ ((Γ.adjMatrix ℤ) v w)
    simp only [SimpleGraph.adjMatrix_apply, eq_intCast]
    by_cases h : Γ.Adj v w
    · simp [h]
    · simp [h]
  rw [h_eq]
  exact Matrix.charpoly_map _ _

/-! ### Phase D-A Step 6: ℚ-side rootMultiplicity ≥ finrank V_λ_ℚ

各 λ ∈ {57, 7, -8} について:
* A_ℚ · E_λ = λ • E_λ から V_λ_ℚ ⊆ eigenspace λ.
* `finrank_eigenspace_le`: dim eigenspace ≤ rootMultiplicity.
* dim V_λ_ℚ ≤ dim eigenspace λ ≤ rootMultiplicity λ in A_ℚ.charpoly. -/

/-- ℚ 上 `A · E_57 = 57 • E_57`. -/
private theorem adjMatrix_ℚ_mul_E57 (hΓ : IsMoore57 Γ) :
    (Γ.adjMatrix ℚ) * (Moore57.E57Matrix V) = (57 : ℚ) • Moore57.E57Matrix V := by
  rw [Moore57.adjMatrix_eq_spectral_decomp hΓ,
      sub_mul, add_mul, smul_mul_assoc, smul_mul_assoc, smul_mul_assoc,
      Moore57.E57Matrix_mul_E57Matrix_eq_E57Matrix hΓ,
      Moore57.E7Matrix_mul_E57Matrix_eq_zero hΓ,
      Moore57.EMinus8Matrix_mul_E57Matrix_eq_zero hΓ,
      smul_zero, smul_zero, add_zero, sub_zero]

/-- ℚ 上 `A · E_7 = 7 • E_7`. -/
private theorem adjMatrix_ℚ_mul_E7 (hΓ : IsMoore57 Γ) :
    (Γ.adjMatrix ℚ) * E7Matrix Γ = (7 : ℚ) • E7Matrix Γ := by
  rw [Moore57.adjMatrix_eq_spectral_decomp hΓ,
      sub_mul, add_mul, smul_mul_assoc, smul_mul_assoc, smul_mul_assoc,
      Moore57.E57Matrix_mul_E7Matrix_eq_zero hΓ,
      Moore57.E7Matrix_mul_E7Matrix_eq_E7Matrix hΓ,
      Moore57.EMinus8Matrix_mul_E7Matrix_eq_zero hΓ,
      smul_zero, smul_zero, zero_add, sub_zero]

/-- ℚ 上 `A · E_-8 = -8 • E_-8`. -/
private theorem adjMatrix_ℚ_mul_EMinus8 (hΓ : IsMoore57 Γ) :
    (Γ.adjMatrix ℚ) * Moore57.EMinus8Matrix Γ = (-8 : ℚ) • Moore57.EMinus8Matrix Γ := by
  rw [Moore57.adjMatrix_eq_spectral_decomp hΓ,
      sub_mul, add_mul, smul_mul_assoc, smul_mul_assoc, smul_mul_assoc,
      Moore57.E57Matrix_mul_EMinus8Matrix_eq_zero hΓ,
      Moore57.E7Matrix_mul_EMinus8Matrix_eq_zero hΓ,
      Moore57.EMinus8Matrix_mul_EMinus8Matrix_eq_EMinus8Matrix hΓ,
      smul_zero, smul_zero, zero_add, zero_sub, neg_smul]

/-- Helper: matrix → LinearMap eigenspace inclusion via A · E = λ • E. -/
private lemma range_E_le_eigenspace (E : Matrix V V ℚ) (μ : ℚ)
    (hAE : (Γ.adjMatrix ℚ) * E = μ • E) :
    LinearMap.range (E.toLin') ≤
    Module.End.eigenspace ((Γ.adjMatrix ℚ).toLin' : Module.End ℚ (V → ℚ)) μ := by
  rintro v ⟨w, rfl⟩
  rw [Module.End.eigenspace_def, LinearMap.mem_ker]
  show ((Γ.adjMatrix ℚ).toLin' - (μ : ℚ) • 1) (E.toLin' w) = 0
  simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply]
  have hAE_apply : (Γ.adjMatrix ℚ).toLin' (E.toLin' w) = μ • (E.toLin' w) := by
    show (Γ.adjMatrix ℚ).mulVec (E.mulVec w) = μ • E.mulVec w
    rw [Matrix.mulVec_mulVec, hAE, Matrix.smul_mulVec]
  rw [hAE_apply, sub_self]

/-- `dim V_57_ℚ = 1` (trace E_57 = 1). -/
private theorem finrank_range_E57Matrix_eq_one (hΓ : IsMoore57 Γ) :
    Module.finrank ℚ (LinearMap.range ((Moore57.E57Matrix V).toLin') :
      Submodule ℚ (V → ℚ)) = 1 := by
  have hE57_idem : IsIdempotentElem
      ((Moore57.E57Matrix V).toLin' : (V → ℚ) →ₗ[ℚ] (V → ℚ)) := by
    rw [IsIdempotentElem, Module.End.mul_eq_comp, ← Moore57.matrix_toLin'_mul,
        Moore57.E57Matrix_mul_E57Matrix_eq_E57Matrix hΓ]
  have hQ := Moore57.finrank_range_eq_matrix_trace (Moore57.E57Matrix V) hE57_idem
  have htrE57 : Matrix.trace (Moore57.E57Matrix V : Matrix V V ℚ) = 1 := by
    have h := Moore57.trace_E57Matrix_mul_permMatrix (Γ := Γ) hΓ (1 : Equiv.Perm V)
    have h_perm_one : (permMatrix (1 : Equiv.Perm V) : Matrix V V ℚ) = 1 := by
      change Equiv.Perm.permMatrix ℚ ((1 : Equiv.Perm V)⁻¹) = 1
      simp
    rw [h_perm_one, Matrix.mul_one] at h
    exact h
  rw [htrE57] at hQ
  exact_mod_cast hQ

/-- ℚ-side: `rootMultiplicity 57 in A_ℚ.charpoly ≥ 1`. -/
private theorem rootMultiplicity_57_ge_one (hΓ : IsMoore57 Γ) :
    1 ≤ (Γ.adjMatrix ℚ).charpoly.rootMultiplicity (57 : ℚ) := by
  have h_sub := range_E_le_eigenspace (Γ := Γ) (Moore57.E57Matrix V) 57
                  (adjMatrix_ℚ_mul_E57 hΓ)
  have h_finrank_le :
      Module.finrank ℚ (LinearMap.range ((Moore57.E57Matrix V).toLin') :
        Submodule ℚ (V → ℚ)) ≤
      Module.finrank ℚ
        (Module.End.eigenspace
          ((Γ.adjMatrix ℚ).toLin' : Module.End ℚ (V → ℚ)) 57) :=
    Submodule.finrank_mono h_sub
  have h_eig_le := LinearMap.finrank_eigenspace_le
        ((Γ.adjMatrix ℚ).toLin' : Module.End ℚ (V → ℚ)) (57 : ℚ)
  rw [Matrix.charpoly_toLin'] at h_eig_le
  rw [← finrank_range_E57Matrix_eq_one hΓ]
  exact h_finrank_le.trans h_eig_le

/-- ℚ-side: `rootMultiplicity 7 in A_ℚ.charpoly ≥ 1729`. -/
private theorem rootMultiplicity_7_ge_1729 (hΓ : IsMoore57 Γ) :
    1729 ≤ (Γ.adjMatrix ℚ).charpoly.rootMultiplicity (7 : ℚ) := by
  have h_sub := range_E_le_eigenspace (Γ := Γ) (E7Matrix Γ) 7 (adjMatrix_ℚ_mul_E7 hΓ)
  have h_finrank_le :
      Module.finrank ℚ (LinearMap.range ((E7Matrix Γ).toLin') :
        Submodule ℚ (V → ℚ)) ≤
      Module.finrank ℚ
        (Module.End.eigenspace
          ((Γ.adjMatrix ℚ).toLin' : Module.End ℚ (V → ℚ)) 7) :=
    Submodule.finrank_mono h_sub
  have h_eig_le := LinearMap.finrank_eigenspace_le
        ((Γ.adjMatrix ℚ).toLin' : Module.End ℚ (V → ℚ)) (7 : ℚ)
  rw [Matrix.charpoly_toLin'] at h_eig_le
  rw [← Moore57.finrank_range_E7Matrix_eq_1729 Γ hΓ]
  exact h_finrank_le.trans h_eig_le

/-- ℚ-side: `rootMultiplicity -8 in A_ℚ.charpoly ≥ 1520`. -/
private theorem rootMultiplicity_minusEight_ge_1520 (hΓ : IsMoore57 Γ) :
    1520 ≤ (Γ.adjMatrix ℚ).charpoly.rootMultiplicity (-8 : ℚ) := by
  have h_sub := range_E_le_eigenspace (Γ := Γ) (Moore57.EMinus8Matrix Γ) (-8)
                  (adjMatrix_ℚ_mul_EMinus8 hΓ)
  have h_finrank_le :
      Module.finrank ℚ (LinearMap.range ((Moore57.EMinus8Matrix Γ).toLin') :
        Submodule ℚ (V → ℚ)) ≤
      Module.finrank ℚ
        (Module.End.eigenspace
          ((Γ.adjMatrix ℚ).toLin' : Module.End ℚ (V → ℚ)) (-8)) :=
    Submodule.finrank_mono h_sub
  have h_eig_le := LinearMap.finrank_eigenspace_le
        ((Γ.adjMatrix ℚ).toLin' : Module.End ℚ (V → ℚ)) (-8 : ℚ)
  rw [Matrix.charpoly_toLin'] at h_eig_le
  rw [← Moore57.finrank_range_EMinus8Matrix_eq_1520 Γ hΓ]
  exact h_finrank_le.trans h_eig_le

/-! ### Modular rep theory: F_11[C_11] による a^{F_11}_λ 値 (focused sorries)

各 V_λ は σ-不変な F_11 [C_11] 部分加群.
V_perm = M_1^5 ⊕ M_11^295 (5 fixed orbits + 295 free orbits, |C_11| = 11) の
直和因子なので, Krull-Schmidt によりブロックサイズは 1 か 11 のみ.

各 V_λ = M_1^{l_λ} ⊕ M_11^{k_λ}:
* dim V_λ = l_λ + 11 k_λ.
* a^{F_11}_λ := dim(V_λ ∩ ker(T_F11)) = l_λ + k_λ.
* l_λ ≡ dim V_λ (mod 11), Σ l_λ = 5.

dim V_λ (= rank E_λ over F_11) は rational rank の good reduction:
* dim V_2 = 1, dim V_7 = 1729, dim V_3 = 1520
  (Moore57 char poly factorization, `IsMoore57.trace_E7Matrix_one` 等経由).

⟹ l_2 = 1, l_7 = 2, l_3 = 2 (各 l_λ ∈ {0..5}, l_λ ≡ dim V_λ mod 11).
⟹ a^{F_11}_λ = 1, 159, 140.

下記 3 つを基幹 sorry として宣言. -/

/-- `V_2 = span(1_V)`: V_2 = Im(9·J), 9·J·g = 9·(Σ g)·1_V, range = ℤ/11·1_V. -/
theorem V2Submodule_eq_span_one (h : Order22ActsOnMoore57 V Γ) :
    V2Submodule Γ =
      Submodule.span (ZMod 11)
        ({(fun _ : V => (1 : ZMod 11))} : Set (V → ZMod 11)) := by
  classical
  haveI : Nonempty V := ⟨h.σ_fix.v 0⟩
  let v_0 : V := h.σ_fix.v 0
  -- helper: E_2 · g = (9 · Σ g) • 1_V
  have h_app : ∀ g : V → ZMod 11,
      (E2MatrixF11 Γ).toLin' g =
        ((9 : ZMod 11) * ∑ i, g i) • (fun _ : V => (1 : ZMod 11)) := by
    intro g
    ext w
    rw [E2_eq_nine_smul_allOnes h.isMoore]
    show ((9 : ZMod 11) • allOnesMatrixF11 V).mulVec g w =
         (((9 : ZMod 11) * ∑ i, g i) • (fun _ : V => (1 : ZMod 11))) w
    simp only [Matrix.mulVec, Matrix.smul_apply, dotProduct, smul_eq_mul,
               Pi.smul_apply, mul_one, allOnesMatrixF11, Matrix.of_apply]
    rw [← Finset.mul_sum]
  apply le_antisymm
  · -- V_2 ≤ span{1_V}
    rintro v ⟨g, rfl⟩
    rw [h_app]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
  · -- span{1_V} ≤ V_2
    rw [Submodule.span_le]
    rintro _ (rfl : _ = _)
    show (fun _ : V => (1 : ZMod 11)) ∈ V2Submodule Γ
    rw [V2Submodule, LinearMap.mem_range]
    -- E_2 (5 • indicator v_0) = (9 · 5) • 1_V = 1_V (since 9·5 ≡ 1 mod 11)
    refine ⟨fun w => if w = v_0 then (5 : ZMod 11) else 0, ?_⟩
    rw [h_app]
    have h_sum : (∑ i, (if i = v_0 then (5 : ZMod 11) else 0)) = 5 := by
      rw [Finset.sum_ite_eq' Finset.univ v_0 (fun _ => (5 : ZMod 11))]
      simp
    rw [h_sum]
    ext w
    show ((9 : ZMod 11) * 5) • ((fun _ : V => (1 : ZMod 11)) w) = 1
    simp only [Pi.smul_apply, smul_eq_mul, mul_one]
    decide

/-- `dim V_2 = 1` over F_11. -/
theorem finrank_V2Submodule_eq_one (h : Order22ActsOnMoore57 V Γ) :
    Module.finrank (ZMod 11) (V2Submodule Γ) = 1 := by
  classical
  haveI : Nonempty V := ⟨h.σ_fix.v 0⟩
  rw [V2Submodule_eq_span_one h]
  -- finrank (span {1_V}) = 1 since 1_V ≠ 0
  rw [show (Submodule.span (ZMod 11)
              ({(fun _ : V => (1 : ZMod 11))} : Set (V → ZMod 11))) =
          (ZMod 11) ∙ (fun _ : V => (1 : ZMod 11)) from rfl]
  apply finrank_span_singleton
  intro h_zero
  have h_ne : Nonempty V := ⟨h.σ_fix.v 0⟩
  obtain ⟨v⟩ := h_ne
  have : (fun _ : V => (1 : ZMod 11)) v = (0 : V → ZMod 11) v := by rw [h_zero]
  simp at this

/-- `a^{F_11}_2 := dim(V_2 ∩ ker T_F11) = 1`.

V_2 = span(1_V), dim 1; V_2 ⊆ ker T_F11; ⟹ V_2 ∩ ker T = V_2. -/
theorem aF11_lambda_two_eq_one (h : Order22ActsOnMoore57 V Γ) :
    Module.finrank (ZMod 11)
        (V2Submodule Γ ⊓ LinearMap.ker (T_F11 h) :
          Submodule (ZMod 11) (V → ZMod 11)) = 1 := by
  rw [aF11_lambda_two_eq_dim_V2, finrank_V2Submodule_eq_one h]

/-- **Phase D-A focused sorry**: `dim V_7 over F_11 = 1729`.

## 数学的構造 (good reduction)

A の特性多項式 (X-57)(X-7)^1729(X+8)^1520 が mod 11 で
((X-2)(X-7)(X-3) distinct) であるため, dim_F_11 V_7 = dim_ℚ V_7 = 1729.

## 形式化 roadmap (~250-450 行, 次セッション)

### Mathlib インフラ (confirmed exists)

- `Matrix.charpoly_map` (`Mathlib.LinearAlgebra.Matrix.Charpoly.Basic:173`):
  `(M.map f).charpoly = M.charpoly.map f`.
- `LinearMap.charpoly_baseChange`
  (`Mathlib.LinearAlgebra.Charpoly.BaseChange:23`):
  `(f.baseChange A).charpoly = f.charpoly.map (algebraMap R A)`.
- `finrank_maxGenEigenspace_eq`
  (`Mathlib.LinearAlgebra.Eigenspace.Zero:202`):
  `finrank K (φ.maxGenEigenspace μ) = φ.charpoly.rootMultiplicity μ`.
- `Module.End.isSemisimple_of_squarefree_aeval_eq_zero`
  (`Mathlib.LinearAlgebra.Semisimple:227`):
  Squarefree p + aeval f p = 0 ⟹ f.IsSemisimple.
- `IsSemisimple.minpoly_squarefree`
  (`Mathlib.LinearAlgebra.Semisimple:253`).

### Existing local infrastructure

ℚ side:
- `finrank_range_E7Matrix_eq_1729`: `dim V_7_ℚ = 1729`.
- `finrank_range_EMinus8Matrix_eq_1520`: `dim V_{-8}_ℚ = 1520`.
- `trace_E7Matrix_eq_1729_helper`, `E7Matrix_toLin'_isIdempotentElem''`.

F_11 side:
- `adjMatrixF11_cubic_eq_zero`: `(A-2)(A-7)(A-3) = 0` over F_11.
- `adjMatrixF11_mul_E_λ_eq_λ_smul_E_λ` (λ ∈ {2, 7, 3}).
- `V2_inter_V7_eq_bot` 等: V_λ pairwise disjoint.
- `V2_sup_V7_sup_V3_eq_top`: V_2 ⊔ V_7 ⊔ V_3 = ⊤.
- `finrank_sum_V_lambda_eq_3250` (本セッション追加).
- `finrank_V2Submodule_eq_one`: dim V_2_F11 = 1.

### Step 1: F_11 で V_λ = ker(A_F11 - λ I) を establish (~50 行)

```lean
theorem V7Submodule_eq_eigenspace (h : Order22ActsOnMoore57 V Γ) :
    V7Submodule Γ =
    LinearMap.ker (((adjMatrixF11 Γ) - (7 : ZMod 11) • 1 : Matrix V V (ZMod 11)).toLin') := by
  -- ⊆ : v = E_7 w, (A - 7 I) v = (A E_7 - 7 E_7) w = 0 from adjMatrixF11_mul_E7_eq.
  -- ⊇ : (A - 7) v = 0 ⟹ v = (E_2 + E_7 + E_3) v with E_μ v ∈ V_μ.
  --   A v = 7 v = 2 E_2 v + 7 E_7 v + 3 E_3 v (using A E_μ = μ E_μ).
  --   (2-7) E_2 v + 0 + (3-7) E_3 v = 0 ⟹ direct sum ⟹ E_2 v = E_3 v = 0.
  -- ~50 行.
  sorry  -- TODO Phase D-A step 1
```

V_λ = maxGenEigenspace λ (diagonalizable):
```lean
theorem V7Submodule_eq_maxGenEigenspace : V7Submodule Γ =
    ((adjMatrixF11 Γ).toLin' : Module.End (ZMod 11) (V → ZMod 11)).maxGenEigenspace 7
```

### Step 2: A_F11.charpoly = (charpoly_ℤ).map via base change (~50 行)

```lean
theorem adjMatrixF11_charpoly_eq_charpoly_intCast :
    (adjMatrixF11 Γ).charpoly =
    (Γ.adjMatrix ℤ).charpoly.map (Int.castRingHom (ZMod 11)) := by
  rw [adjMatrixF11, Γ.adjMatrix_intCast (ZMod 11)]
  -- adjMatrix R = (adjMatrix ℤ).map (Int.cast).
  exact Matrix.charpoly_map _ _
```

### Step 3: ℚ-charpoly factorization (~150 行) — bottleneck

```lean
theorem adjMatrix_ℚ_charpoly_factored (hΓ : IsMoore57 Γ) :
    (Γ.adjMatrix ℚ).charpoly =
    (X - C (57 : ℚ)) * (X - C 7) ^ 1729 * (X + C 8) ^ 1520 := by
  -- Strategy:
  -- (a) (A - 57)(A - 7)(A + 8) = 0 over ℚ (cubic from A^2 + A - 56 = J + AJ = 57 J).
  -- (b) Min poly | cubic, and 57, 7, -8 are eigenvalues, so min poly = cubic.
  -- (c) Min poly squarefree ⟹ A diagonalizable (IsSemisimple via Mathlib).
  -- (d) charpoly | min poly^N. charpoly degree = 3250. Roots ⊂ {57, 7, -8}.
  -- (e) charpoly = (X-57)^a (X-7)^b (X+8)^c with a+b+c = 3250.
  -- (f) finrank_maxGenEigenspace_eq + V_λ = maxGenEigenspace ⟹ a, b, c = 1, 1729, 1520.
  sorry
```

### Step 4: ℤ-charpoly factorization (Gauss lemma) (~30 行)

ℚ-factorization with integer coefficients ⟹ ℤ-factorization.
`Polynomial.coe_lift` or factoring through ℤ[X].

### Step 5: Reduce mod 11 (~30 行)

```lean
theorem adjMatrixF11_charpoly_factored :
    (adjMatrixF11 Γ).charpoly =
    (X - C (2 : ZMod 11)) * (X - C 7) ^ 1729 * (X - C 3) ^ 1520 := by
  rw [adjMatrixF11_charpoly_eq_charpoly_intCast, adjMatrix_ℤ_charpoly_factored]
  -- Map (X-57)(X-7)^1729(X+8)^1520 via ℤ → F_11.
  -- 57 ↦ 2, -8 ↦ 3 (≡ -8 mod 11).
  simp [Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C,
        Polynomial.map_sub, Polynomial.map_add]
  -- ring or decide for ZMod numerics.
```

### Step 6: rootMultiplicity (~20 行)

`(X-2)(X-7)^1729(X-3)^1520).rootMultiplicity 7 = 1729` (distinct roots).
Use `Polynomial.rootMultiplicity_X_sub_C_pow` + product/coprime lemmas.

### Step 7: Wire-up (~20 行)

```lean
theorem finrank_V7Submodule_eq_1729 :
    Module.finrank (ZMod 11) (V7Submodule Γ) = 1729 := by
  rw [V7Submodule_eq_maxGenEigenspace h, finrank_maxGenEigenspace_eq]
  rw [adjMatrixF11_charpoly_factored h]
  -- (X-2)(X-7)^1729(X-3)^1520).rootMultiplicity 7 = 1729.
  ...
```

## 主依存

Step 3 (ℚ-charpoly factorization) が中核. 詳細:
- `Module.End.IsSemisimple` from squarefree min poly (Mathlib).
- charpoly factorization for diagonalizable (custom proof via decomposition).
  Mathlib に直接 lemma がない場合は構築要.

## Mathlib search needed

- `Module.End.IsSemisimple` + charpoly factorization 直接 lemma?
- `Polynomial.rootMultiplicity_map` で root preservation 直接 lemma?

## Estimated total: ~350 行 sorry-free + 1 sorry remaining (or 0 if all closed). -/
theorem finrank_V7Submodule_eq_1729 (h : Order22ActsOnMoore57 V Γ) :
    Module.finrank (ZMod 11) (V7Submodule Γ) = 1729 := by
  -- Phase D-A Steps 1-4 経由で:
  -- dim V_7 = A_F11.toLin'.charpoly.rootMultiplicity 7 = adjMatrixF11.charpoly.rootMultiplicity 7.
  rw [finrank_V7Submodule_eq_rootMultiplicity h, Matrix.charpoly_toLin']
  -- 残作業: (adjMatrixF11 Γ).charpoly.rootMultiplicity (7 : ZMod 11) = 1729.
  -- 戦略: adjMatrixF11.charpoly = (Γ.adjMatrix ℤ).charpoly.map (Int.castRingHom (ZMod 11))
  --       (Γ.adjMatrix ℚ).charpoly = (X - 57)(X - 7)^1729 (X + 8)^1520 over ℚ[X]
  --       reduce mod 11: (X - 2)(X - 7)^1729 (X - 3)^1520 over F_11[X]
  --       rootMultiplicity (7) = 1729 (distinct roots).
  sorry

/-- `dim V_3 over F_11 = 1520` (derived from dim V_2 + dim V_7 + Σ = 3250). -/
theorem finrank_V3Submodule_eq_1520 (h : Order22ActsOnMoore57 V Γ) :
    Module.finrank (ZMod 11) (V3Submodule Γ) = 1520 := by
  have h_sum := finrank_sum_V_lambda_eq_card_V h
  have h_2 := finrank_V2Submodule_eq_one h
  have h_7 := finrank_V7Submodule_eq_1729 h
  omega

/-- F_11 modular rep theory **基幹 sorry**:
`a^{F_11}_7 := dim(V_7 ∩ ker T_F11) = 159`.

## 戦略分析 (2026-05-17 詳細評価)

### 数学的構造 (hybrid B + A)

(a) **Jordan 単調性 (Option B)**: `g_λ(j) := dim(V_λ ∩ ker T_F11^j)` は concave,
    非減少。 `Σ_λ g_λ(j) = g_total(j) = 5 + 295 j` (j ∈ [1, 11]) は線形
    (`finrank_ker_T_F11_pow` sorry-free).

    Concave 関数の和が線形 ⟹ 各 g_λ が `[1, 11]` 上で線形。
    Slope k_λ = (dim V_λ - a_F11_λ) / 10。
    ⟹ V_λ の Jordan 構造は **size 1 と 11 のブロックのみ**:
    `V_λ = M_1^{l_λ} ⊕ M_11^{k_λ}` で `l_λ + k_λ = a_F11_λ`, `l_λ + 11 k_λ = dim V_λ`.

(b) **σ-trace = l_λ (F_11 上)**: `trace(σ ∘ E_λ) over F_11 = l_λ`.
    各 M_11 で `trace σ = 11 ≡ 0 (mod 11)`, M_1 で `trace σ = 1`.
    Σ l_λ = 5 (= #Fix σ from `σ_fix`).

    具体的計算 (Moore57 + σ_pow_eleven):
    - trace(σ · E_2) = 1 over F_11 (`l_2 = 1`)
    - trace(σ · E_7) = 2 over F_11 (`l_7 = 2`)
    - trace(σ · E_3) = 2 over F_11 (`l_3 = 2`)

    確認: 1 + 2 + 2 = 5 ✓

(c) **dim V_λ over F_11 (Option A; good reduction)**: 主要 bottleneck.
    `dim V_7 over F_11 = 1729` を ℚ-rank からの reduction で導出する必要あり。

    Mathlib infrastructure:
    - `Matrix.charpoly_map`: charpoly 保存 (sorry-free).
    - `Polynomial.rootMultiplicity` + diagonalizability (`finrank_maxGenEigenspace_eq`).
    - 不足: A diagonalizable over ℚ + charpoly = ∏ (X - λ)^{dim V_λ} の formalization.

    ad-hoc 代替: rank E_7 over F_11 ≤ rank E_7 over ℚ = 1729 (semi-continuity)
    + Σ rank E_λ over F_11 = 3250 + rank E_2 = 1 + rank E_3 ≤ 1520 ⟹ 等式強制。

### 最終チェーン

dim V_7 = 1729 + (a) Jordan + (b) σ-trace ⟹
* l_7 = 2 (intrinsic from σ-trace + Σ l_λ = 5 と l_λ ∈ [0, 4]).
* k_7 = (dim V_7 - l_7) / 11 = (1729 - 2) / 11 = 157.
* a^{F_11}_7 = l_7 + k_7 = 159. ✓

### 工数見積 (~600-1000 行 total)

* B framework (concave linearity for V_λ): ~200-300 行.
* σ-trace identification (with KS): ~150-250 行.
* dim V_λ via good reduction (or alternative): ~250-450 行.
* Final wire-up: ~50 行.

### 残課題

主依存: (c) dim V_λ over F_11 — good reduction の formalization が中核。
σ-trace計算 (b) は sorry-free に可能だが KS identification を要する。
Jordan 単調性 (a) は既存 `finrank_ker_pow_concave` + `concave_linearity_forcing` で実現可能。 -/
theorem aF11_lambda_seven_eq_159 (h : Order22ActsOnMoore57 V Γ) :
    Module.finrank (ZMod 11)
        (V7Submodule Γ ⊓ LinearMap.ker (T_F11 h) :
          Submodule (ZMod 11) (V → ZMod 11)) = 159 := by
  -- Phase D-D wire-up: combine Phase D-B (linearity) + Phase D-A (dim V_λ) + concavity.
  -- (1) dim V_λ + 9 a_F11_λ = 10 g_λ(2)  (telescoped linearity from j=1 to j=11).
  -- (2) g_λ(2) ≤ 2 a_F11_λ                (concavity at j=1 with g_λ(0) = 0).
  -- (3) a_F11_2 + a_F11_7 + a_F11_3 = 300 (direct sum decomposition).
  -- (4) a_F11_2 = 1                        (V_2 = span(1_V)).
  -- omega over ℕ handles: a_F11_7 ∈ [158, 160] AND a_F11_7 ≡ 9 (mod 10) ⟹ = 159.
  classical
  -- Abbreviations.
  set a2 := Module.finrank (ZMod 11)
    (V2Submodule Γ ⊓ LinearMap.ker (T_F11 h) :
      Submodule (ZMod 11) (V → ZMod 11)) with ha2_def
  set a7 := Module.finrank (ZMod 11)
    (V7Submodule Γ ⊓ LinearMap.ker (T_F11 h) :
      Submodule (ZMod 11) (V → ZMod 11)) with ha7_def
  set a3 := Module.finrank (ZMod 11)
    (V3Submodule Γ ⊓ LinearMap.ker (T_F11 h) :
      Submodule (ZMod 11) (V → ZMod 11)) with ha3_def
  set b7 := Module.finrank (ZMod 11)
    (V7Submodule Γ ⊓ LinearMap.ker ((T_F11 h)^2) :
      Submodule (ZMod 11) (V → ZMod 11)) with hb7_def
  set b3 := Module.finrank (ZMod 11)
    (V3Submodule Γ ⊓ LinearMap.ker ((T_F11 h)^2) :
      Submodule (ZMod 11) (V → ZMod 11)) with hb3_def
  -- (1) Linearity relations (Phase D-B finalize).
  have h_lin_7 : 1729 + 9 * a7 = 10 * b7 := by
    have key := dim_V7_plus_9_aF11_seven_eq_10_g2 h
    rw [finrank_V7Submodule_eq_1729 h, pow_one] at key
    exact key
  have h_lin_3 : 1520 + 9 * a3 = 10 * b3 := by
    have key := dim_V3_plus_9_aF11_three_eq_10_g2 h
    rw [finrank_V3Submodule_eq_1520 h, pow_one] at key
    exact key
  -- (2) Concavity at j=1: b_λ + g_λ(0) ≤ 2 * a_λ, with g_λ(0) = 0.
  have h_ker0 : LinearMap.ker ((T_F11 h)^0) = (⊥ : Submodule (ZMod 11) (V → ZMod 11)) := by
    rw [pow_zero, Module.End.one_eq_id, LinearMap.ker_id]
  have h_concave_7 : b7 ≤ 2 * a7 := by
    have key := finrank_V7_inter_ker_T_F11_pow_concave h (show (1:ℕ) ≤ 1 from le_refl _)
    rw [show (1:ℕ) + 1 = 2 from rfl, show (1:ℕ) - 1 = 0 from rfl,
        h_ker0, inf_bot_eq, finrank_bot, pow_one] at key
    omega
  have h_concave_3 : b3 ≤ 2 * a3 := by
    have key := finrank_V3_inter_ker_T_F11_pow_concave h (show (1:ℕ) ≤ 1 from le_refl _)
    rw [show (1:ℕ) + 1 = 2 from rfl, show (1:ℕ) - 1 = 0 from rfl,
        h_ker0, inf_bot_eq, finrank_bot, pow_one] at key
    omega
  -- (3) Sum decomposition.
  have h_sum : a2 + a7 + a3 = 300 := h.aF11_sum_eq_300
  -- (4) a_F11_2 = 1.
  have h_a2 : a2 = 1 := h.aF11_lambda_two_eq_one
  -- Combine: omega solves a7 ∈ [158, 160] ∩ {a : a ≡ 9 (mod 10)} = {159}.
  omega

/-- `a^{F_11}_7 + a^{F_11}_3 = 299` (= 300 - a^{F_11}_2 with a^{F_11}_2 = 1). -/
theorem aF11_seven_plus_three_eq_299 (h : Order22ActsOnMoore57 V Γ) :
    Module.finrank (ZMod 11)
        (V7Submodule Γ ⊓ LinearMap.ker (T_F11 h) :
          Submodule (ZMod 11) (V → ZMod 11)) +
      Module.finrank (ZMod 11)
        (V3Submodule Γ ⊓ LinearMap.ker (T_F11 h) :
          Submodule (ZMod 11) (V → ZMod 11)) = 299 := by
  have h_sum := h.aF11_sum_eq_300
  have h_2 := h.aF11_lambda_two_eq_one
  omega

/-- `a^{F_11}_3 := dim(V_3 ∩ ker T_F11) = 140`.

`aF11_sum_eq_300` + `aF11_lambda_two_eq_one` + `aF11_lambda_seven_eq_159` から
sorry-free に導出 (300 = 1 + 159 + a^{F_11}_3 ⟹ a^{F_11}_3 = 140). -/
theorem aF11_lambda_three_eq_140 (h : Order22ActsOnMoore57 V Γ) :
    Module.finrank (ZMod 11)
        (V3Submodule Γ ⊓ LinearMap.ker (T_F11 h) :
          Submodule (ZMod 11) (V → ZMod 11)) = 140 := by
  have h_sum := h.aF11_sum_eq_300
  have h_2 := h.aF11_lambda_two_eq_one
  have h_7 := h.aF11_lambda_seven_eq_159
  omega

/-! ### F_11 trace identity: spectral side (sorry-free) + orbital side (focused sorry)

spectral basis:
  trace(A | ker T_F11) = Σ_λ λ · dim(V_λ ∩ ker T_F11) over F_11
  (A·E_λ = λ·E_λ から V_λ 上 A は λ·I で作用).

orbital basis (separate sorry):
  trace(A | ker T_F11) = 10n mod 11  (σ-不変性 + Tk_constant). -/

/-- `E_2` restricted to ker T_F11 is idempotent (lifted from E_2 * E_2 = E_2). -/
private theorem E2_restrict_ker_T_isIdempotent (h : Order22ActsOnMoore57 V Γ) :
    IsIdempotentElem h.E2_restrict_ker_T := by
  show h.E2_restrict_ker_T * h.E2_restrict_ker_T = h.E2_restrict_ker_T
  apply LinearMap.ext
  intro v
  apply Subtype.ext
  show (E2MatrixF11 Γ).toLin' ((E2MatrixF11 Γ).toLin' v.val) = (E2MatrixF11 Γ).toLin' v.val
  rw [show (E2MatrixF11 Γ).toLin' ((E2MatrixF11 Γ).toLin' v.val) =
        (E2MatrixF11 Γ * E2MatrixF11 Γ).toLin' v.val from by
      rw [Matrix.toLin'_mul]; rfl,
      E2_idempotent h.isMoore]

/-- `E_7` restricted to ker T_F11 is idempotent. -/
private theorem E7_restrict_ker_T_isIdempotent (h : Order22ActsOnMoore57 V Γ) :
    IsIdempotentElem h.E7_restrict_ker_T := by
  show h.E7_restrict_ker_T * h.E7_restrict_ker_T = h.E7_restrict_ker_T
  apply LinearMap.ext
  intro v
  apply Subtype.ext
  show (E7MatrixF11 Γ).toLin' ((E7MatrixF11 Γ).toLin' v.val) = (E7MatrixF11 Γ).toLin' v.val
  rw [show (E7MatrixF11 Γ).toLin' ((E7MatrixF11 Γ).toLin' v.val) =
        (E7MatrixF11 Γ * E7MatrixF11 Γ).toLin' v.val from by
      rw [Matrix.toLin'_mul]; rfl,
      E7_idempotent h.isMoore]

/-- `E_3` restricted to ker T_F11 is idempotent. -/
private theorem E3_restrict_ker_T_isIdempotent (h : Order22ActsOnMoore57 V Γ) :
    IsIdempotentElem h.E3_restrict_ker_T := by
  show h.E3_restrict_ker_T * h.E3_restrict_ker_T = h.E3_restrict_ker_T
  apply LinearMap.ext
  intro v
  apply Subtype.ext
  show (E3MatrixF11 Γ).toLin' ((E3MatrixF11 Γ).toLin' v.val) = (E3MatrixF11 Γ).toLin' v.val
  rw [show (E3MatrixF11 Γ).toLin' ((E3MatrixF11 Γ).toLin' v.val) =
        (E3MatrixF11 Γ * E3MatrixF11 Γ).toLin' v.val from by
      rw [Matrix.toLin'_mul]; rfl,
      E3_idempotent h.isMoore]

/-- range of `E_2_restrict_ker_T` (as Submodule of ker T_F11) mapped via subtype
equals `V_2 ⊓ ker T_F11` (Submodule of V → ZMod 11). -/
private theorem range_E2_restrict_ker_T_map_subtype_eq (h : Order22ActsOnMoore57 V Γ) :
    Submodule.map (Submodule.subtype (LinearMap.ker (T_F11 h)))
        (LinearMap.range h.E2_restrict_ker_T) =
      V2Submodule Γ ⊓ LinearMap.ker (T_F11 h) := by
  classical
  ext w
  simp only [Submodule.mem_map, LinearMap.mem_range, Submodule.coe_subtype,
             Submodule.mem_inf]
  refine ⟨?_, ?_⟩
  · -- forward: from `∃ z, z ∈ range E_2_restrict ∧ z.val = w`, derive w ∈ V_2 ∩ ker T.
    rintro ⟨⟨z, hz_kerT⟩, ⟨u, hu⟩, hzw⟩
    -- hzw : z = w (after Subtype.val unfolding)
    have h_zw : z = w := hzw
    have h_z_eq : (E2MatrixF11 Γ).toLin' u.val = z := congrArg Subtype.val hu
    refine ⟨?_, ?_⟩
    · -- w ∈ V_2
      rw [V2Submodule, LinearMap.mem_range]
      exact ⟨u.val, by rw [h_z_eq, h_zw]⟩
    · -- w ∈ ker T_F11
      rw [← h_zw]; exact hz_kerT
  · -- backward: w ∈ V_2 ∩ ker T → w = E_2_restrict ⟨w, hwk⟩.val (since E_2 w = w).
    rintro ⟨h_V2, h_kerT⟩
    refine ⟨⟨w, h_kerT⟩, ⟨⟨w, h_kerT⟩, ?_⟩, rfl⟩
    apply Subtype.ext
    show (E2MatrixF11 Γ).toLin' w = w
    obtain ⟨u, hu⟩ := LinearMap.mem_range.mp h_V2
    rw [← hu]
    show (E2MatrixF11 Γ).toLin' ((E2MatrixF11 Γ).toLin' u) = (E2MatrixF11 Γ).toLin' u
    rw [show (E2MatrixF11 Γ).toLin' ((E2MatrixF11 Γ).toLin' u) =
          (E2MatrixF11 Γ * E2MatrixF11 Γ).toLin' u from by
        rw [Matrix.toLin'_mul]; rfl,
        E2_idempotent h.isMoore]

/-- range of `E_7_restrict_ker_T` mapped via subtype = `V_7 ⊓ ker T_F11`. -/
private theorem range_E7_restrict_ker_T_map_subtype_eq (h : Order22ActsOnMoore57 V Γ) :
    Submodule.map (Submodule.subtype (LinearMap.ker (T_F11 h)))
        (LinearMap.range h.E7_restrict_ker_T) =
      V7Submodule Γ ⊓ LinearMap.ker (T_F11 h) := by
  classical
  ext w
  simp only [Submodule.mem_map, LinearMap.mem_range, Submodule.coe_subtype,
             Submodule.mem_inf]
  refine ⟨?_, ?_⟩
  · rintro ⟨⟨z, hz_kerT⟩, ⟨u, hu⟩, hzw⟩
    have h_zw : z = w := hzw
    have h_z_eq : (E7MatrixF11 Γ).toLin' u.val = z := congrArg Subtype.val hu
    refine ⟨?_, ?_⟩
    · rw [V7Submodule, LinearMap.mem_range]
      exact ⟨u.val, by rw [h_z_eq, h_zw]⟩
    · rw [← h_zw]; exact hz_kerT
  · rintro ⟨h_V7, h_kerT⟩
    refine ⟨⟨w, h_kerT⟩, ⟨⟨w, h_kerT⟩, ?_⟩, rfl⟩
    apply Subtype.ext
    show (E7MatrixF11 Γ).toLin' w = w
    obtain ⟨u, hu⟩ := LinearMap.mem_range.mp h_V7
    rw [← hu]
    show (E7MatrixF11 Γ).toLin' ((E7MatrixF11 Γ).toLin' u) = (E7MatrixF11 Γ).toLin' u
    rw [show (E7MatrixF11 Γ).toLin' ((E7MatrixF11 Γ).toLin' u) =
          (E7MatrixF11 Γ * E7MatrixF11 Γ).toLin' u from by
        rw [Matrix.toLin'_mul]; rfl,
        E7_idempotent h.isMoore]

/-- range of `E_3_restrict_ker_T` mapped via subtype = `V_3 ⊓ ker T_F11`. -/
private theorem range_E3_restrict_ker_T_map_subtype_eq (h : Order22ActsOnMoore57 V Γ) :
    Submodule.map (Submodule.subtype (LinearMap.ker (T_F11 h)))
        (LinearMap.range h.E3_restrict_ker_T) =
      V3Submodule Γ ⊓ LinearMap.ker (T_F11 h) := by
  classical
  ext w
  simp only [Submodule.mem_map, LinearMap.mem_range, Submodule.coe_subtype,
             Submodule.mem_inf]
  refine ⟨?_, ?_⟩
  · rintro ⟨⟨z, hz_kerT⟩, ⟨u, hu⟩, hzw⟩
    have h_zw : z = w := hzw
    have h_z_eq : (E3MatrixF11 Γ).toLin' u.val = z := congrArg Subtype.val hu
    refine ⟨?_, ?_⟩
    · rw [V3Submodule, LinearMap.mem_range]
      exact ⟨u.val, by rw [h_z_eq, h_zw]⟩
    · rw [← h_zw]; exact hz_kerT
  · rintro ⟨h_V3, h_kerT⟩
    refine ⟨⟨w, h_kerT⟩, ⟨⟨w, h_kerT⟩, ?_⟩, rfl⟩
    apply Subtype.ext
    show (E3MatrixF11 Γ).toLin' w = w
    obtain ⟨u, hu⟩ := LinearMap.mem_range.mp h_V3
    rw [← hu]
    show (E3MatrixF11 Γ).toLin' ((E3MatrixF11 Γ).toLin' u) = (E3MatrixF11 Γ).toLin' u
    rw [show (E3MatrixF11 Γ).toLin' ((E3MatrixF11 Γ).toLin' u) =
          (E3MatrixF11 Γ * E3MatrixF11 Γ).toLin' u from by
        rw [Matrix.toLin'_mul]; rfl,
        E3_idempotent h.isMoore]

/-- finrank(range E_2_restrict) = a^{F_11}_2 via subtype map equality + finrank_map_subtype. -/
private theorem finrank_range_E2_restrict_eq_aF11_two (h : Order22ActsOnMoore57 V Γ) :
    Module.finrank (ZMod 11) (LinearMap.range h.E2_restrict_ker_T) =
      Module.finrank (ZMod 11) (V2Submodule Γ ⊓ LinearMap.ker (T_F11 h) :
        Submodule (ZMod 11) (V → ZMod 11)) := by
  rw [← range_E2_restrict_ker_T_map_subtype_eq h,
      Submodule.finrank_map_subtype_eq]

/-- finrank(range E_7_restrict) = a^{F_11}_7. -/
private theorem finrank_range_E7_restrict_eq_aF11_seven (h : Order22ActsOnMoore57 V Γ) :
    Module.finrank (ZMod 11) (LinearMap.range h.E7_restrict_ker_T) =
      Module.finrank (ZMod 11) (V7Submodule Γ ⊓ LinearMap.ker (T_F11 h) :
        Submodule (ZMod 11) (V → ZMod 11)) := by
  rw [← range_E7_restrict_ker_T_map_subtype_eq h,
      Submodule.finrank_map_subtype_eq]

/-- finrank(range E_3_restrict) = a^{F_11}_3. -/
private theorem finrank_range_E3_restrict_eq_aF11_three (h : Order22ActsOnMoore57 V Γ) :
    Module.finrank (ZMod 11) (LinearMap.range h.E3_restrict_ker_T) =
      Module.finrank (ZMod 11) (V3Submodule Γ ⊓ LinearMap.ker (T_F11 h) :
        Submodule (ZMod 11) (V → ZMod 11)) := by
  rw [← range_E3_restrict_ker_T_map_subtype_eq h,
      Submodule.finrank_map_subtype_eq]

/-- trace(E_2_restrict) over ZMod 11 = (a^{F_11}_2 : ZMod 11). -/
private theorem trace_E2_restrict_ker_T_eq (h : Order22ActsOnMoore57 V Γ) :
    LinearMap.trace (ZMod 11) _ h.E2_restrict_ker_T =
      ((Module.finrank (ZMod 11) (V2Submodule Γ ⊓ LinearMap.ker (T_F11 h) :
          Submodule (ZMod 11) (V → ZMod 11)) : ℕ) : ZMod 11) := by
  have h_idem : IsIdempotentElem h.E2_restrict_ker_T := E2_restrict_ker_T_isIdempotent h
  have h_isProj : LinearMap.IsProj (LinearMap.range h.E2_restrict_ker_T)
      h.E2_restrict_ker_T :=
    (LinearMap.isProj_range_iff_isIdempotentElem _).mpr h_idem
  rw [h_isProj.trace, finrank_range_E2_restrict_eq_aF11_two h]

/-- trace(E_7_restrict) over ZMod 11 = (a^{F_11}_7 : ZMod 11). -/
private theorem trace_E7_restrict_ker_T_eq (h : Order22ActsOnMoore57 V Γ) :
    LinearMap.trace (ZMod 11) _ h.E7_restrict_ker_T =
      ((Module.finrank (ZMod 11) (V7Submodule Γ ⊓ LinearMap.ker (T_F11 h) :
          Submodule (ZMod 11) (V → ZMod 11)) : ℕ) : ZMod 11) := by
  have h_idem : IsIdempotentElem h.E7_restrict_ker_T := E7_restrict_ker_T_isIdempotent h
  have h_isProj : LinearMap.IsProj (LinearMap.range h.E7_restrict_ker_T)
      h.E7_restrict_ker_T :=
    (LinearMap.isProj_range_iff_isIdempotentElem _).mpr h_idem
  rw [h_isProj.trace, finrank_range_E7_restrict_eq_aF11_seven h]

/-- trace(E_3_restrict) over ZMod 11 = (a^{F_11}_3 : ZMod 11). -/
private theorem trace_E3_restrict_ker_T_eq (h : Order22ActsOnMoore57 V Γ) :
    LinearMap.trace (ZMod 11) _ h.E3_restrict_ker_T =
      ((Module.finrank (ZMod 11) (V3Submodule Γ ⊓ LinearMap.ker (T_F11 h) :
          Submodule (ZMod 11) (V → ZMod 11)) : ℕ) : ZMod 11) := by
  have h_idem : IsIdempotentElem h.E3_restrict_ker_T := E3_restrict_ker_T_isIdempotent h
  have h_isProj : LinearMap.IsProj (LinearMap.range h.E3_restrict_ker_T)
      h.E3_restrict_ker_T :=
    (LinearMap.isProj_range_iff_isIdempotentElem _).mpr h_idem
  rw [h_isProj.trace, finrank_range_E3_restrict_eq_aF11_three h]

/-- A_restrict = 2 • E_2_restrict + 7 • E_7_restrict + 3 • E_3_restrict (linear map identity).
Lifted from matrix identity `ELambda_decomp_A`. -/
private theorem adjMatrixF11_restrict_eq_smul_sum (h : Order22ActsOnMoore57 V Γ) :
    h.adjMatrixF11_restrict_ker_T =
      (2 : ZMod 11) • h.E2_restrict_ker_T +
      (7 : ZMod 11) • h.E7_restrict_ker_T +
      (3 : ZMod 11) • h.E3_restrict_ker_T := by
  apply LinearMap.ext
  intro v
  apply Subtype.ext
  -- LHS.val = (adjMatrixF11 Γ).toLin' v.val
  -- RHS.val = 2 • E_2 v.val + 7 • E_7 v.val + 3 • E_3 v.val (after unfolding smul and add on subtypes)
  show (adjMatrixF11 Γ).toLin' v.val = _
  -- From ELambda_decomp_A: 2 • E_2 + 7 • E_7 + 3 • E_3 = A.
  have h_decomp_apply :
      ((2 : ZMod 11) • E2MatrixF11 Γ + (7 : ZMod 11) • E7MatrixF11 Γ +
          (3 : ZMod 11) • E3MatrixF11 Γ).toLin' v.val =
      (adjMatrixF11 Γ).toLin' v.val := by
    rw [ELambda_decomp_A]
  rw [← h_decomp_apply]
  -- LHS = sum.toLin' v.val. Unfold using toLin'_add and toLin'_smul.
  show ((2 : ZMod 11) • E2MatrixF11 Γ + (7 : ZMod 11) • E7MatrixF11 Γ +
        (3 : ZMod 11) • E3MatrixF11 Γ).toLin' v.val = _
  have h_add_apply : ∀ (M N : Matrix V V (ZMod 11)),
      (M + N).toLin' v.val = M.toLin' v.val + N.toLin' v.val := fun M N => by
    simp [Matrix.toLin'_apply]
  have h_smul_apply : ∀ (c : ZMod 11) (M : Matrix V V (ZMod 11)),
      (c • M).toLin' v.val = c • M.toLin' v.val := fun c M => by
    simp [Matrix.toLin'_apply]
  rw [h_add_apply, h_add_apply, h_smul_apply, h_smul_apply, h_smul_apply]
  rfl

/-- **Spectral side of trace identity** (sorry-free):
trace(A_restrict over ker T_F11) = 2·a^{F_11}_2 + 7·a^{F_11}_7 + 3·a^{F_11}_3 in ZMod 11.

Uses `ELambda_decomp_A` (matrix-level) lifted to LinearMap.restrict,
trace linearity, and `IsProj.trace` for each E_λ_restrict. -/
theorem trace_adjMatrixF11_restrict_eq_spectral_side
    (h : Order22ActsOnMoore57 V Γ) :
    LinearMap.trace (ZMod 11) _ h.adjMatrixF11_restrict_ker_T =
      (2 : ZMod 11) *
        ((Module.finrank (ZMod 11)
          (V2Submodule Γ ⊓ LinearMap.ker (T_F11 h) :
            Submodule (ZMod 11) (V → ZMod 11)) : ℕ) : ZMod 11)
    + (7 : ZMod 11) *
        ((Module.finrank (ZMod 11)
          (V7Submodule Γ ⊓ LinearMap.ker (T_F11 h) :
            Submodule (ZMod 11) (V → ZMod 11)) : ℕ) : ZMod 11)
    + (3 : ZMod 11) *
        ((Module.finrank (ZMod 11)
          (V3Submodule Γ ⊓ LinearMap.ker (T_F11 h) :
            Submodule (ZMod 11) (V → ZMod 11)) : ℕ) : ZMod 11) := by
  rw [adjMatrixF11_restrict_eq_smul_sum h]
  rw [map_add, map_add, map_smul, map_smul, map_smul]
  rw [trace_E2_restrict_ker_T_eq h, trace_E7_restrict_ker_T_eq h,
      trace_E3_restrict_ker_T_eq h]
  simp only [smul_eq_mul]

/-! ### 軌道側 trace identity 形式化のための infrastructure

`kerTF11_quotientEquiv` (Phase4F11OrbitKernel) を使い trace を `(V/σ → F_11)` 側に
転送. 軌道基底 = Pi.basisFun で対角和に展開. -/

/-- Conjugate of `A_restrict` to `(Quotient → F_11)` via `kerTF11_quotientEquiv`. -/
noncomputable def adjMatrixF11_quot (h : Order22ActsOnMoore57 V Γ) :
    (Quotient (Equiv.Perm.SameCycle.setoid h.σ) → ZMod 11) →ₗ[ZMod 11]
      (Quotient (Equiv.Perm.SameCycle.setoid h.σ) → ZMod 11) :=
  ((h.kerTF11_quotientEquiv).symm.toLinearMap).comp
    (h.adjMatrixF11_restrict_ker_T.comp (h.kerTF11_quotientEquiv).toLinearMap)

/-- `kerTF11_quotientEquiv.conj` of `adjMatrixF11_quot` recovers `A_restrict`. -/
private theorem kerTF11_quotientEquiv_conj_adjMatrixF11_quot
    (h : Order22ActsOnMoore57 V Γ) :
    h.kerTF11_quotientEquiv.conj h.adjMatrixF11_quot =
      h.adjMatrixF11_restrict_ker_T := by
  apply LinearMap.ext
  intro v
  simp only [LinearEquiv.conj_apply_apply, adjMatrixF11_quot, LinearMap.comp_apply,
             LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]

/-- **Trace equality via conjugation** (sorry-free):
`trace(A_restrict over ker T_F11) = trace(A_quot over V/σ → F_11)`.

`LinearMap.trace_conj'` から従う. -/
theorem trace_adjMatrixF11_restrict_eq_trace_quot (h : Order22ActsOnMoore57 V Γ) :
    LinearMap.trace (ZMod 11) _ h.adjMatrixF11_restrict_ker_T =
      LinearMap.trace (ZMod 11) _ h.adjMatrixF11_quot := by
  rw [← kerTF11_quotientEquiv_conj_adjMatrixF11_quot h]
  exact LinearMap.trace_conj' _ _

/-- **Trace as sum of diagonals over orbits** (sorry-free):
`trace(A_quot) = Σ_O (A_quot (Pi.basisFun O)) O` over `(Quotient s → F_11)`. -/
theorem trace_adjMatrixF11_quot_eq_sum (h : Order22ActsOnMoore57 V Γ)
    [DecidableRel (Equiv.Perm.SameCycle.setoid h.σ).r]
    [Fintype (Quotient (Equiv.Perm.SameCycle.setoid h.σ))] :
    LinearMap.trace (ZMod 11) _ h.adjMatrixF11_quot =
      ∑ O : Quotient (Equiv.Perm.SameCycle.setoid h.σ),
        h.adjMatrixF11_quot (Pi.basisFun (ZMod 11) _ O) O := by
  classical
  rw [LinearMap.trace_eq_matrix_trace (ZMod 11)
        (Pi.basisFun (ZMod 11) (Quotient (Equiv.Perm.SameCycle.setoid h.σ))) _]
  rw [Matrix.trace]
  apply Finset.sum_congr rfl
  intro O _
  rw [Matrix.diag_apply, LinearMap.toMatrix_apply, Pi.basisFun_repr]

/-- **iso on basisFun = orbit indicator** (sorry-free):
`(kerTF11_quotientEquiv (Pi.basisFun O)).val v = (Pi.basisFun O) (Quotient.mk v)`. -/
theorem kerTF11_quotientEquiv_basisFun_apply (h : Order22ActsOnMoore57 V Γ)
    [DecidableRel (Equiv.Perm.SameCycle.setoid h.σ).r]
    (O : Quotient (Equiv.Perm.SameCycle.setoid h.σ)) (v : V) :
    ((h.kerTF11_quotientEquiv (Pi.basisFun (ZMod 11) _ O)) : V → ZMod 11) v =
      Pi.basisFun (ZMod 11) _ O (Quotient.mk _ v) :=
  kerTF11_quotientEquiv_apply h _ v

/-- **A_restrict applied to orbit indicator** (sorry-free, via defeq):
For `v : V` and σ-orbit `O`, the value of `A_restrict (e (Pi.basisFun _ _ O))` at `v`
is the F_11 sum `Σ_w (Γ.adjMatrix v w) * (Pi.basisFun _ _ O) (Quotient.mk w)`. -/
theorem adjMatrixF11_restrict_ker_T_basisFun_val
    (h : Order22ActsOnMoore57 V Γ)
    [DecidableRel (Equiv.Perm.SameCycle.setoid h.σ).r]
    (O : Quotient (Equiv.Perm.SameCycle.setoid h.σ)) (v : V) :
    ((h.adjMatrixF11_restrict_ker_T (h.kerTF11_quotientEquiv
        (Pi.basisFun (ZMod 11) _ O))) : V → ZMod 11) v =
      ∑ w : V, (adjMatrixF11 Γ) v w *
        (Pi.basisFun (ZMod 11) _ O (Quotient.mk _ w)) :=
  rfl

/-- σ-不変な orbit-neighbor count 関数 (helper for descending).
For each `v : V`, the value is `Σ_w (adjMatrixF11 Γ) v w * (Pi.basisFun O) (Quotient.mk w)`.
By σ-automorphism + Quotient.mk respect for σ, this is σ-invariant. -/
private noncomputable def orbitNeighborSumF11
    (h : Order22ActsOnMoore57 V Γ)
    [DecidableRel (Equiv.Perm.SameCycle.setoid h.σ).r]
    (O : Quotient (Equiv.Perm.SameCycle.setoid h.σ)) (v : V) : ZMod 11 :=
  ∑ w : V, (adjMatrixF11 Γ) v w *
    (Pi.basisFun (ZMod 11) _ O (Quotient.mk _ w))

/-- **σ-invariance of orbitNeighborSumF11** (sorry-free).
For `a ~ b` (same σ-cycle), `orbitNeighborSumF11 a = orbitNeighborSumF11 b`.

証明: First show σ-step invariance `orbitNeighborSumF11 (σ v) = orbitNeighborSumF11 v`
via `Equiv.sum_comp h.σ` substitution + σ-aut of Γ + Quotient.mk respect for σ.
Then `sigma_invariant_zpow` lifts to σ^i invariance, giving the SameCycle result. -/
private theorem orbitNeighborSumF11_sigma_invariant
    (h : Order22ActsOnMoore57 V Γ)
    [DecidableRel (Equiv.Perm.SameCycle.setoid h.σ).r]
    (O : Quotient (Equiv.Perm.SameCycle.setoid h.σ)) :
    ∀ a b : V, (Equiv.Perm.SameCycle.setoid h.σ).r a b →
      h.orbitNeighborSumF11 O a = h.orbitNeighborSumF11 O b := by
  -- Step 1: σ-step invariance.
  have h_step : ∀ v : V,
      h.orbitNeighborSumF11 O (h.σ v) = h.orbitNeighborSumF11 O v := by
    intro v
    unfold orbitNeighborSumF11
    -- Σ_w (adj Γ) (σ v) w * g(w) = Σ_w (adj Γ) v w * g(w)
    -- where g(w) = Pi.basisFun O (Quotient.mk w).
    -- Substitute w → σ w using Equiv.sum_comp.
    rw [← Equiv.sum_comp h.σ (fun w : V =>
        (adjMatrixF11 Γ) (h.σ v) w *
          (Pi.basisFun (ZMod 11) _ O (Quotient.mk _ w)))]
    apply Finset.sum_congr rfl
    intro w _
    congr 1
    · -- (adjMatrixF11 Γ) (σ v) (σ w) = (adjMatrixF11 Γ) v w  (σ-aut)
      unfold adjMatrixF11
      rw [SimpleGraph.adjMatrix_apply, SimpleGraph.adjMatrix_apply]
      by_cases hadj : Γ.Adj v w
      · rw [if_pos hadj, if_pos ((h.σ_aut v w).mp hadj)]
      · rw [if_neg hadj, if_neg (fun h' => hadj ((h.σ_aut v w).mpr h'))]
    · -- Pi.basisFun O (Quotient.mk (σ w)) = Pi.basisFun O (Quotient.mk w)
      -- since Quotient.mk (σ w) = Quotient.mk w (same cycle).
      have h_mk : Quotient.mk (Equiv.Perm.SameCycle.setoid h.σ) (h.σ w) =
          Quotient.mk _ w := by
        apply Quotient.sound
        refine ⟨(-1 : ℤ), ?_⟩
        simp [zpow_neg, zpow_one]
      rw [h_mk]
  -- Step 2: lift to σ^i invariance via sigma_invariant_zpow.
  intro a b hab
  obtain ⟨i, hi⟩ := hab
  rw [← hi]
  exact (sigma_invariant_zpow h h_step i a).symm

/-- Descended orbit-neighbor count function on `Quotient`. -/
private noncomputable def orbitNeighborSumQuot
    (h : Order22ActsOnMoore57 V Γ)
    [DecidableRel (Equiv.Perm.SameCycle.setoid h.σ).r]
    (O : Quotient (Equiv.Perm.SameCycle.setoid h.σ)) :
    Quotient (Equiv.Perm.SameCycle.setoid h.σ) → ZMod 11 :=
  Quotient.lift (h.orbitNeighborSumF11 O) (h.orbitNeighborSumF11_sigma_invariant O)

/-- **e of orbitNeighborSumQuot = A_restrict (e (Pi.basisFun O))** (sorry-free):
The candidate `orbitNeighborSumQuot` pulls back via `e` to `A_restrict (e (Pi.basisFun O))`. -/
private theorem kerTF11_quotientEquiv_orbitNeighborSumQuot_eq
    (h : Order22ActsOnMoore57 V Γ)
    [DecidableRel (Equiv.Perm.SameCycle.setoid h.σ).r]
    (O : Quotient (Equiv.Perm.SameCycle.setoid h.σ)) :
    h.kerTF11_quotientEquiv (h.orbitNeighborSumQuot O) =
      h.adjMatrixF11_restrict_ker_T
        (h.kerTF11_quotientEquiv (Pi.basisFun (ZMod 11) _ O)) := by
  apply Subtype.ext
  funext v
  rw [kerTF11_quotientEquiv_apply, adjMatrixF11_restrict_ker_T_basisFun_val]
  -- LHS: orbitNeighborSumQuot O (Quotient.mk _ v) = orbitNeighborSumF11 O v (by Quotient.lift_mk)
  -- RHS: same sum
  show h.orbitNeighborSumQuot O (Quotient.mk _ v) = _
  unfold orbitNeighborSumQuot
  rw [Quotient.lift_mk]
  rfl

/-- **A_quot diagonal entry (sorry-free given σ-invariance)**:
`A_quot (Pi.basisFun O) (Quotient.mk v) = Σ_w (adjMatrixF11 Γ) v w * (Pi.basisFun O) (Quotient.mk w)`.

Uses `kerTF11_quotientEquiv_orbitNeighborSumQuot_eq` + `LinearEquiv.symm_apply_eq`. -/
theorem adjMatrixF11_quot_basisFun_apply_at_mk
    (h : Order22ActsOnMoore57 V Γ)
    [DecidableRel (Equiv.Perm.SameCycle.setoid h.σ).r]
    (O : Quotient (Equiv.Perm.SameCycle.setoid h.σ)) (v : V) :
    h.adjMatrixF11_quot (Pi.basisFun (ZMod 11) _ O) (Quotient.mk _ v) =
      ∑ w : V, (adjMatrixF11 Γ) v w *
        (Pi.basisFun (ZMod 11) _ O (Quotient.mk _ w)) := by
  -- adjMatrixF11_quot = e.symm ∘ A_restrict ∘ e
  -- Apply to (Quotient.mk v)
  show (h.kerTF11_quotientEquiv.symm
    (h.adjMatrixF11_restrict_ker_T
      (h.kerTF11_quotientEquiv (Pi.basisFun (ZMod 11) _ O)))) (Quotient.mk _ v) = _
  -- Use e.symm of (e f) = f, with f = orbitNeighborSumQuot O
  rw [show h.adjMatrixF11_restrict_ker_T
        (h.kerTF11_quotientEquiv (Pi.basisFun (ZMod 11) _ O)) =
        h.kerTF11_quotientEquiv (h.orbitNeighborSumQuot O) from
        (kerTF11_quotientEquiv_orbitNeighborSumQuot_eq h O).symm,
      LinearEquiv.symm_apply_apply]
  show h.orbitNeighborSumQuot O (Quotient.mk _ v) = _
  unfold orbitNeighborSumQuot
  rw [Quotient.lift_mk]
  rfl

/-- **A_quot on Pi.basisFun equals orbitNeighborSumQuot** (sorry-free):
The function `Quotient → F_11` after applying `A_quot` to `Pi.basisFun O` is exactly
the descended `orbitNeighborSumQuot O`. Uses `LinearEquiv.symm_apply_apply`. -/
theorem adjMatrixF11_quot_basisFun_eq_orbitNeighborSumQuot
    (h : Order22ActsOnMoore57 V Γ)
    [DecidableRel (Equiv.Perm.SameCycle.setoid h.σ).r]
    (O : Quotient (Equiv.Perm.SameCycle.setoid h.σ)) :
    h.adjMatrixF11_quot (Pi.basisFun (ZMod 11) _ O) = h.orbitNeighborSumQuot O := by
  show h.kerTF11_quotientEquiv.symm
    (h.adjMatrixF11_restrict_ker_T
      (h.kerTF11_quotientEquiv (Pi.basisFun (ZMod 11) _ O))) = _
  rw [← kerTF11_quotientEquiv_orbitNeighborSumQuot_eq h O]
  exact h.kerTF11_quotientEquiv.symm_apply_apply _

/-- **A_quot diagonal entry at general O** (sorry-free):
`A_quot (Pi.basisFun O) O = orbitNeighborSumF11 O (Quotient.out O)`.

Uses `adjMatrixF11_quot_basisFun_eq_orbitNeighborSumQuot` + `Quotient.out_eq`
+ σ-invariance. -/
theorem adjMatrixF11_quot_diagonal_eq_orbitNeighborSumF11_out
    (h : Order22ActsOnMoore57 V Γ)
    [DecidableRel (Equiv.Perm.SameCycle.setoid h.σ).r]
    (O : Quotient (Equiv.Perm.SameCycle.setoid h.σ)) :
    h.adjMatrixF11_quot (Pi.basisFun (ZMod 11) _ O) O =
      h.orbitNeighborSumF11 O (Quotient.out O) := by
  rw [adjMatrixF11_quot_basisFun_eq_orbitNeighborSumQuot h O]
  -- Goal: orbitNeighborSumQuot O O = orbitNeighborSumF11 O (Quotient.out O)
  -- Use Quotient.inductionOn to extract a representative.
  induction O using Quotient.inductionOn with
  | _ v =>
    -- Goal: orbitNeighborSumQuot (Quotient.mk _ v) (Quotient.mk _ v) =
    --        orbitNeighborSumF11 (Quotient.mk _ v) (Quotient.out (Quotient.mk _ v))
    unfold orbitNeighborSumQuot
    rw [Quotient.lift_mk]
    -- Goal: orbitNeighborSumF11 (Quotient.mk _ v) v = orbitNeighborSumF11 (Quotient.mk _ v) (Quotient.out _)
    have h_rel : (Equiv.Perm.SameCycle.setoid h.σ).r v
        (Quotient.out (Quotient.mk (Equiv.Perm.SameCycle.setoid h.σ) v)) :=
      Quotient.exact (Quotient.out_eq _).symm
    exact h.orbitNeighborSumF11_sigma_invariant _ v _ h_rel

/-- **Trace = orbital count over vertices** (sorry-free).
The trace of `A_restrict` equals `Σ_w (adjMatrixF11 Γ) (Quotient.out (Quotient.mk w)) w`
in F_11, which counts vertex pairs `(rep, w)` with rep adjacent to w in same orbit. -/
theorem trace_adjMatrixF11_restrict_eq_sum_over_vertices
    (h : Order22ActsOnMoore57 V Γ)
    [DecidableRel (Equiv.Perm.SameCycle.setoid h.σ).r]
    [Fintype (Quotient (Equiv.Perm.SameCycle.setoid h.σ))] :
    LinearMap.trace (ZMod 11) _ h.adjMatrixF11_restrict_ker_T =
      ∑ w : V, (adjMatrixF11 Γ)
        (Quotient.out (Quotient.mk (Equiv.Perm.SameCycle.setoid h.σ) w)) w := by
  classical
  rw [trace_adjMatrixF11_restrict_eq_trace_quot, trace_adjMatrixF11_quot_eq_sum]
  -- Step 1: Expand each diagonal entry via the lemma.
  simp_rw [adjMatrixF11_quot_diagonal_eq_orbitNeighborSumF11_out h, orbitNeighborSumF11]
  -- Goal: Σ_O Σ_w (adjMatrixF11 Γ) (Quotient.out O) w * (Pi.basisFun _ _ O) (Quotient.mk _ w)
  --        = Σ_w (adjMatrixF11 Γ) (Quotient.out (Quotient.mk _ w)) w
  -- Step 2: Swap sums + collapse via Pi.basisFun.
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro w _
  -- For each w: Σ_O (adj Γ) (Quot.out O) w * (Pi.basisFun O) (Quot.mk w) = (adj Γ) (Quot.out (Quot.mk w)) w
  -- Rewrite each term using Pi.basisFun = Pi.single, then collapse to single term.
  rw [show (∑ O : Quotient (Equiv.Perm.SameCycle.setoid h.σ),
            (adjMatrixF11 Γ) (Quotient.out O) w *
              (Pi.basisFun (ZMod 11) _ O (Quotient.mk _ w))) =
          ∑ O : Quotient (Equiv.Perm.SameCycle.setoid h.σ),
            (if Quotient.mk _ w = O
             then (adjMatrixF11 Γ) (Quotient.out O) w else 0) from by
      apply Finset.sum_congr rfl
      intro O _
      rw [Pi.basisFun_apply, Pi.single_apply]
      split_ifs with hO
      · rw [mul_one]
      · rw [mul_zero]]
  rw [Finset.sum_ite_eq Finset.univ (Quotient.mk _ w)
      (fun O => (adjMatrixF11 Γ) (Quotient.out O) w)]
  simp

/-! ### C3 helpers: σ-orbit cardinality and orbitNeighborCount -/

/-- σ-orbit neighbor count: |{d ∈ Fin 11 : σ^d v is adjacent to v}|. -/
private noncomputable def orbitNeighborCountN (h : Order22ActsOnMoore57 V Γ) (v : V) : ℕ :=
  ((Finset.range 11).filter (fun d => Γ.Adj v ((h.σ ^ d) v))).card

/-- σ-step invariance of orbitNeighborCountN: `onc (σ v) = onc v`. -/
private theorem orbitNeighborCountN_σ_step (h : Order22ActsOnMoore57 V Γ) :
    ∀ v : V, h.orbitNeighborCountN (h.σ v) = h.orbitNeighborCountN v := by
  intro v
  unfold orbitNeighborCountN
  congr 1
  apply Finset.filter_congr
  intro d _
  have h_comm : (h.σ ^ d) (h.σ v) = h.σ ((h.σ ^ d) v) := by
    rw [← Equiv.Perm.mul_apply, ← Equiv.Perm.mul_apply]
    congr 1
    rw [← pow_succ, pow_succ']
  rw [h_comm]
  exact (h.σ_aut v ((h.σ ^ d) v)).symm

/-- SameCycle invariance of orbitNeighborCountN. -/
private theorem orbitNeighborCountN_sameCycle (h : Order22ActsOnMoore57 V Γ) :
    ∀ a b : V, (Equiv.Perm.SameCycle.setoid h.σ).r a b →
      h.orbitNeighborCountN a = h.orbitNeighborCountN b := by
  intro a b ⟨i, hi⟩
  rw [← hi]
  exact (sigma_invariant_zpow (f := h.orbitNeighborCountN) h
      (h.orbitNeighborCountN_σ_step) i a).symm

/-- For σ-fixed v, σ^d v = v for any d ∈ ℕ. -/
private theorem σ_pow_eq_self_of_fixed (h : Order22ActsOnMoore57 V Γ)
    {v : V} (hv : h.σ v = v) (d : ℕ) : (h.σ ^ d) v = v := by
  induction d with
  | zero => simp
  | succ k ih =>
    rw [pow_succ]
    simp only [Equiv.Perm.mul_apply]
    rw [hv]; exact ih

/-- For σ-fixed v, orbitNeighborCountN v = 0 (no loops, σ^d v = v). -/
private theorem orbitNeighborCountN_eq_zero_of_fixed (h : Order22ActsOnMoore57 V Γ)
    {v : V} (hv : h.σ v = v) : h.orbitNeighborCountN v = 0 := by
  unfold orbitNeighborCountN
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro d _
  rw [σ_pow_eq_self_of_fixed h hv]
  exact SimpleGraph.irrefl Γ

/-- For free rep (σ rep ≠ rep), σ^n rep = rep iff 11 ∣ n.
Uses `IsCycle.pow_eq_one_iff'` + `cycleOf_pow_apply_self` + cycleType. -/
private theorem σ_pow_apply_eq_self_iff_dvd_of_free (h : Order22ActsOnMoore57 V Γ)
    {rep : V} (hrep : h.σ rep ≠ rep) (n : ℕ) :
    (h.σ ^ n) rep = rep ↔ 11 ∣ n := by
  have h_rep_in_supp : rep ∈ h.σ.support := Equiv.Perm.mem_support.mpr hrep
  have h_cycleOf : Equiv.Perm.IsCycle (h.σ.cycleOf rep) :=
    Equiv.Perm.isCycle_cycleOf h.σ hrep
  have h_orderOf : orderOf (h.σ.cycleOf rep) = 11 := by
    rw [h_cycleOf.orderOf]
    have h_in_cf : h.σ.cycleOf rep ∈ h.σ.cycleFactorsFinset :=
      Equiv.Perm.cycleOf_mem_cycleFactorsFinset_iff.mpr h_rep_in_supp
    have h_in_ct : (h.σ.cycleOf rep).support.card ∈ h.σ.cycleType := by
      rw [Equiv.Perm.cycleType_def]
      exact Multiset.mem_map.mpr ⟨h.σ.cycleOf rep, h_in_cf, rfl⟩
    rw [cycleType_σ_eq_replicate h] at h_in_ct
    exact Multiset.eq_of_mem_replicate h_in_ct
  have h_cycle_apply_ne : (h.σ.cycleOf rep) rep ≠ rep := by
    rw [Equiv.Perm.cycleOf_apply_self]
    exact hrep
  -- (σ^n) rep = (cycleOf σ rep ^ n) rep, then iff via IsCycle.pow_eq_one_iff'.
  constructor
  · intro hpow
    have h_cycle_pow_eq : ((h.σ.cycleOf rep) ^ n) rep = rep := by
      rw [Equiv.Perm.cycleOf_pow_apply_self]; exact hpow
    have h_cycle_pow_one : (h.σ.cycleOf rep) ^ n = 1 :=
      (h_cycleOf.pow_eq_one_iff' h_cycle_apply_ne).mpr h_cycle_pow_eq
    have h_dvd : orderOf (h.σ.cycleOf rep) ∣ n :=
      orderOf_dvd_of_pow_eq_one h_cycle_pow_one
    rw [h_orderOf] at h_dvd; exact h_dvd
  · intro hdvd
    have h_cycle_pow_one : (h.σ.cycleOf rep) ^ n = 1 := by
      rw [← h_orderOf] at hdvd
      exact orderOf_dvd_iff_pow_eq_one.mp hdvd
    have h_cycle_pow_eq : ((h.σ.cycleOf rep) ^ n) rep = rep := by
      rw [h_cycle_pow_one]; rfl
    rw [← Equiv.Perm.cycleOf_pow_apply_self h.σ rep n]
    exact h_cycle_pow_eq

/-- For fixed rep, σ-fiber is {rep}. -/
private theorem σ_fiber_eq_singleton_of_fixed (h : Order22ActsOnMoore57 V Γ)
    [DecidableRel (Equiv.Perm.SameCycle.setoid h.σ).r]
    (O : Quotient (Equiv.Perm.SameCycle.setoid h.σ))
    (hO : h.σ (Quotient.out O) = Quotient.out O) :
    Finset.univ.filter (fun v : V =>
        Quotient.mk (Equiv.Perm.SameCycle.setoid h.σ) v = O) = {Quotient.out O} := by
  ext v
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
  constructor
  · intro hv
    have h_sc : (Equiv.Perm.SameCycle.setoid h.σ).r v (Quotient.out O) := by
      apply Quotient.exact
      rw [hv]; exact (Quotient.out_eq _).symm
    have h_fixed_v : h.σ v = v :=
      (Equiv.Perm.SameCycle.apply_eq_self_iff h_sc).mpr hO
    exact Equiv.Perm.SameCycle.eq_of_left h_sc h_fixed_v
  · intro hv
    rw [hv]; exact Quotient.out_eq _

/-- (cycleOf σ rep).support.card = 11 for free rep, from cycleType. -/
private theorem cycleOf_support_card_eq_eleven (h : Order22ActsOnMoore57 V Γ)
    {rep : V} (hrep : h.σ rep ≠ rep) :
    (h.σ.cycleOf rep).support.card = 11 := by
  have h_rep_in_supp : rep ∈ h.σ.support := Equiv.Perm.mem_support.mpr hrep
  have h_cycleOf_mem : h.σ.cycleOf rep ∈ h.σ.cycleFactorsFinset :=
    Equiv.Perm.cycleOf_mem_cycleFactorsFinset_iff.mpr h_rep_in_supp
  have h_in_ct : (h.σ.cycleOf rep).support.card ∈ h.σ.cycleType := by
    rw [Equiv.Perm.cycleType_def]
    exact Multiset.mem_map.mpr ⟨h.σ.cycleOf rep, h_cycleOf_mem, rfl⟩
  rw [cycleType_σ_eq_replicate h] at h_in_ct
  exact Multiset.eq_of_mem_replicate h_in_ct

/-- For free rep, σ^· : Fin 11 → V is injective at rep (using primality of 11). -/
private theorem σ_pow_apply_injective_of_free (h : Order22ActsOnMoore57 V Γ)
    {rep : V} (hrep : h.σ rep ≠ rep)
    {d₁ d₂ : ℕ} (h₁ : d₁ < 11) (h₂ : d₂ < 11)
    (heq : (h.σ ^ d₁) rep = (h.σ ^ d₂) rep) : d₁ = d₂ := by
  -- WLOG d₁ ≤ d₂. Then σ^(d₂ - d₁) rep = rep. By prime order, 11 ∣ (d₂ - d₁). Hence d₁ = d₂.
  wlog hle : d₁ ≤ d₂ with H
  · exact (H h hrep h₂ h₁ heq.symm (Nat.le_of_not_le hle)).symm
  -- σ^d₁ * σ^(d₂-d₁) = σ^d₂. Combined with heq, get σ^(d₂-d₁) rep = rep.
  have h_sub : (h.σ ^ (d₂ - d₁)) rep = rep := by
    have h_split : (h.σ ^ d₁) ((h.σ ^ (d₂ - d₁)) rep) = (h.σ ^ d₂) rep := by
      rw [← Equiv.Perm.mul_apply, ← pow_add, Nat.add_sub_cancel' hle]
    have h_eq2 : (h.σ ^ d₁) ((h.σ ^ (d₂ - d₁)) rep) = (h.σ ^ d₁) rep := by
      rw [h_split]; exact heq.symm
    exact (h.σ ^ d₁).injective h_eq2
  -- 11 ∣ (d₂ - d₁), and d₂ - d₁ < 11, so d₂ - d₁ = 0.
  have h_dvd : 11 ∣ (d₂ - d₁) :=
    (σ_pow_apply_eq_self_iff_dvd_of_free h hrep _).mp h_sub
  have h_lt : d₂ - d₁ < 11 := by omega
  have : d₂ - d₁ = 0 := Nat.eq_zero_of_dvd_of_lt h_dvd h_lt
  omega

/-- For free rep, σ-fiber cardinality equals 11 via direct bijection on Finset.range 11. -/
private theorem σ_fiber_card_eq_eleven_of_free (h : Order22ActsOnMoore57 V Γ)
    [DecidableRel (Equiv.Perm.SameCycle.setoid h.σ).r]
    (O : Quotient (Equiv.Perm.SameCycle.setoid h.σ))
    (hO : h.σ (Quotient.out O) ≠ Quotient.out O) :
    (Finset.univ.filter (fun v : V =>
        Quotient.mk (Equiv.Perm.SameCycle.setoid h.σ) v = O)).card = 11 := by
  rw [show 11 = (Finset.range 11).card from (Finset.card_range 11).symm]
  symm
  apply Finset.card_bij (fun (d : ℕ) (_ : d ∈ Finset.range 11) => (h.σ ^ d) (Quotient.out O))
  · -- hi: σ^d (out O) ∈ fiber O.
    intro d _
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    have h_setoid_r : (Equiv.Perm.SameCycle.setoid h.σ).r
        (Quotient.out O) ((h.σ ^ d) (Quotient.out O)) :=
      ⟨(d : ℤ), by rw [zpow_natCast]⟩
    have h_mk_step : Quotient.mk (Equiv.Perm.SameCycle.setoid h.σ)
                       ((h.σ ^ d) (Quotient.out O)) =
                     Quotient.mk (Equiv.Perm.SameCycle.setoid h.σ) (Quotient.out O) :=
      (Quotient.sound h_setoid_r).symm
    rw [h_mk_step]
    exact Quotient.out_eq O
  · -- inj: σ^d₁ rep = σ^d₂ rep ⟹ d₁ = d₂.
    intro d₁ hd₁ d₂ hd₂ heq
    rw [Finset.mem_range] at hd₁ hd₂
    exact σ_pow_apply_injective_of_free h hO hd₁ hd₂ heq
  · -- surj: any v in fiber, ∃ d ∈ range 11, σ^d rep = v.
    intro v hv
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv
    have h_sc : h.σ.SameCycle (Quotient.out O) v := by
      have h_mk_eq : Quotient.mk (Equiv.Perm.SameCycle.setoid h.σ) v =
                     Quotient.mk (Equiv.Perm.SameCycle.setoid h.σ) (Quotient.out O) := by
        rw [hv]; exact (Quotient.out_eq _).symm
      exact (Quotient.exact h_mk_eq).symm
    obtain ⟨i, hi⟩ := h_sc
    -- σ^i (out O) = v with i ∈ ℤ. Use σ^11 = 1 to find d ∈ ℕ with d < 11.
    have h_σ11 : (h.σ : Equiv.Perm V) ^ (11 : ℤ) = 1 := by
      rw [show ((11 : ℤ)) = ((11 : ℕ) : ℤ) from rfl, zpow_natCast]; exact h.σ_pow_eleven
    have h_emod_nonneg : 0 ≤ i % 11 := Int.emod_nonneg _ (by decide)
    have h_emod_lt : i % 11 < 11 := Int.emod_lt_of_pos _ (by decide)
    set d : ℕ := (i % 11).toNat with hd_def
    have h_d_eq : (d : ℤ) = i % 11 := Int.toNat_of_nonneg h_emod_nonneg
    have h_d_lt : d < 11 := by
      have : (d : ℤ) < 11 := h_d_eq ▸ h_emod_lt
      exact_mod_cast this
    have h_z : ((h.σ : Equiv.Perm V) ^ (i % 11)) (Quotient.out O) = v := by
      have h_eq_i : i = (i % 11) + 11 * (i / 11) := by
        have := Int.emod_add_ediv i 11
        linarith
      have h_zpow_eq : h.σ ^ i = h.σ ^ (i % 11) := by
        conv_lhs => rw [h_eq_i]
        rw [zpow_add, zpow_mul, h_σ11, one_zpow, mul_one]
      rw [← h_zpow_eq]; exact hi
    refine ⟨d, Finset.mem_range.mpr h_d_lt, ?_⟩
    have h_cast : (h.σ ^ d) (Quotient.out O) =
                  ((h.σ : Equiv.Perm V) ^ (i % 11)) (Quotient.out O) := by
      rw [← h_d_eq]; simp [zpow_natCast]
    rw [h_cast, h_z]

/-- **Orbital side of trace identity** (sorry-free!):
`trace(A_restrict over ker T_F11) = (10 * traceNumber : ZMod 11)`.

## 数学的内容 (Macaj-Siran/Cameron Higman framework)

中核: 整数行列レベルで `trace(A · P_int) = 110 n` (where `P_int = Σ_{k=0}^{10} σ^k`),
そこから軌道基底経由で `trace(A | ker T_F11) = 10 n` を引き出す.

### Step 1: 整数 trace identity (using `Tk_eq_eleven_mul_traceNumber`)

`Tk_eq_eleven_mul_traceNumber : T_k = 11n` for `k = 1..10` (既証, over ℚ).
`T_0 = trace(A) = 0` (no loops).

`Σ_{k=0}^{10} T_k = 0 + 10 · 11n = 110n` over ℤ.

### Step 2: `trace(A · P_int) = 110n`

`P_int = Σ_{k=0}^{10} σ^k` as ℤ-matrix.
`trace(A · P_int) = Σ_k trace(A σ^k) = Σ_k T_k = 110n`.

### Step 3: P_int の軌道構造

`P_int(u, v) = #{k ∈ [0, 10] : σ^k(v) = u}`:
- `v = u` fixed: `11`
- `u ∈ orbit(v), u ≠ v`: `1`
- `v free, u = v`: `1` (k=0)
- それ以外: `0`

`(A · P_int)(v, v) = Σ_u A(v, u) P_int(u, v)`:
- `v` fixed: `= 11 · A(v, v) = 0`
- `v` free: `= Σ_{u ∈ orbit(v)} A(v, u) = |N(v) ∩ orbit(v)|`

`trace(A · P_int) = Σ_{v free} |N(v) ∩ orbit(v)| = 2 · #{internal edges in free orbits} = 110n`.

### Step 4: σ-不変性で軌道平均

各 free orbit `O` で `|N(v) ∩ O|` は `v ∈ O` で一定 (`σ`-equivariance).
`11 · |N(v_O) ∩ O| = Σ_{v ∈ O} |N(v) ∩ O|`.

### Step 5: 軌道基底 trace の計算

`ker T_F11 ≃ (V/σ → F_11)` via `funLeft (Quotient.mk s)`.
軌道基底 `{1_O : O ∈ V/σ}` の下で `A_restrict` の matrix:
`[A_restrict]_{O', O} = |N(v_{O'}) ∩ O|` (F_11 cast).

対角 `[A_restrict]_{O, O} = |N(v_O) ∩ O|`:
- `O` fixed (singleton): `0`.
- `O` free: `(1/11) · Σ_v ∈ O |N(v) ∩ O| = (2/11) · #(internal edges in O)`.

`#(internal edges in O)` is divisible by 11 (σ acts freely on edges within O,
each edge orbit has length exactly 11 since |O|=11 prime).

So `|N(v_O) ∩ O| = 2 m_O` where `m_O := #(internal edges in O)/11 ∈ ℕ`.

### Step 6: 総和 = 10n

`Σ_O |N(v_O) ∩ O| = Σ_O free 2 m_O = (2/11) · Σ_O #(internal edges in O)
                  = (2/11) · 55n = 10n`.

(Using Step 4 sum identity = 110n divided by 11 averaging.)

So `trace(A_restrict) = Σ_O |N(v_O) ∩ O| = 10n` over ℤ. Mod 11: `10n mod 11`.

## Lean 形式化の現状 (2026-05-17, 多数 commits)

実装済み (sorry-free):
1. ✓ `kerTF11_quotientEquiv : (Quotient s → F_11) ≃ₗ ker T_F11`.
2. ✓ `trace_adjMatrixF11_restrict_eq_trace_quot` (LinearMap.trace_conj').
3. ✓ `trace_adjMatrixF11_quot_eq_sum` (Pi.basisFun 経由).
4. ✓ `adjMatrixF11_quot_basisFun_eq_orbitNeighborSumQuot`.
5. ✓ `adjMatrixF11_quot_diagonal_eq_orbitNeighborSumF11_out` (Quotient.inductionOn + σ-inv).
6. ✓ `trace_adjMatrixF11_restrict_eq_sum_over_vertices`:
   `trace = Σ_w (adjMatrixF11 Γ) (Quotient.out (Quotient.mk w)) w` (in F_11).

**残作業** (sorry-free 化可能, ~60-100 行):
`Σ_w (adjMatrixF11 Γ) (Quotient.out (Quotient.mk w)) w = ((10 * traceNumber : ℕ) : ZMod 11)`.

戦略:
- LHS = (count : F_11) where count = #{w : Γ.Adj (rep(w)) w}, rep(w) = Quotient.out (Quotient.mk w).
- count を σ-orbit + slope analysis で 10n と identify:
  - For each free orbit O, w ∈ O iff w = σ^k (rep_O) for unique k ∈ {0..10}.
  - count = Σ_O free #{k ∈ {0..10} : Γ.Adj (rep_O) (σ^k rep_O)}.
  - For k = 0: false (no loops).
  - For k ∈ {1..10}: by σ-invariance, #{O : Γ.Adj rep (σ^k rep)} = T_k / 11 = n.
  - count = Σ_{k=1..10} n = 10n.
- Uses: `Tk_eq_eleven_mul_traceNumber : T_k = 11n` (sorry-free, 既存).

依存: 主に既存 `Tk_eq_eleven_mul_traceNumber` + `Equiv.Perm.cycleOf`/`SameCycle` machinery
for orbit bijection. ~60-100 lines.

## 戦略的位置付け (2026-05-17 web search + analysis)

このルートは Macaj-Siran 2010 (`tmp/pdfs/j.laa.2009.07.018.txt`) の Higman trace
identity を F_11 へ persist する形. `a_F11_7 = 159` (good reduction) が独立必要
であるため, 本 sorry を閉じても次の sorry が残る. しかし trace identity を
完全に分離することで, Phase 4F11Spectral の各部品が明確化される.

軌道側 trace identity の **約 90%** が今日 sorry-free 化された.
残るは 1 つの集計 (count = 10n) のみ. -/
theorem trace_adjMatrixF11_restrict_eq_orbital_side
    (h : Order22ActsOnMoore57 V Γ) :
    LinearMap.trace (ZMod 11) _ h.adjMatrixF11_restrict_ker_T =
      ((10 * h.traceNumber : ℕ) : ZMod 11) := by
  classical
  haveI : DecidableRel (Equiv.Perm.SameCycle.setoid h.σ).r := fun _ _ => Classical.dec _
  haveI : Fintype (Quotient (Equiv.Perm.SameCycle.setoid h.σ)) := Quotient.fintype _
  rw [trace_adjMatrixF11_restrict_eq_sum_over_vertices]
  -- Goal: Σ_w (adjMatrixF11 Γ) (Quotient.out (Quotient.mk w)) w = ((10n : ℕ) : ZMod 11)
  -- Step A: Convert each matrix entry to if-then-else form.
  have h_unfold : (∑ w : V, (adjMatrixF11 Γ)
        (Quotient.out (Quotient.mk (Equiv.Perm.SameCycle.setoid h.σ) w)) w) =
      ∑ w : V, (if Γ.Adj
          (Quotient.out (Quotient.mk (Equiv.Perm.SameCycle.setoid h.σ) w)) w
        then (1 : ZMod 11) else 0) := by
    apply Finset.sum_congr rfl
    intro w _
    unfold adjMatrixF11
    rw [SimpleGraph.adjMatrix_apply]
  rw [h_unfold]
  -- Step B: sum_boole to convert to count cast.
  rw [Finset.sum_boole]
  -- Goal: (#{w ∈ univ | Γ.Adj (rep w) w} : ZMod 11) = ((10 * n : ℕ) : ZMod 11)
  -- Step C: prove count = 10n in ℕ via orbit partition + Tk identity.
  -- Sub-step C1: Σ_d=0..10 T_d = 110n (T_0 = 0, T_k = 11n for k ∈ 1..10).
  have h_sum_Tk : ∑ d ∈ Finset.range 11, h.Tk d = 110 * h.traceNumber := by
    have h_T0 : h.Tk 0 = 0 := by
      unfold Tk
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro x _
      simp only [pow_zero, Equiv.Perm.coe_one, id_eq]
      exact SimpleGraph.irrefl Γ
    -- Finset.range 11 = insert 0 (Finset.Ioo 0 11) or use Finset.sum_range_succ_comm
    have h_split : Finset.range 11 = insert 0 (Finset.Ioc 0 10) := by
      ext d
      simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Ioc]
      omega
    rw [h_split, Finset.sum_insert (by simp), h_T0, zero_add]
    -- Σ_{d ∈ Ioc 0 10} h.Tk d = 110n
    have h_each : ∀ d ∈ Finset.Ioc 0 10, h.Tk d = 11 * h.traceNumber := by
      intro d hd
      rw [Finset.mem_Ioc] at hd
      exact h.Tk_eq_eleven_mul_traceNumber hd.1 hd.2
    rw [Finset.sum_congr rfl h_each]
    rw [Finset.sum_const, Nat.card_Ioc, Nat.sub_zero, smul_eq_mul]
    ring
  -- Sub-step C2: Σ_v |allOrbitNeighbors v| = Σ_d T_d via Finset.sum_comm.
  have h_v_sum_Tk : (∑ v : V, ((Finset.range 11).filter
        (fun d => Γ.Adj v ((h.σ ^ d) v))).card) = ∑ d ∈ Finset.range 11, h.Tk d := by
    classical
    have heq_v : ∀ v : V,
        ((Finset.range 11).filter (fun d => Γ.Adj v ((h.σ ^ d) v))).card =
        ∑ d ∈ Finset.range 11, (if Γ.Adj v ((h.σ ^ d) v) then 1 else 0 : ℕ) := by
      intro v
      rw [Finset.card_filter]
    simp_rw [heq_v]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intros d _
    rw [show ∑ v : V, (if Γ.Adj v ((h.σ ^ d) v) then 1 else 0 : ℕ) =
      (Finset.univ.filter (fun v : V => Γ.Adj v ((h.σ ^ d) v))).card from
      (Finset.card_filter _ _).symm]
    rfl
  -- Combine: Σ_v |allOrbitNeighbors v| = 110n.
  have h_v_sum_eq_110n : (∑ v : V, ((Finset.range 11).filter
        (fun d => Γ.Adj v ((h.σ ^ d) v))).card) = 110 * h.traceNumber := by
    rw [h_v_sum_Tk, h_sum_Tk]
  -- Sub-step C3: 11 * count = Σ_v |allOrbitNeighbors v| (via sigma-invariance + orbit partition).
  -- Recognize that Σ_v |allOrbitNeighbors v| = Σ_v orbitNeighborCountN v.
  have h_v_sum_eq_onc :
      (∑ v : V, ((Finset.range 11).filter
        (fun d => Γ.Adj v ((h.σ ^ d) v))).card) = ∑ v : V, h.orbitNeighborCountN v := rfl
  -- C3a: Σ_v onc v = 11 * Σ_O onc(rep_O).
  have h_v_sum_eq_11_sum_O :
      (∑ v : V, h.orbitNeighborCountN v) =
      11 * ∑ O : Quotient (Equiv.Perm.SameCycle.setoid h.σ),
              h.orbitNeighborCountN (Quotient.out O) := by
    have h_maps : ∀ v ∈ (Finset.univ : Finset V),
        Quotient.mk (Equiv.Perm.SameCycle.setoid h.σ) v ∈
          (Finset.univ : Finset (Quotient (Equiv.Perm.SameCycle.setoid h.σ))) :=
      fun _ _ => Finset.mem_univ _
    rw [← Finset.sum_fiberwise_of_maps_to h_maps h.orbitNeighborCountN]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro O _
    -- Inner sum = 11 * onc rep_O.
    by_cases hO : h.σ (Quotient.out O) = Quotient.out O
    · -- Fixed: fiber = {rep}, onc rep = 0, sum = 0 = 11 * 0.
      rw [show ({v ∈ Finset.univ | Quotient.mk (Equiv.Perm.SameCycle.setoid h.σ) v = O} :
            Finset V) =
          Finset.univ.filter (fun v : V =>
            Quotient.mk (Equiv.Perm.SameCycle.setoid h.σ) v = O) from rfl,
          σ_fiber_eq_singleton_of_fixed h O hO]
      rw [Finset.sum_singleton, orbitNeighborCountN_eq_zero_of_fixed h hO, mul_zero]
    · -- Free: all values equal onc rep, sum = 11 * onc rep.
      have h_const : ∀ v ∈ Finset.univ.filter (fun v : V =>
          Quotient.mk (Equiv.Perm.SameCycle.setoid h.σ) v = O),
          h.orbitNeighborCountN v = h.orbitNeighborCountN (Quotient.out O) := by
        intro v hv
        simp only [Finset.mem_filter] at hv
        have h_mk : Quotient.mk (Equiv.Perm.SameCycle.setoid h.σ) v =
                    Quotient.mk _ (Quotient.out O) := by
          rw [hv.2]; exact (Quotient.out_eq _).symm
        have h_sc : (Equiv.Perm.SameCycle.setoid h.σ).r v (Quotient.out O) :=
          Quotient.exact h_mk
        exact h.orbitNeighborCountN_sameCycle v _ h_sc
      rw [show ({v ∈ Finset.univ | Quotient.mk (Equiv.Perm.SameCycle.setoid h.σ) v = O} :
            Finset V) =
          Finset.univ.filter (fun v : V =>
            Quotient.mk (Equiv.Perm.SameCycle.setoid h.σ) v = O) from rfl]
      rw [Finset.sum_congr rfl h_const, Finset.sum_const, smul_eq_mul]
      rw [σ_fiber_card_eq_eleven_of_free h O hO]
  -- C3b: count = Σ_O onc(rep_O).
  have h_count_eq_sum_O :
      (Finset.univ.filter (fun w : V =>
          Γ.Adj (Quotient.out (Quotient.mk (Equiv.Perm.SameCycle.setoid h.σ) w)) w)).card =
      ∑ O : Quotient (Equiv.Perm.SameCycle.setoid h.σ),
        h.orbitNeighborCountN (Quotient.out O) := by
    -- Partition the count by Quotient.mk.
    rw [Finset.card_filter]
    have h_maps : ∀ v ∈ (Finset.univ : Finset V),
        Quotient.mk (Equiv.Perm.SameCycle.setoid h.σ) v ∈
          (Finset.univ : Finset (Quotient (Equiv.Perm.SameCycle.setoid h.σ))) :=
      fun _ _ => Finset.mem_univ _
    rw [← Finset.sum_fiberwise_of_maps_to h_maps
        (fun w : V =>
          (if Γ.Adj (Quotient.out (Quotient.mk
            (Equiv.Perm.SameCycle.setoid h.σ) w)) w then 1 else 0 : ℕ))]
    apply Finset.sum_congr rfl
    intro O _
    -- Inner: ∑ w ∈ filter (Q.mk · = O), [Adj (Quot.out (Quot.mk w)) w] = onc rep_O.
    -- For each w in filter, Quot.mk w = O, so Quot.out (Quot.mk w) = Quot.out O = rep_O.
    -- Inner = #{w ∈ fiber O : Adj rep_O w}.
    by_cases hO : h.σ (Quotient.out O) = Quotient.out O
    · -- Fixed: inner sum = 0 (fiber = {rep}, no loops). onc rep = 0.
      rw [σ_fiber_eq_singleton_of_fixed h O hO]
      rw [Finset.sum_singleton, orbitNeighborCountN_eq_zero_of_fixed h hO]
      rw [Quotient.out_eq O]
      rw [if_neg (SimpleGraph.irrefl Γ)]
    · -- Free: bijection σ^· : range 11 ↔ fiber O.
      -- Step 1: substitute Quot.out (Quot.mk _ w) with Quot.out O in the if-condition.
      have h_substitute :
          (∑ w ∈ Finset.univ.filter (fun w : V =>
              Quotient.mk (Equiv.Perm.SameCycle.setoid h.σ) w = O),
              (if Γ.Adj (Quotient.out (Quotient.mk
                (Equiv.Perm.SameCycle.setoid h.σ) w)) w then 1 else 0 : ℕ)) =
          (∑ w ∈ Finset.univ.filter (fun w : V =>
              Quotient.mk (Equiv.Perm.SameCycle.setoid h.σ) w = O),
              (if Γ.Adj (Quotient.out O) w then 1 else 0 : ℕ)) := by
        apply Finset.sum_congr rfl
        intro w hw
        simp only [Finset.mem_filter] at hw
        rw [show Quotient.out (Quotient.mk (Equiv.Perm.SameCycle.setoid h.σ) w) =
              Quotient.out O from by rw [hw.2]]
      rw [h_substitute]
      -- Step 2: sum_boole + filter_filter to convert to card.
      rw [Finset.sum_boole]
      rw [Finset.filter_filter]
      -- Goal: (univ.filter (Q.mk · = O ∧ Adj (Quot.out O) ·)).card = onc rep_O.
      -- Step 3: bijection σ^· : range 11 (filtered) ↔ filter.
      unfold orbitNeighborCountN
      symm
      apply Finset.card_bij
        (fun (d : ℕ) (_ : d ∈ (Finset.range 11).filter
          (fun d => Γ.Adj (Quotient.out O) ((h.σ ^ d) (Quotient.out O)))) =>
            (h.σ ^ d) (Quotient.out O))
      · -- hi
        intro d hd
        simp only [Finset.mem_filter, Finset.mem_range] at hd
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        refine ⟨?_, hd.2⟩
        have h_setoid_r : (Equiv.Perm.SameCycle.setoid h.σ).r
            (Quotient.out O) ((h.σ ^ d) (Quotient.out O)) :=
          ⟨(d : ℤ), by rw [zpow_natCast]⟩
        have h_mk_step :
            Quotient.mk (Equiv.Perm.SameCycle.setoid h.σ)
              ((h.σ ^ d) (Quotient.out O)) =
            Quotient.mk (Equiv.Perm.SameCycle.setoid h.σ) (Quotient.out O) :=
          (Quotient.sound h_setoid_r).symm
        rw [h_mk_step]; exact Quotient.out_eq O
      · -- inj
        intro d₁ hd₁ d₂ hd₂ heq
        rw [Finset.mem_filter, Finset.mem_range] at hd₁ hd₂
        exact σ_pow_apply_injective_of_free h hO hd₁.1 hd₂.1 heq
      · -- surj
        intro v hv
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv
        obtain ⟨h_mk_v, h_adj_v⟩ := hv
        have h_sc : h.σ.SameCycle (Quotient.out O) v := by
          have h_eq : Quotient.mk (Equiv.Perm.SameCycle.setoid h.σ) v =
                      Quotient.mk _ (Quotient.out O) := by
            rw [h_mk_v]; exact (Quotient.out_eq _).symm
          exact (Quotient.exact h_eq).symm
        obtain ⟨i, hi⟩ := h_sc
        have h_σ11 : (h.σ : Equiv.Perm V) ^ (11 : ℤ) = 1 := by
          rw [show ((11 : ℤ)) = ((11 : ℕ) : ℤ) from rfl, zpow_natCast]
          exact h.σ_pow_eleven
        have h_emod_nonneg : 0 ≤ i % 11 := Int.emod_nonneg _ (by decide)
        have h_emod_lt : i % 11 < 11 := Int.emod_lt_of_pos _ (by decide)
        set d : ℕ := (i % 11).toNat with hd_def
        have h_d_eq : (d : ℤ) = i % 11 := Int.toNat_of_nonneg h_emod_nonneg
        have h_d_lt : d < 11 := by
          have : (d : ℤ) < 11 := h_d_eq ▸ h_emod_lt
          exact_mod_cast this
        have h_zpow_eq : h.σ ^ i = h.σ ^ (i % 11) := by
          have h_eq_i : i = (i % 11) + 11 * (i / 11) := by
            have := Int.emod_add_ediv i 11
            linarith
          conv_lhs => rw [h_eq_i]
          rw [zpow_add, zpow_mul, h_σ11, one_zpow, mul_one]
        have h_apply : (h.σ ^ d) (Quotient.out O) = v := by
          have h_cast : (h.σ ^ d) (Quotient.out O) =
                        ((h.σ : Equiv.Perm V) ^ (i % 11)) (Quotient.out O) := by
            rw [← h_d_eq]; simp [zpow_natCast]
          rw [h_cast, ← h_zpow_eq, hi]
        refine ⟨d, ?_, h_apply⟩
        simp only [Finset.mem_filter, Finset.mem_range]
        refine ⟨h_d_lt, ?_⟩
        rw [h_apply]; exact h_adj_v
  -- Combine: 11 * count = 11 * Σ_O onc rep_O = Σ_v onc v = 110n. Hence count = 10n.
  have h_11count_eq_110n :
      11 * (Finset.univ.filter (fun w : V =>
          Γ.Adj (Quotient.out (Quotient.mk (Equiv.Perm.SameCycle.setoid h.σ) w)) w)).card =
      110 * h.traceNumber := by
    rw [h_count_eq_sum_O, ← h_v_sum_eq_11_sum_O, ← h_v_sum_eq_onc, h_v_sum_eq_110n]
  have h_count_eq_10n :
      (Finset.univ.filter (fun w : V =>
          Γ.Adj (Quotient.out (Quotient.mk (Equiv.Perm.SameCycle.setoid h.σ) w)) w)).card =
      10 * h.traceNumber := by
    have : 11 * (Finset.univ.filter (fun w : V =>
        Γ.Adj (Quotient.out (Quotient.mk (Equiv.Perm.SameCycle.setoid h.σ) w)) w)).card =
        11 * (10 * h.traceNumber) := by
      rw [h_11count_eq_110n]; ring
    exact Nat.eq_of_mul_eq_mul_left (by omega) this
  -- Cast count = 10n to ZMod 11.
  push_cast
  rw [h_count_eq_10n]
  push_cast
  rfl

/-- **F_11 trace identity** (sorry-free!):
`10 * traceNumber ≡ 2 · a^{F_11}_2 + 7 · a^{F_11}_7 + 3 · a^{F_11}_3 (mod 11)`.

Direct corollary of spectral side + orbital side (both sorry-free).
Both sides equal `LinearMap.trace _ _ adjMatrixF11_restrict_ker_T`. -/
theorem trace_identity_via_F11_spectral (h : Order22ActsOnMoore57 V Γ) :
    (10 * h.traceNumber : ZMod 11) =
      (2 : ZMod 11) *
        ((Module.finrank (ZMod 11)
          (V2Submodule Γ ⊓ LinearMap.ker (T_F11 h) :
            Submodule (ZMod 11) (V → ZMod 11)) : ℕ) : ZMod 11)
    + (7 : ZMod 11) *
        ((Module.finrank (ZMod 11)
          (V7Submodule Γ ⊓ LinearMap.ker (T_F11 h) :
            Submodule (ZMod 11) (V → ZMod 11)) : ℕ) : ZMod 11)
    + (3 : ZMod 11) *
        ((Module.finrank (ZMod 11)
          (V3Submodule Γ ⊓ LinearMap.ker (T_F11 h) :
            Submodule (ZMod 11) (V → ZMod 11)) : ℕ) : ZMod 11) := by
  have h_spec := trace_adjMatrixF11_restrict_eq_spectral_side h
  have h_orb := trace_adjMatrixF11_restrict_eq_orbital_side h
  push_cast at h_orb
  rw [← h_orb, h_spec]

/-! ## 上界証明の主結果 -/

/-- **F_11 spectral trace argument**:
`10 * traceNumber ≡ 6 (mod 11)`.

合成: `trace_identity_via_F11_spectral` + a^{F_11}_λ 値 (1, 159, 140)
⟹ 10n ≡ 2·1 + 7·159 + 3·140 ≡ 1535 ≡ 6 mod 11. -/
theorem ten_traceNumber_mod_eleven_eq_six_via_F11_spectral
    (h : Order22ActsOnMoore57 V Γ) :
    10 * h.traceNumber % 11 = 6 := by
  have h_id := trace_identity_via_F11_spectral h
  rw [aF11_lambda_two_eq_one h, aF11_lambda_seven_eq_159 h,
      aF11_lambda_three_eq_140 h] at h_id
  -- h_id : 10 * (h.traceNumber : ZMod 11) = 2 * ↑1 + 7 * ↑159 + 3 * ↑140 (in ZMod 11)
  -- Bridge to mod arithmetic: cast ℕ versions, use ZMod.natCast_eq_natCast_iff.
  have h_six : ((10 * h.traceNumber : ℕ) : ZMod 11) = ((6 : ℕ) : ZMod 11) := by
    push_cast
    rw [h_id]
    decide
  have h_modeq : 10 * h.traceNumber % 11 = 6 % 11 :=
    (ZMod.natCast_eq_natCast_iff _ _ 11).mp h_six
  omega

/-- **Phase D 主結果**: `a_7 ≤ 160` (実際は = 159).

`ten_traceNumber_mod_eleven_eq_six_via_F11_spectral` + Phase 3 候補
`traceNumber_mem_candidates` の合成. -/
theorem a7_le_160_via_F11_spectral_proof (h : Order22ActsOnMoore57 V Γ) :
    ∃ a : ℕ, (3 * a : ℤ) = 2 * (h.traceNumber : ℤ) + 467 ∧ a ≤ 160 := by
  -- Step 1: F_11 trace argument gives 10n ≡ 6 (mod 11)
  have h_mod : 10 * h.traceNumber % 11 = 6 :=
    h.ten_traceNumber_mod_eleven_eq_six_via_F11_spectral
  -- Step 2: Phase 3 candidates n ∈ {5, 20, 35, 50}. Only n = 5 has 10n ≡ 6 (mod 11):
  --   10·5 = 50 ≡ 6, 10·20 = 200 ≡ 2, 10·35 = 350 ≡ 9, 10·50 = 500 ≡ 5 (mod 11).
  have h_n : h.traceNumber = 5 := by
    rcases h.traceNumber_mem_candidates with h5 | h20 | h35 | h50
    · exact h5
    · exfalso; rw [h20] at h_mod; omega
    · exfalso; rw [h35] at h_mod; omega
    · exfalso; rw [h50] at h_mod; omega
  -- Step 3: With n = 5, witness a = 159: 3·159 = 477 = 2·5 + 467
  refine ⟨159, ?_, by decide⟩
  rw [h_n]
  decide

end Order22ActsOnMoore57

end Moore57
