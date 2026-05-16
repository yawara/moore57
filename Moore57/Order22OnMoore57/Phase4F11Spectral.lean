import Moore57.Order22OnMoore57.Phase3FourCycleBound
import Moore57.Order22OnMoore57.Phase4F11OrbitKernel
import Moore57.Order22OnMoore57.TraceNumber
import Mathlib.Algebra.Polynomial.Eval.Defs

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

/-- F_11 modular rep theory **基幹 sorry**:
`a^{F_11}_7 := dim(V_7 ∩ ker T_F11) = 159`.

証明戦略 (依存):
A. `dim V_7 over F_11 = 1729` — good reduction of rational rank.
   * `IsMoore57.trace_E7Matrix_one : trace(E_7) = 1729` over ℚ (existing).
   * Idempotent rank = trace ⟹ rank E_7 over ℚ = 1729.
   * E_7 has integer entries scaled by units of ℤ_(11). Reduce mod 11.
   * rank preservation under good reduction (denominators 15, 750 coprime to 11).
B. `Σ l_λ = 5` — F_11[C_11] structure of V_perm = M_1^5 ⊕ M_11^{295}.
   * Already have Σ a^{F_11}_λ = 300 (sorry-free), Σ k_λ = k_7 + k_3 + 0 = 295.
   * l_λ := a^{F_11}_λ - k_λ ≥ 0 (from Im T^10 ⊆ ker T proved).
   * Σ l_λ = 300 - 295 = 5 (provable directly from above).
C. `l_7 ≡ dim V_7 mod 11 = 2` — F_11[C_11] structure (M_11 contributes 0 to σ-trace).
   * Via trace(σ E_7) over F_11 = 2 (Higman + matrix computation).
   * Identifies trace(σ on V_7) = l_7 over F_11.
D. `l_7 = 2` — combining B (l_7 ≤ 4 from Σ = 5 and l_2 = 1, l_3 ≥ 0) + C (mod 11).
E. `k_7 = 157` — A + D: dim V_7 = 11 k_7 + l_7 = 1729 = 11·157 + 2.
F. `a^{F_11}_7 = l_7 + k_7 = 2 + 157 = 159`.

主依存: A (good reduction) + C (F_11[C_11] σ-trace identification) — substantial. -/
theorem aF11_lambda_seven_eq_159 (h : Order22ActsOnMoore57 V Γ) :
    Module.finrank (ZMod 11)
        (V7Submodule Γ ⊓ LinearMap.ker (T_F11 h) :
          Submodule (ZMod 11) (V → ZMod 11)) = 159 := by
  sorry

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

/-! ### F_11 trace identity (orbit + spectral bridge) -/

/-- F_11 trace identity **基幹 sorry** (orbit + spectral bridge):
`10 * traceNumber ≡ 2 · a^{F_11}_2 + 7 · a^{F_11}_7 + 3 · a^{F_11}_3 (mod 11)`.

orbital basis:
  trace(A | ker T_F11) = 10n (mod 11)  -- σ-不変性 + Tk_constant.
spectral basis:
  trace(A | ker T_F11) = Σ_λ λ · dim(V_λ ∩ ker T_F11) over F_11.
  (A·E_λ = λ·E_λ から V_λ 上 A は λ·I で作用.)

Both equal: `10n ≡ Σ λ · a^{F_11}_λ mod 11`.

証明戦略 (主依存):
* A_F11 が ker T_F11 を保つ (A と σ が可換).
* `A.restrict ker T : ker T → ker T` で trace を取れる.
* Spectral side: trace = Σ_λ λ · trace(E_λ | ker T).
  - Mathlib `IsProj.trace`: idempotent の trace = rank of image.
  - `E_λ | ker T` is a projection onto `V_λ ∩ ker T` (E_λ idem + commutes σ).
  - trace(E_λ | ker T) = dim(V_λ ∩ ker T) = a^{F_11}_λ.
* Orbital side: trace via orbital basis = Σ_O free orbit |N(v_O) ∩ O| · 1.
  - 各 free orbit O: diagonal coefficient = |N(v_O) ∩ O|.
  - Sum = 10n (via Tk_constant + σ-equivariance).
* Both equal.

主依存: `LinearMap.trace` machinery + explicit orbit-basis trace computation.
~250-300 lines. -/
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
  sorry

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
