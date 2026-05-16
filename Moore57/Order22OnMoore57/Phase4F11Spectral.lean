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

/-! ## 上界証明の主結果 (focused sorry) -/

/-- **Phase D 主結果 (sorry, F_11 spectral)**: `a_7 ≤ 160`. -/
theorem a7_le_160_via_F11_spectral_proof (h : Order22ActsOnMoore57 V Γ) :
    ∃ a : ℕ, (3 * a : ℤ) = 2 * (h.traceNumber : ℤ) + 467 ∧ a ≤ 160 := by
  -- 戦略 outline:
  -- 1. F_11 spectral: V_F_11 = V_2 ⊕ V_7 ⊕ V_3 (E_λ idempotent + orthogonal + sum = I).
  -- 2. σ-equivariance: V_λ は σ-invariant.
  -- 3. Restricted Jordan: 各 V_λ 内 (σ - I)^11 = 0, dim ker(...)_j 線形.
  -- 4. a^{F_11}_7 + 10 k_7 = 1729 (dim V_7), l_7 ≥ 0 ⟹ a^{F_11}_7 ≥ 158.
  --    a^{F_11}_3 + 10 k_3 = 1520, l_3 ≥ 0 ⟹ a^{F_11}_3 ≥ 140.
  -- 5. Sum a^{F_11}_2 + a^{F_11}_7 + a^{F_11}_3 = 300 ⟹ a^{F_11}_7 = 300 - 1 - a^{F_11}_3 ≤ 159.
  -- 6. Kernel monotonicity: a_7 ≤ a^{F_11}_7 ≤ 159 ≤ 160.
  -- 7. Phase 3: ∃ a, 3a = 2n + 467 ∧ a ≤ 160.
  sorry

end Order22ActsOnMoore57

end Moore57
