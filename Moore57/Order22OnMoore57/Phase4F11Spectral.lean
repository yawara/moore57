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
    have h_no_loop : ¬ Γ.Adj v v := Γ.loopless.irrefl v
    simp [h_no_loop]
    decide
  · by_cases hadj : Γ.Adj v w
    · simp [hvw, hadj]
    · simp [hvw, hadj]

/-- F_11 上 `(A - 2 I)(A - 7 I)(A - 3 I) = 0` (Q charpoly mod 11 factorization). -/
theorem adjMatrixF11_cubic_eq_zero (hΓ : IsMoore57 Γ) :
    (adjMatrixF11 Γ - (2 : ZMod 11) • 1) *
    (adjMatrixF11 Γ - (7 : ZMod 11) • 1) *
    (adjMatrixF11 Γ - (3 : ZMod 11) • 1) = 0 := by
  sorry

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
