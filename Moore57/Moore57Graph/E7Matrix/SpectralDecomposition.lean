import Moore57.Moore57Graph.E7Matrix.Idempotent
import Moore57.Moore57Graph.E7Matrix.PermutationCommutation
import Mathlib.Tactic.Abel

/-!
# Moore57 隣接行列の有理固有空間分解

Moore graph of degree 57 (SRG (3250, 57, 0, 1)) の隣接行列 `A` は
有理固有値 57, 7, -8 を持つ. 対応する直交べき等射影行列

* `E57Matrix V = (1/3250) J` — 57-固有空間 (all-ones line, dim 1)
* `E7Matrix Γ` — 7-固有空間 (dim 1729; 既存)
* `EMinus8Matrix Γ = I - E7Matrix - E57Matrix` — -8 固有空間 (dim 1520)

について本ファイルでは

* 3 つすべて idempotent (`E_λ² = E_λ`)
* 直交 (`E_λ · E_λ' = 0` for λ ≠ λ')
* 和 = 単位行列 (`E_57 + E_7 + E_-8 = I`)
* 隣接行列の固有値分解 `A = 57 E_57 + 7 E_7 - 8 E_-8`

を示す. これにより `Tk_constant` の rep theory 引数の代数的基盤が整う.
-/

namespace Moore57

section HigmanTrace

open Matrix

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- Moore57 の 57-固有空間 (all-ones line) への射影行列. -/
noncomputable def E57Matrix (V : Type*) [Fintype V] : Matrix V V ℚ :=
  (1 / 3250 : ℚ) • allOnesMatrix V

/-- Moore57 の -8 固有空間への射影行列 (= I - E_7 - E_57). -/
noncomputable def EMinus8Matrix (Γ : SimpleGraph V) [DecidableRel Γ.Adj] :
    Matrix V V ℚ :=
  (1 : Matrix V V ℚ) - E7Matrix Γ - E57Matrix V

/-! ### Idempotency and orthogonality of E_57 -/

/-- `E_57² = E_57`. -/
theorem E57Matrix_mul_E57Matrix_eq_E57Matrix (hΓ : IsMoore57 Γ) :
    E57Matrix V * E57Matrix V = E57Matrix V := by
  classical
  ext v w
  have hJ2 := congrFun (congrFun (allOnesMatrix_mul_allOnesMatrix_of_moore hΓ) v) w
  simp only [E57Matrix, Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_apply,
    smul_eq_mul] at hJ2 ⊢
  rw [hJ2]
  ring

/-- `E_57 · E_7 = 0`. -/
theorem E57Matrix_mul_E7Matrix_eq_zero (hΓ : IsMoore57 Γ) :
    E57Matrix V * E7Matrix Γ = 0 := by
  classical
  ext v w
  have hJA := congrFun (congrFun (allOnesMatrix_mul_adjMatrix hΓ) v) w
  have hJ2 := congrFun (congrFun (allOnesMatrix_mul_allOnesMatrix_of_moore hΓ) v) w
  -- (J * E_7)(v, w) = (1/15) (JA + 8 J·I)(v, w) - (1/750) J²(v, w)
  -- = (1/15)(57 + 8) - (1/750)·3250 = 65/15 - 13/3 = 0
  simp only [E57Matrix, E7Matrix, Matrix.smul_mul, Matrix.mul_smul,
    Matrix.mul_sub, Matrix.mul_add, Matrix.mul_one,
    Matrix.smul_apply, Matrix.add_apply, Matrix.sub_apply,
    smul_eq_mul, Matrix.zero_apply] at hJA hJ2 ⊢
  rw [hJA, hJ2]
  by_cases hvw : v = w
  · subst w
    simp [allOnesMatrix]
    ring
  · simp [allOnesMatrix, hvw]
    ring

/-- `E_7 · E_57 = 0`. 対称形. -/
theorem E7Matrix_mul_E57Matrix_eq_zero (hΓ : IsMoore57 Γ) :
    E7Matrix Γ * E57Matrix V = 0 := by
  classical
  ext v w
  have hAJ := congrFun (congrFun (adjMatrix_mul_allOnesMatrix hΓ) v) w
  have hJ2 := congrFun (congrFun (allOnesMatrix_mul_allOnesMatrix_of_moore hΓ) v) w
  simp only [E57Matrix, E7Matrix, Matrix.smul_mul, Matrix.mul_smul,
    Matrix.sub_mul, Matrix.add_mul, Matrix.one_mul,
    Matrix.smul_apply, Matrix.add_apply, Matrix.sub_apply,
    smul_eq_mul, Matrix.zero_apply] at hAJ hJ2 ⊢
  rw [hAJ, hJ2]
  by_cases hvw : v = w
  · subst w
    simp [allOnesMatrix]
    ring
  · simp [allOnesMatrix]
    ring

/-! ### Sum decomposition and E_{-8} -/

/-- `E_57 + E_7 + E_{-8} = I` (定義より自明). -/
theorem E57_plus_E7_plus_EMinus8_eq_one :
    E57Matrix V + E7Matrix Γ + EMinus8Matrix Γ = 1 := by
  simp [EMinus8Matrix]
  abel

/-- `E_{-8}² = E_{-8}`. orthogonal idempotent から従う:
`E_-8² = (I - E_7 - E_57)² = I - 2(E_7 + E_57) + (E_7 + E_57)²`
`= I - 2 E_7 - 2 E_57 + E_7² + E_57² + 2 E_7 E_57`
`= I - 2 E_7 - 2 E_57 + E_7 + E_57 + 0 = I - E_7 - E_57 = E_-8`. -/
theorem EMinus8Matrix_mul_EMinus8Matrix_eq_EMinus8Matrix (hΓ : IsMoore57 Γ) :
    EMinus8Matrix Γ * EMinus8Matrix Γ = EMinus8Matrix Γ := by
  classical
  have hE7sq := E7Matrix_mul_E7Matrix_eq_E7Matrix hΓ
  have hE57sq := E57Matrix_mul_E57Matrix_eq_E57Matrix (V := V) hΓ
  have hE57E7 := E57Matrix_mul_E7Matrix_eq_zero (V := V) hΓ
  have hE7E57 := E7Matrix_mul_E57Matrix_eq_zero (V := V) hΓ
  simp only [EMinus8Matrix, sub_mul, mul_sub, mul_one, one_mul,
    hE7sq, hE57sq, hE57E7, hE7E57, sub_zero, zero_sub]
  abel

/-- `E_57 · E_{-8} = 0`. -/
theorem E57Matrix_mul_EMinus8Matrix_eq_zero (hΓ : IsMoore57 Γ) :
    E57Matrix V * EMinus8Matrix Γ = 0 := by
  classical
  have hE57sq := E57Matrix_mul_E57Matrix_eq_E57Matrix (V := V) hΓ
  have hE57E7 := E57Matrix_mul_E7Matrix_eq_zero (V := V) hΓ
  simp [EMinus8Matrix, mul_sub, mul_one, hE57sq, hE57E7]

/-- `E_{-8} · E_57 = 0`. -/
theorem EMinus8Matrix_mul_E57Matrix_eq_zero (hΓ : IsMoore57 Γ) :
    EMinus8Matrix Γ * E57Matrix V = 0 := by
  classical
  have hE57sq := E57Matrix_mul_E57Matrix_eq_E57Matrix (V := V) hΓ
  have hE7E57 := E7Matrix_mul_E57Matrix_eq_zero (V := V) hΓ
  simp [EMinus8Matrix, sub_mul, one_mul, hE57sq, hE7E57]

/-- `E_7 · E_{-8} = 0`. -/
theorem E7Matrix_mul_EMinus8Matrix_eq_zero (hΓ : IsMoore57 Γ) :
    E7Matrix Γ * EMinus8Matrix Γ = 0 := by
  classical
  have hE7sq := E7Matrix_mul_E7Matrix_eq_E7Matrix hΓ
  have hE7E57 := E7Matrix_mul_E57Matrix_eq_zero (V := V) hΓ
  simp [EMinus8Matrix, mul_sub, mul_one, hE7sq, hE7E57]

/-- `E_{-8} · E_7 = 0`. -/
theorem EMinus8Matrix_mul_E7Matrix_eq_zero (hΓ : IsMoore57 Γ) :
    EMinus8Matrix Γ * E7Matrix Γ = 0 := by
  classical
  have hE7sq := E7Matrix_mul_E7Matrix_eq_E7Matrix hΓ
  have hE57E7 := E57Matrix_mul_E7Matrix_eq_zero (V := V) hΓ
  simp [EMinus8Matrix, sub_mul, one_mul, hE7sq, hE57E7]

/-! ### Spectral decomposition of A -/

/-- 隣接行列の固有値分解: `A = 57 E_57 + 7 E_7 - 8 E_{-8}`. -/
theorem adjMatrix_eq_spectral_decomp (hΓ : IsMoore57 Γ) :
    Γ.adjMatrix ℚ =
      (57 : ℚ) • E57Matrix V + (7 : ℚ) • E7Matrix Γ - (8 : ℚ) • EMinus8Matrix Γ := by
  classical
  -- E_-8 = I - E_7 - E_57
  -- 57 E_57 + 7 E_7 - 8 (I - E_7 - E_57)
  -- = 57 E_57 + 7 E_7 - 8 I + 8 E_7 + 8 E_57
  -- = 65 E_57 + 15 E_7 - 8 I
  -- = 65 · (1/3250) J + 15 · ((1/15)(A + 8 I) - (1/750) J) - 8 I
  -- = J/50 + A + 8I - J/50 - 8I = A ✓
  simp only [EMinus8Matrix, E57Matrix, E7Matrix]
  ext v w
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply,
    Matrix.one_apply, allOnesMatrix, smul_eq_mul, mul_one]
  by_cases hvw : v = w
  · subst w; simp [Matrix.one_apply]; ring
  · simp [Matrix.one_apply, hvw]
    by_cases hadj : Γ.Adj v w
    · simp [hadj]; ring
    · simp [hadj]; ring

/-! ### Commutation with permutation matrices -/

/-- `E_57` は graph automorphism と交換する. -/
theorem E57Matrix_mul_permMatrix_eq_permMatrix_mul_E57Matrix (σ : Equiv.Perm V) :
    E57Matrix V * permMatrix σ = permMatrix σ * E57Matrix V := by
  simp [E57Matrix, Matrix.smul_mul, Matrix.mul_smul,
    allOnesMatrix_mul_permMatrix_eq_permMatrix_mul_allOnesMatrix σ]

/-- `E_{-8}` は graph automorphism と交換する. -/
theorem EMinus8Matrix_mul_permMatrix_eq_permMatrix_mul_EMinus8Matrix
    (σ : Equiv.Perm V) (haut : ∀ v w, Γ.Adj v w ↔ Γ.Adj (σ v) (σ w)) :
    EMinus8Matrix Γ * permMatrix σ = permMatrix σ * EMinus8Matrix Γ := by
  simp only [EMinus8Matrix, Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul,
    Matrix.mul_one]
  rw [E7Matrix_mul_permMatrix_eq_permMatrix_mul_E7Matrix Γ σ haut]
  rw [E57Matrix_mul_permMatrix_eq_permMatrix_mul_E57Matrix (V := V) σ]

end HigmanTrace

end Moore57
