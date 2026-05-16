import Moore57.Order22OnMoore57.Phase4RepTheory
import Moore57.Foundations.LinearAlgebra.JordanMonotonicity
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Phase 4 F_11 framework: V → ZMod 11 setup

Phase 4 の K-S を avoid するため, V_F_11 := V → ZMod 11 上で σ-作用と A-作用を
定義し, Jordan 単調性 (`Moore57.LinearAlgebra.finrank_ker_pow_concave`) を
適用するための基盤を整備.

## 主な定義 (本ファイル)

* `permMatrix_F11 σ`: σ の F_11 permutation matrix.
* `permMatrix_F11_pow_eleven`: σ^11 = 1 から `permMatrix_F11^11 = 1`.
* `adjMatrix_F11`: Γ.adjMatrix (ZMod 11).
* `adjMatrix_F11_commute_permMatrix_F11`: A と σ が F_11 上可換.

## 戦略

`σ_F11_lin : V_F_11 → V_F_11` (= `(permMatrix_F11 σ).toLin'`)
`T_F11 := σ_F11_lin - 1`: nilpotent of degree 11 over F_11.

orbit decomp により `finrank ker(T_F11^j) = 5 + 295 j` for `1 ≤ j ≤ 11`.
これを `Phase4F11OrbitKernel.lean` で示す (次の段階).

Eigenspace decomp により `V_F11 = V_2_F11 ⊕ V_7_F11 ⊕ V_3_F11`,
各 V_λ_F11 は σ-不変, `Jordan_monotonicity` 適用可.

最終的に linearity forcing + 数値計算で `a_7 = 159` を導出.
-/

namespace Moore57

namespace Order22ActsOnMoore57

open LinearMap Submodule Module

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-! ## F_11 permutation matrix -/

/-- σ の F_11 上 permutation matrix (Moore57 convention: σ⁻¹ side). -/
noncomputable def permMatrixF11 (σ : Equiv.Perm V) : Matrix V V (ZMod 11) :=
  σ.symm.toPEquiv.toMatrix

/-- `permMatrixF11 (1 : Equiv.Perm V) = 1`. -/
theorem permMatrixF11_one :
    (permMatrixF11 (1 : Equiv.Perm V)) = 1 := by
  change Equiv.Perm.permMatrix (ZMod 11) ((1 : Equiv.Perm V)⁻¹) = 1
  simp

/-- `permMatrixF11 (σ * τ) = permMatrixF11 σ * permMatrixF11 τ`. -/
theorem permMatrixF11_mul (σ τ : Equiv.Perm V) :
    (permMatrixF11 (σ * τ)) = permMatrixF11 σ * permMatrixF11 τ := by
  change Equiv.Perm.permMatrix (ZMod 11) ((σ * τ)⁻¹) =
    Equiv.Perm.permMatrix (ZMod 11) σ⁻¹ * Equiv.Perm.permMatrix (ZMod 11) τ⁻¹
  rw [mul_inv_rev, Matrix.permMatrix_mul]

/-- `permMatrixF11 σ^n = permMatrixF11 (σ^n)`. -/
theorem permMatrixF11_pow (σ : Equiv.Perm V) (n : ℕ) :
    (permMatrixF11 σ) ^ n = permMatrixF11 (σ ^ n) := by
  induction n with
  | zero => simp [permMatrixF11_one]
  | succ k ih => rw [pow_succ, ih, pow_succ, permMatrixF11_mul]

variable (h : Order22ActsOnMoore57 V Γ)

/-- σ^11 = 1 ⟹ `permMatrixF11 h.σ ^ 11 = 1`. -/
theorem permMatrixF11_σ_pow_eleven :
    (permMatrixF11 h.σ) ^ 11 = 1 := by
  rw [permMatrixF11_pow, h.σ_pow_eleven, permMatrixF11_one]

/-- toLin' 版: `((permMatrixF11 h.σ).toLin')^11 = 1`. -/
theorem permMatrixF11_σ_toLin'_pow_eleven :
    ((permMatrixF11 h.σ).toLin' : (V → ZMod 11) →ₗ[ZMod 11] (V → ZMod 11))^11 = 1 := by
  rw [← Matrix.toLin'_pow, permMatrixF11_σ_pow_eleven, Matrix.toLin'_one]
  rfl

/-! ## F_11 adjacency matrix -/

/-- Γ の adjacency matrix を F_11 係数で. -/
noncomputable def adjMatrixF11 (Γ : SimpleGraph V) [DecidableRel Γ.Adj] :
    Matrix V V (ZMod 11) :=
  Γ.adjMatrix (ZMod 11)

end Order22ActsOnMoore57

end Moore57
