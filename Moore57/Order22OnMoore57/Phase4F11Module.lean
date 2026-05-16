import Moore57.Order22OnMoore57.Action
import Moore57.Foundations.LinearAlgebra.JordanMonotonicity
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.Combinatorics.SimpleGraph.AdjMatrix

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

/-! ## permMatrixF11 適用補題 (mul を計算) -/

/-- 左から `permMatrixF11 σ` を掛けると行が `σ.symm` で置換される. -/
theorem permMatrixF11_mul_apply (σ : Equiv.Perm V) (M : Matrix V V (ZMod 11)) (v w : V) :
    (permMatrixF11 σ * M) v w = M (σ.symm v) w := by
  classical
  rw [Matrix.mul_apply]
  calc
    ∑ u : V, permMatrixF11 σ v u * M u w
        = permMatrixF11 σ v (σ.symm v) * M (σ.symm v) w := by
          refine Finset.sum_eq_single (σ.symm v) ?_ ?_
          · intro u _ hu
            have hne : σ.symm v ≠ u := hu.symm
            simp [permMatrixF11, hne]
          · intro h
            exact False.elim (h (Finset.mem_univ _))
    _ = M (σ.symm v) w := by
          simp [permMatrixF11]

/-- 右から `permMatrixF11 σ` を掛けると列が `σ` で置換される. -/
theorem mul_permMatrixF11_apply (M : Matrix V V (ZMod 11)) (σ : Equiv.Perm V) (v w : V) :
    (M * permMatrixF11 σ) v w = M v (σ w) := by
  classical
  rw [Matrix.mul_apply]
  calc
    ∑ u : V, M v u * permMatrixF11 σ u w
        = M v (σ w) * permMatrixF11 σ (σ w) w := by
          refine Finset.sum_eq_single (σ w) ?_ ?_
          · intro u _ hu
            have hne : w ≠ σ.symm u := by
              intro hyp
              apply hu
              calc
                u = σ (σ.symm u) := (σ.apply_symm_apply u).symm
                _ = σ w := by rw [← hyp]
            have hne' : σ.symm u ≠ w := fun hyp => hne hyp.symm
            simp [permMatrixF11, hne']
          · intro h
            exact False.elim (h (Finset.mem_univ _))
    _ = M v (σ w) := by
          simp [permMatrixF11]

/-! ## adjMatrixF11 と permMatrixF11 の可換性 -/

/-- F_11 版: graph automorphism σ は adjacency matrix と (F_11 上) 可換. -/
theorem adjMatrixF11_mul_permMatrixF11_eq_permMatrixF11_mul_adjMatrixF11
    (Γ : SimpleGraph V) [DecidableRel Γ.Adj] (σ : Equiv.Perm V)
    (haut : ∀ v w, Γ.Adj v w ↔ Γ.Adj (σ v) (σ w)) :
    adjMatrixF11 Γ * permMatrixF11 σ = permMatrixF11 σ * adjMatrixF11 Γ := by
  classical
  ext v w
  rw [mul_permMatrixF11_apply, permMatrixF11_mul_apply]
  show (Γ.adjMatrix (ZMod 11)) v (σ w) = (Γ.adjMatrix (ZMod 11)) (σ.symm v) w
  have hAdj : Γ.Adj v (σ w) ↔ Γ.Adj (σ.symm v) w := by
    simpa using (haut (σ.symm v) w).symm
  by_cases h : Γ.Adj v (σ w)
  · have h' : Γ.Adj (σ.symm v) w := hAdj.mp h
    simp [h, h']
  · have h' : ¬ Γ.Adj (σ.symm v) w := fun hyp => h (hAdj.mpr hyp)
    simp [h, h']

variable (h : Order22ActsOnMoore57 V Γ) in
/-- `h.σ_aut` を使った可換版. -/
theorem adjMatrixF11_commute_permMatrixF11_σ :
    adjMatrixF11 Γ * permMatrixF11 h.σ = permMatrixF11 h.σ * adjMatrixF11 Γ :=
  adjMatrixF11_mul_permMatrixF11_eq_permMatrixF11_mul_adjMatrixF11 Γ h.σ h.σ_aut

end Order22ActsOnMoore57

end Moore57
