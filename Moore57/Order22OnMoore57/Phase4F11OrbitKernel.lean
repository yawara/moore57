import Moore57.Order22OnMoore57.Phase4F11Module
import Moore57.Foundations.LinearAlgebra.JordanMonotonicity
import Mathlib.LinearAlgebra.Matrix.CharP

/-!
# Phase 4 Step 3: dim ker((σ-I)^j on V_F_11) = 5 + 295 j

orbital decomposition を経由せず, 以下 3 つの数値計算で結論:

1. `(σ - I)^{11} = 0` (Frobenius binomial over F_11).
2. `dim ker(σ - I) on V_F_11 = 300` (= #σ-orbits).
3. `dim range((σ - I)^{10}) on V_F_11 = 295` (= #free orbits).

組み合わせ + Jordan 単調性 (`finrank_ker_pow_concave`) で:
`dim ker((σ-I)^j on V_F_11) = 5 + 295 j` for `1 ≤ j ≤ 11`.

## Step 3 構成

* `permMatrixF11_sub_one_pow_eleven_eq_zero`: (σ - I)^{11} = 0 over F_11 (本ファイル).
* `finrank_ker_permMatrixF11_sub_one`: dim ker(σ - I) = #orbits = 300 (次段階).
* `finrank_range_permMatrixF11_sub_one_pow_ten`: dim range = 295 (次段階).
* `finrank_ker_T_F11_pow`: 主 dim 公式 (組み合わせ).
-/

namespace Moore57

namespace Order22ActsOnMoore57

open LinearMap Submodule Module

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-! ## Step 3.1: Frobenius binomial で `(σ - I)^{11} = 0` -/

/-- F_11 上の matrix ring に CharP 11. -/
instance : Fact (Nat.Prime 11) := ⟨by decide⟩

/-- `Order22ActsOnMoore57` から `Nonempty V` を導出. -/
private theorem nonempty_V_of_action (h : Order22ActsOnMoore57 V Γ) : Nonempty V :=
  ⟨h.σ_fix.v 0⟩

/-- **Frobenius binomial 帰結**: `(permMatrixF11 σ - 1)^{11} = 0` over F_11.

証明: char 11 の commute element に対する Frobenius:
`(σ - 1)^{11} = σ^{11} - 1^{11} = σ^{11} - 1 = 1 - 1 = 0` (∵ σ^{11} = 1). -/
theorem permMatrixF11_sub_one_pow_eleven_eq_zero (h : Order22ActsOnMoore57 V Γ) :
    ((permMatrixF11 h.σ) - 1) ^ 11 = (0 : Matrix V V (ZMod 11)) := by
  haveI : Nonempty V := h.nonempty_V_of_action
  haveI : CharP (Matrix V V (ZMod 11)) 11 := Matrix.charP 11
  have h_comm : Commute (permMatrixF11 h.σ) (1 : Matrix V V (ZMod 11)) :=
    Commute.one_right _
  have h_eq : ((permMatrixF11 h.σ) - 1)^11 =
      (permMatrixF11 h.σ)^11 - (1 : Matrix V V (ZMod 11))^11 :=
    sub_pow_char_of_commute (p := 11) (R := Matrix V V (ZMod 11)) h_comm
  rw [h_eq, h.permMatrixF11_σ_pow_eleven, one_pow]
  simp

/-- toLin' 版: `((permMatrixF11 σ - 1).toLin')^{11} = 0`. -/
theorem permMatrixF11_sub_one_toLin'_pow_eleven_eq_zero
    (h : Order22ActsOnMoore57 V Γ) :
    (((permMatrixF11 h.σ) - 1 : Matrix V V (ZMod 11)).toLin' :
        (V → ZMod 11) →ₗ[ZMod 11] (V → ZMod 11)) ^ 11 = 0 := by
  rw [← Matrix.toLin'_pow, h.permMatrixF11_sub_one_pow_eleven_eq_zero]
  ext v
  simp

end Order22ActsOnMoore57

end Moore57
