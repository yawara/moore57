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

/-! ## Step 3.2: dim ker(σ - I) = 300 (= #σ-orbits)

`Equiv.Perm.SameCycle.setoid σ` を使い orbit Quotient と σ-fixed function を
linearly equivalence 付けて Module.finrank_pi で dim を出す.

詳細実装は ~150 行. ここでは結論のみ sorry. -/

/-- T := (permMatrixF11 σ - 1).toLin' (略記). -/
noncomputable def T_F11 (h : Order22ActsOnMoore57 V Γ) :
    (V → ZMod 11) →ₗ[ZMod 11] (V → ZMod 11) :=
  ((permMatrixF11 h.σ) - 1).toLin'

/-- **Step 3.2 (sorry)**: `dim_F_11 ker T = #σ-orbits = 300`.

Moore57 の σ (order 11, 5 fixed points, 295 free orbits) に対し orbit 数 300.
σ-不変関数空間 = (Quotient (Equiv.Perm.SameCycle.setoid σ) → F_11), dim = 300.

Mathlib: `Equiv.Perm.SameCycle.setoid`, `Quotient.lift`, `Module.finrank_pi`. -/
theorem finrank_ker_T_F11_eq_300 (h : Order22ActsOnMoore57 V Γ) :
    Module.finrank (ZMod 11) (LinearMap.ker (T_F11 h)) = 300 := by
  sorry

/-! ## Step 3.3: dim range((σ - I)^10) = 295 (= #free orbits)

(σ - I)^10 = Σ_{k=0}^{10} σ^k (F_11 binomial; C(10, k) ≡ ±1 mod 11 + 符号統合).
この operator は each free orbit の orbit-sum を返し, fixed orbit には 0.
よって range = span of free orbit-sum, dim = #free orbits = 295. -/

/-- **Step 3.3 (sorry)**: `dim_F_11 range(T^10) = 295`. -/
theorem finrank_range_T_F11_pow_ten_eq_295 (h : Order22ActsOnMoore57 V Γ) :
    Module.finrank (ZMod 11) (LinearMap.range ((T_F11 h)^10)) = 295 := by
  sorry

/-! ## Step 3.4: 主 dim formula `dim ker((σ-I)^j) = 5 + 295 j`

Steps 3.1 (T^11 = 0), 3.2 (dim ker T = 300), 3.3 (dim range T^10 = 295) と
Jordan 単調性 (`Moore57.LinearAlgebra.finrank_ker_pow_concave`) から derive.

戦略:
* f(j) := dim ker T^j (j = 0, ..., 11).
* f(0) = 0, f(1) = 300 (Step 3.2), f(11) = 3250 (Step 3.1 + ker_zero),
  f(10) = 3250 - 295 = 2955 (Step 3.3 + rank-nullity).
* μ_j := f(j) - f(j-1) は j 非増加 (Jordan).
* μ_11 = 295. 非増加性 ⟹ μ_j ≥ 295 for j ∈ [2, 11].
* Σ_{j=2}^{11} μ_j = 2950 = 10·295. 各 ≥ 295 ⟹ all = 295.
* ⟹ f(j) = f(1) + 295(j-1) = 5 + 295 j for j ∈ [1, 11].

実装 ~80 行 (interval_cases + 各 ケース concavity + omega) で derivable.
-/
theorem finrank_ker_T_F11_pow (h : Order22ActsOnMoore57 V Γ)
    {j : ℕ} (hj : 1 ≤ j) (hj_le : j ≤ 11) :
    Module.finrank (ZMod 11) (LinearMap.ker ((T_F11 h)^j)) = 5 + 295 * j := by
  sorry

end Order22ActsOnMoore57

end Moore57
