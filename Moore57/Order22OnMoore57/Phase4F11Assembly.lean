import Moore57.Order22OnMoore57.Phase4F11OrbitKernel
import Moore57.Order22OnMoore57.TraceNumber

/-!
# Phase 4 Step 4: Assembly — eigenspace 分解 + a_7 = 159

Step 3.4 の dim formula + F_11 eigenspace 分解 + Jordan 単調性
+ 「2 つの非増加列の和が定数 ⟹ 両者定数」argument により a_7 = 159 を導出.

## 戦略

V_F_11 = V_2 ⊕ V_7 ⊕ V_3 (A の F_11 spectral, 固有値 2, 7, 3 distinct).
T := σ_F_11 - I を各 V_λ に restrict.

* μ_j(V_λ) := dim ker(T^j on V_λ) - dim ker(T^(j-1) on V_λ).
* Jordan 単調性: μ_j(V_λ) 非増加.
* 保存則: Σ_λ μ_j(V_λ) = μ_j(V_F11).

V_2 は dim 1, a_2 = 1 ⟹ μ_j(V_2) = 0 for j ≥ 2.

V_7 + V_3: μ_j(V_7) + μ_j(V_3) = 295 (j ∈ [2, 11]), 両者非増加 ⟹ 両者定数.

数値解:
* μ_j(V_7) = k_7 = (1729 - a_7)/10 (constant for j ∈ [2, 11]).
* μ_j(V_3) = k_3 = (1221 + a_7)/10.
* l_7 := a_7 - k_7 = (11 a_7 - 1729)/10 ≥ 0 ⟹ a_7 ≥ 158.
* l_3 := a_3 - k_3 = (1769 - 11 a_7)/10 ≥ 0 ⟹ a_7 ≤ 160.
* a_7 ≡ 9 (mod 10) (integer 条件).
* ⟹ a_7 = 159.

## 必要な sub-sorry

* Eigenspace 分解 `V_F_11 = V_2 ⊕ V_7 ⊕ V_3`.
* `a^{F_11}_λ = a_λ` (kernel monotonicity ℚ → F_11).
* dim ker((σ-I)^j on V_λ_F11) for j = 1, 11 から数値解.

これらは更なる infrastructure (F_11 spectral projection + ℚ → F_11 lattice
argument) が必要. 本 step は **structural skeleton** を提供.
-/

namespace Moore57

namespace Order22ActsOnMoore57

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- **Step 4 主結果 (sorry, F_11 eigenspace + linearity forcing 要)**: `a_7 = 159`. -/
theorem a7_eq_159_from_F11_full (h : Order22ActsOnMoore57 V Γ) :
    ∃ a : ℕ, (3 * a : ℤ) = 2 * (h.traceNumber : ℤ) + 467 ∧ a = 159 := by
  -- 戦略 (詳細実装は ~200 行):
  -- 1. V_F_11 を A の F_11 eigenvalue ごとに decompose: V_2 ⊕ V_7 ⊕ V_3.
  -- 2. Kernel monotonicity ℚ → F_11 で a^{F_11}_λ = a_λ.
  -- 3. T = σ_F_11 - I を各 V_λ に restrict.
  -- 4. Jordan 単調性 + 保存則 + V_2 trivial で:
  --    μ_j(V_7) + μ_j(V_3) = 295 (定数 in j ∈ [2, 11]) ∧ 両者非増加 ⟹ 両者定数.
  -- 5. k_7 = (1729 - a_7)/10, k_3 = (1221 + a_7)/10.
  -- 6. l_7 ≥ 0 ⟹ a_7 ≥ 158. l_3 ≥ 0 ⟹ a_7 ≤ 160.
  --    a_7 ≡ 9 (mod 10) ⟹ a_7 ∈ {159}.
  -- 7. 3a = 2n + 467 (Phase 3) と合わせて結論.
  sorry

end Order22ActsOnMoore57

end Moore57
