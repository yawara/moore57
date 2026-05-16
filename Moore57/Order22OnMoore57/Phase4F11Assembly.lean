import Moore57.Order22OnMoore57.Phase4F11OrbitKernel
import Moore57.Order22OnMoore57.Phase3FourCycleBound
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

## 構造

* `a7_le_160_via_F11_spectral` (sorry, hard F_11 部分): ∃ a, 3a = 2n + 467 ∧ a ≤ 160.
  - V_F_11 = V_2 ⊕ V_7 ⊕ V_3 eigenspace 分解 + 各 V_λ 内 Jordan + kernel monotonicity.
* `a7_eq_159_from_F11_full` (sorry-free given `a7_le_160_via_F11_spectral`):
  - Phase 3 candidates `a ∈ {159, 169, 179, 189}` + 上界 `a ≤ 160` から `a = 159`.
-/

namespace Moore57

namespace Order22ActsOnMoore57

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- **Step 4 上界 (focused sorry, F_11 spectral)**: `a_7 ≤ 160` via F_11 eigenspace analysis. -/
theorem a7_le_160_via_F11_spectral (h : Order22ActsOnMoore57 V Γ) :
    ∃ a : ℕ, (3 * a : ℤ) = 2 * (h.traceNumber : ℤ) + 467 ∧ a ≤ 160 := by
  -- 戦略 (詳細実装 ~400-500 行):
  -- 1. F_11 char poly of A factorizes as (X - 2)(X - 7)(X - 3) (since 57 ≡ 2, -8 ≡ 3 mod 11).
  -- 2. Lagrange projection E_λ in Matrix V V (ZMod 11):
  --    E_2 = 9 (A - 7I)(A - 3I), E_7 = 5 (A - 2I)(A - 3I), E_3 = 8 (A - 2I)(A - 7I).
  -- 3. E_λ idempotent + orthogonal + sum = I.
  -- 4. V_λ := image(E_λ.toLin') の各 σ-invariance (∵ A·σ = σ·A から E_λ · σ = σ · E_λ).
  -- 5. T_λ = (σ|V_λ) - I.toLin', T_λ^11 = 0 on V_λ.
  -- 6. Jordan monotonicity + 保存則 + V_2 trivial で:
  --    μ_j(V_7) + μ_j(V_3) = 295 (j ∈ [2, 11]) ∧ 両者非増加 ⟹ 両者定数 k_7, k_3.
  -- 7. dim V_7 = a^{F11}_7 + 10 k_7 = 1729.
  --    dim V_3 = a^{F11}_3 + 10 k_3 = 1520.
  --    a^{F11}_2 + a^{F11}_7 + a^{F11}_3 = 300 (Step 3.2).
  -- 8. l_3 = a^{F11}_3 - k_3 ≥ 0 ⟹ 11 · a^{F11}_3 ≥ 1520 ⟹ a^{F11}_3 ≥ 139.
  --    a^{F11}_7 = 300 - 1 - a^{F11}_3 ≤ 300 - 1 - 139 = 160.
  -- 9. Kernel monotonicity ℚ → F_11: a_7 ≤ a^{F11}_7 ≤ 160.
  -- 10. 3 a_7 = 2 n + 467 (Phase 3 via Phase4RepTheory.exists_a7_form_3a_eq_2n_plus_467).
  sorry

/-- **Phase 3 → Phase 4 bridge**: `∃ a, 3a = 2n + 467` (Phase 3 dim relation). -/
private theorem exists_a7_form_3a_eq_2n_plus_467 (h : Order22ActsOnMoore57 V Γ) :
    ∃ a c : ℕ, a + 10 * c = 1729 ∧ (3 * a : ℤ) = 2 * (h.traceNumber : ℤ) + 467 := by
  obtain ⟨a, c, h_eq, hdim⟩ := h.traceNumber_eq_25_plus_15_mul_dim_form
  refine ⟨a, c, hdim, ?_⟩
  have h_dim_int : (a : ℤ) + 10 * c = 1729 := by exact_mod_cast hdim
  linarith

/-- **Phase 3 candidate enumeration**: `a ∈ {159, 169, 179, 189}`. -/
private theorem exists_a7_in_phase3_candidates (h : Order22ActsOnMoore57 V Γ) :
    ∃ a : ℕ, (3 * a : ℤ) = 2 * (h.traceNumber : ℤ) + 467 ∧
      (a = 159 ∨ a = 169 ∨ a = 179 ∨ a = 189) := by
  obtain ⟨a, _, _, ha_eq⟩ := h.exists_a7_form_3a_eq_2n_plus_467
  refine ⟨a, ha_eq, ?_⟩
  rcases h.traceNumber_mem_candidates with h5 | h20 | h35 | h50
  · left; rw [h5] at ha_eq; omega
  · right; left; rw [h20] at ha_eq; omega
  · right; right; left; rw [h35] at ha_eq; omega
  · right; right; right; rw [h50] at ha_eq; omega

/-- **Step 4 主結果**: `a_7 = 159`. Phase 3 候補 + F_11 spectral 上界の合成. -/
theorem a7_eq_159_from_F11_full (h : Order22ActsOnMoore57 V Γ) :
    ∃ a : ℕ, (3 * a : ℤ) = 2 * (h.traceNumber : ℤ) + 467 ∧ a = 159 := by
  obtain ⟨a, ha_eq, ha_in⟩ := h.exists_a7_in_phase3_candidates
  obtain ⟨a', ha_eq', ha_le⟩ := h.a7_le_160_via_F11_spectral
  -- a = a' (uniqueness from 3a = 2n + 467; both integer equations agree).
  have h_a_eq : a = a' := by
    have h_3_eq : (3 * a : ℤ) = (3 * a' : ℤ) := ha_eq.trans ha_eq'.symm
    have : (a : ℤ) = (a' : ℤ) := by linarith
    exact_mod_cast this
  rw [h_a_eq] at ha_in
  -- a' ∈ {159, 169, 179, 189} ∧ a' ≤ 160 ⟹ a' = 159.
  have h_a_159 : a' = 159 := by
    rcases ha_in with h159 | h169 | h179 | h189
    · exact h159
    · rw [h169] at ha_le; omega
    · rw [h179] at ha_le; omega
    · rw [h189] at ha_le; omega
  exact ⟨a', ha_eq', h_a_159⟩

end Order22ActsOnMoore57

end Moore57
