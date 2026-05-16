import Moore57.Order22OnMoore57.Phase3FourCycleBound

/-!
# 自然言語証明 §4: F_11 modular rep theory による `10n ≡ 6 (mod 11)`

主結論: `traceNumber_mod_eleven_eq_five`. F_11 上で `trace(A | V^σ) = 10n` と
`trace_F_11(A | V^σ) = 6 (mod 11)` を二通り計算して等値.

## 構造

`trace(A | V^σ) = 10n` (over ℤ, via orbit basis + Phase 3 (B))
* Phase 3 で sum_slopesAdj_eq_55n.
* 各長さ 11 軌道の Frobenius 自己相似性: 内部辺ありなら 2 寄与/頂点.

`trace_F_11(A | V^σ) ≡ 6 (mod 11)` (via F_11 Krull-Schmidt)
* V_perm = M_1^5 ⊕ M_11^295 (orbit decomp over F_11[C_11]).
* V_perm = V_2 ⊕ V_7 ⊕ V_3 (A の F_11 spectral, distinct eigenvalues).
* 各 V_λ = M_1^{l_λ} ⊕ M_11^{k_λ}, l_λ ≡ dim V_λ (mod 11), 0 ≤ l_λ ≤ 5.
* l_2 = 1, l_7 = 2, l_3 = 2; a^{F_11}_λ = l_λ + k_λ: 1, 159, 140.
* trace = 2·1 + 7·159 + 3·140 = 1535 ≡ 6 (mod 11).

## 実装方針

本ファイルは:
* `trace_orbit_basis_eq_ten_n`: 10n = trace orbit basis. (sorry-free を目指す.)
* `trace_spectral_eq_six_mod_eleven`: trace F_11 spectral = 6 mod 11. (heavyweight, sorry.)
* `traceNumber_mod_eleven_eq_five`: 統合.

Phase 4 の完全実装には F_11[C_11] Krull-Schmidt の自前構築 (~500 行) 要.
本ファイルは未完成段階を残し, ModularF11.lean の sorry を Phase4RepTheory.lean に
集約する.
-/

namespace Moore57

namespace Order22ActsOnMoore57

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

variable (h : Order22ActsOnMoore57 V Γ)

/-! ## 中核補題: 内部辺ありの軌道の総数 = 5n -/

/-- `Σ_x |slopesAdj h x| = #{x : |slopesAdj h x| = 1}` since slope sets ≤ 1.

Phase 3 (B) `slopesAdj_card_le_one` + sum_slopesAdj_eq_55n を結合. -/
theorem card_filter_slopesAdj_eq_one_eq_55n :
    (Finset.univ.filter
      (fun x : V => (h.slopesAdj x).card = 1)).card = 55 * h.traceNumber := by
  classical
  -- sum_slopesAdj = 55n (Phase 3 B)
  have h_sum := h.sum_slopesAdj_eq_55n
  -- Σ_x |slopesAdj x| = Σ_x (if |slopesAdj x| = 1 then 1 else 0) since ≤ 1.
  have h_le := h.slopesAdj_card_le_one
  have h_sum_eq : ∑ x : V, (h.slopesAdj x).card =
      ∑ x : V, (if (h.slopesAdj x).card = 1 then 1 else 0 : ℕ) := by
    apply Finset.sum_congr rfl
    intros x _
    have hle := h_le x
    interval_cases (h.slopesAdj x).card <;> simp
  rw [h_sum_eq] at h_sum
  rw [← h_sum]
  -- Σ ite ... = filter card
  rw [Finset.sum_ite]
  simp

/-! ## (B-Step 1) 整数等式 `3 a₇ = 2 n + 467` (sorry-free, Phase 3 から) -/

/-- **Phase 3 帰結 (整数等式)**: ∃ a c, a + 10 c = 1729 ∧ 3 a = 2 n + 467.

派生:
* `11n = 25 + 15(a - c)`, `a + 10c = 1729` (Phase 3 A) を解いて
  `c = (1729 - a)/10`, `15c = 3(1729 - a)/2`. 整理して
  `11n + 75c = 25 + 15a + 60c` ⟹ `11n + 15c = 25 + 15a` ⟹
  `11n = 25 + 15(a - c)` (元の式).
* もう一つ独立な関係: `2(11n) - 11(a + 10c) = 50 + 30(a-c) - 11a - 110c`
  `= 50 + 30a - 30c - 11a - 110c = 50 + 19a - 140c`.
  これは 22n - 11·1729 = 22n - 19019.
  `50 + 19a - 140c = 22n - 19019`. 整理: `19a - 140c = 22n - 19069`. ない方向.
* 直接: a + 10c = 1729 ⟹ 10c = 1729 - a ⟹ 30c = 3(1729 - a).
  11n = 25 + 15a - 15c. 30倍: 330n = 750 + 450a - 450c
  = 750 + 450a - 15 · 30c = 750 + 450a - 15·3·(1729-a) = 750 + 450a - 45·1729 + 45a
  = 750 - 77805 + 495a = 495a - 77055. So 495a - 330n = 77055.
  Divide by 165: 3a - 2n = 77055/165 = 467. ✓ -/
theorem exists_a7_form_3a_eq_2n_plus_467 :
    ∃ a c : ℕ, a + 10 * c = 1729 ∧ (3 * a : ℤ) = 2 * (h.traceNumber : ℤ) + 467 := by
  obtain ⟨a, c, h_eq, hdim⟩ := h.traceNumber_eq_25_plus_15_mul_dim_form
  refine ⟨a, c, hdim, ?_⟩
  -- 11n = 25 + 15(a - c), a + 10c = 1729 から 3a = 2n + 467
  have h_dim_int : (a : ℤ) + 10 * c = 1729 := by exact_mod_cast hdim
  -- 11n + 15c = 25 + 15a (from h_eq)
  -- 165a = 11·15a = 11·(11n + 15c - 25) = 121n + 165c - 275
  -- 165a - 165c = 121n - 275
  -- 165(a-c) = 121n - 275 ... but also a+10c = 1729 so c = (1729-a)/10
  -- Better: from 11n = 25 + 15a - 15c and a + 10c = 1729:
  -- multiply first by 2: 22n = 50 + 30a - 30c
  -- multiply second by 3: 3a + 30c = 5187
  -- add: 22n + 3a = 50 + 33a + 5187 - 60c ... hmm let me just use linarith
  linarith

/-- **Phase 3 帰結 (候補列挙)**: ∃ a, 3 a = 2 n + 467 ∧ a ∈ {159, 169, 179, 189}.

Phase 3 candidates n ∈ {5, 20, 35, 50} と integer relation `3a = 2n + 467` を組合せ. -/
theorem exists_a7_in_phase3_candidates :
    ∃ a : ℕ, (3 * a : ℤ) = 2 * (h.traceNumber : ℤ) + 467 ∧
      (a = 159 ∨ a = 169 ∨ a = 179 ∨ a = 189) := by
  obtain ⟨a, c, _, ha_eq⟩ := h.exists_a7_form_3a_eq_2n_plus_467
  refine ⟨a, ha_eq, ?_⟩
  -- Phase 3 candidates n ∈ {5, 20, 35, 50} から a 候補列挙
  rcases h.traceNumber_mem_candidates with h5 | h20 | h35 | h50
  · -- n = 5: 3a = 10 + 467 = 477, a = 159
    left; rw [h5] at ha_eq; omega
  · -- n = 20: 3a = 40 + 467 = 507, a = 169
    right; left; rw [h20] at ha_eq; omega
  · -- n = 35: 3a = 70 + 467 = 537, a = 179
    right; right; left; rw [h35] at ha_eq; omega
  · -- n = 50: 3a = 100 + 467 = 567, a = 189
    right; right; right; rw [h50] at ha_eq; omega

/-! ## (B-Step 2) F_11 K-S 由来の上界 (sorry: 残った Phase 4 核心) -/

/-- **(Phase 4 核心 sorry, focused form)**: `a_7 = 159`.

これが F_11 Krull-Schmidt の本質的内容. 派生として `n = 5`, `10n ≡ 6 (mod 11)` が従う.

## 証明スケッチ (F_11[C_11] Krull-Schmidt)

V_perm = (V → F_11) を F_11[X]-module と見る (X = σ 作用).
σ^{11} = 1 ⟹ V_perm は X^{11} - 1 = (X-1)^{11} torsion (over F_11, char 11).

**Step 1**: orbit decomp で V_perm = M_1^5 ⊕ M_{11}^{295} (F_11[X]-mod).
* 各固定軌道 (singleton) は M_1 = F_11[X]/(X-1).
* 各長さ 11 自由軌道は M_{11} = F_11[X]/(X^{11}-1) = F_11[X]/(X-1)^{11}.

**Step 2**: A の F_11-spectral 分解 (有理 spectral からの reduction).
A mod 11 の最小多項式は (X-2)(X-7)(X-3) (distinct roots), なので A は
F_11 上対角化可能. V_perm = V_2^{F_11} ⊕ V_7^{F_11} ⊕ V_3^{F_11},
dimension は ℚ 上と同じ (char poly が ℤ 上同じ).
* dim V_2^{F_11} = 1, dim V_7^{F_11} = 1729, dim V_3^{F_11} = 1520.

**Step 3**: Krull-Schmidt uniqueness applied.
V_perm = V_2 ⊕ V_7 ⊕ V_3 (eigenspace decomp), and V_perm = M_1^5 ⊕ M_{11}^{295}
(orbit decomp). 両者は K-S 一意性で一致. 各 V_λ は M_1, M_{11} のみで分解:
V_λ = M_1^{l_λ} ⊕ M_{11}^{k_λ}.
* dim V_λ = l_λ + 11 k_λ. l_λ + l_2 + l_3 = 5. k_λ + k_2 + k_3 = 295.
* l_λ ≡ dim V_λ (mod 11), 0 ≤ l_λ ≤ 5.

**Step 4**: 数値計算.
* l_2 ≡ 1 (mod 11), 0 ≤ l_2 ≤ 5 ⟹ l_2 = 1.
* l_7 ≡ 1729 ≡ 2 (mod 11), 0 ≤ l_7 ≤ 5 ⟹ l_7 = 2.
* l_3 ≡ 1520 ≡ 2 (mod 11), 0 ≤ l_3 ≤ 5 ⟹ l_3 = 2.
* 各 k_λ: k_2 = 0, k_7 = 157, k_3 = 138.

**Step 5**: a^{F_11}_λ = l_λ + k_λ:
* a^{F_11}_2 = 1, a^{F_11}_7 = 159, a^{F_11}_3 = 140.

**Step 6**: Kernel monotonicity + Σ-conservation で a^{F_11}_λ = a_λ:
* a^{F_11}_λ ≥ a_λ (ker((σ-I) over F_11) ⊇ ker (σ-I) over ℚ).
* Σ a^{F_11}_λ = dim V_perm^{σ, F_11} = 300 = Σ a_λ.
* 各 ≥ なので equality.

**結論**: a_7 = a^{F_11}_7 = 159. Phase 3 candidates a ∈ {159, 169, 179, 189}
の中で 159 のみ. これが Phase 3 と整合し n = 5.

## Mathlib インフラ

`Module.equiv_directSum_of_isTorsion` (in `Mathlib/Algebra/Module/PID.lean`):
PID 上 torsion module の elementary divisor 分解 (existence + uniqueness).
F_11[X] is PID, V_perm は torsion. これを使う.

実装規模: ~300-500 行 (F_11 framework, orbit decomp, V_λ submodule analysis,
K-S uniqueness invocation). -/
theorem a7_eq_159_via_F11_KrullSchmidt :
    ∃ a : ℕ, (3 * a : ℤ) = 2 * (h.traceNumber : ℤ) + 467 ∧ a = 159 := by
  sorry

/-- **Phase 4 派生**: `traceNumber = 5`. K-S 由来の `a_7 = 159` から導出. -/
theorem traceNumber_eq_five_via_F11 :
    h.traceNumber = 5 := by
  obtain ⟨a, ha_eq, ha_159⟩ := h.a7_eq_159_via_F11_KrullSchmidt
  rw [ha_159] at ha_eq
  -- 3 · 159 = 477 = 2 n + 467 ⟹ n = 5
  push_cast at ha_eq
  have : (h.traceNumber : ℤ) = 5 := by linarith
  exact_mod_cast this

/-- **Phase 4 主結論**: `10 * traceNumber ≡ 6 (mod 11)`. -/
theorem ten_traceNumber_mod_eleven_eq_six :
    10 * h.traceNumber % 11 = 6 := by
  rw [h.traceNumber_eq_five_via_F11]

/-! ## 統合 -/

/-- **Phase 4 主結論**: `h.traceNumber % 11 = 5`.

`10 * n ≡ 6 (mod 11)` と `10 ≡ -1 (mod 11)` から `n ≡ -6 ≡ 5 (mod 11)`. -/
theorem traceNumber_mod_eleven_eq_five :
    h.traceNumber % 11 = 5 := by
  have h_ten := h.ten_traceNumber_mod_eleven_eq_six
  exact Moore57.Order22ActsOnMoore57.traceNumber_mod_eleven_eq_five_of_ten_mul_modular
    h_ten

/-- **Phase 3 + Phase 4 統合**: `n = 5`.

Phase 4 で `n % 11 = 5`, Phase 3 で `n ∈ {5, 20, 35, 50}`.
5 のみが mod 11 で 5 (∵ 20 % 11 = 9, 35 % 11 = 2, 50 % 11 = 6). -/
theorem traceNumber_eq_five : h.traceNumber = 5 := by
  have h_mod : h.traceNumber % 11 = 5 := h.traceNumber_mod_eleven_eq_five
  rcases h.traceNumber_mem_candidates with h5 | h20 | h35 | h50
  · exact h5
  · exfalso; rw [h20] at h_mod; omega
  · exfalso; rw [h35] at h_mod; omega
  · exfalso; rw [h50] at h_mod; omega

end Order22ActsOnMoore57

end Moore57
