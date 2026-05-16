import Moore57.Order22OnMoore57.TraceConstancy
import Moore57.Order22OnMoore57.ModularF11

/-!
# 自然言語証明 §3: 複素 spectral 制限 → `n ∈ {5, 20, 35, 50}`
# Phase 4 との合成: `n = 5`

主結論 (sorry の集合):
* `traceNumber_mem_candidates` (sorry, §3): `n ∈ {5, 20, 35, 50}`.
* `traceNumber_eq_five`: Phase 3 + Phase 4 の合成. 候補集合中 mod 11 で 5 と
  合致するのは 5 のみ.

証明スケッチ §3 (自然言語証明):
1. C_11 の頂点置換表現の Q 上分解: V_perm ≅ 300 · 1 ⊕ 295 · Φ
   (Φ = 10 次元有理既約).
2. 57-固有空間は all-one line (1 次元).
3. E_7 ≅ a · 1 ⊕ c · Φ と書くと a + 10c = 1729.
4. tr(σ^k | E_7) = a - c (k ≠ 0).
5. E_{-8} ≅ (299 - a) · 1 ⊕ (295 - c) · Φ.
6. tr(σ^k | E_{-8}) = 4 - a + c.
7. T_k = 57 + 7(a-c) - 8(4-a+c) = 25 + 15(a-c).
8. a + 10c = 1729 ⟹ a - c ≡ 2 (mod 11).
9. T_k = 55 + 165s ⟹ n = 5 + 15s.
10. 4-cycle 禁止: 各長さ 11 軌道は高々 1 つの slope pair で内部辺.
    5 個の slope pair × n = 5n ≤ 295 (orbit 数).
11. n ≤ 59 と n = 5 + 15s より n ∈ {5, 20, 35, 50}.

下層流用候補:
* D_19 の Phase 4 (`Phases/Phase4.lean`) の Q[C_11] 表現論を 19 → 11 で具体化.
-/

namespace Moore57

namespace Order22ActsOnMoore57

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

variable (h : Order22ActsOnMoore57 V Γ)

/-- **Algebraic backbone (pure mod arithmetic)**: `11n = 25 + 15m` で `m ≡ 2 (mod 11)`
かつ `n : ℕ` のとき, `∃ s : ℕ, n = 5 + 15 * s`.

これは Phase 3 の中核 mod arithmetic. 11n = 25 + 15(a_7 - c_7) と
(a_7 - c_7) ≡ 2 (mod 11) (これらは rep theory output) を仮定すれば直ちに従う. -/
theorem traceNumber.eq_five_plus_fifteen_mul_of_modular
    {n : ℕ} {m : ℤ} (h_eq : (11 * n : ℤ) = 25 + 15 * m) (h_mod : m % 11 = 2) :
    ∃ s : ℕ, n = 5 + 15 * s := by
  -- m = 11k + 2 for some k : ℤ
  have hk_exists : ∃ k : ℤ, m = 11 * k + 2 := by
    refine ⟨m / 11, ?_⟩
    have := Int.emod_add_ediv m 11
    omega
  obtain ⟨k, hk⟩ := hk_exists
  -- 11n = 25 + 15(11k + 2) = 55 + 165k = 11(5 + 15k)
  rw [hk] at h_eq
  have h_n_int : (n : ℤ) = 5 + 15 * k := by linarith
  -- n ≥ 0 ⟹ k ≥ 0
  have hk_nn : (0 : ℤ) ≤ k := by
    have hn_nn : (0 : ℤ) ≤ (n : ℤ) := Int.natCast_nonneg n
    by_contra h_neg
    push_neg at h_neg
    have hk_le : k ≤ -1 := by linarith
    have : (n : ℤ) ≤ 5 + 15 * (-1) := by
      rw [h_n_int]; linarith
    linarith
  obtain ⟨s, rfl⟩ := Int.eq_ofNat_of_zero_le hk_nn
  refine ⟨s, ?_⟩
  have : (n : ℤ) = ((5 + 15 * s : ℕ) : ℤ) := by
    rw [h_n_int]; push_cast; ring
  exact_mod_cast this

/-- **Phase 3 中間補題**: `traceNumber = 5 + 15s ∧ traceNumber ≤ 59 → traceNumber ∈ {5,20,35,50}`.

純算術. `s ≤ 3` から enumeration. -/
theorem traceNumber.mem_candidates_of_form
    {n : ℕ} (h_form : ∃ s : ℕ, n = 5 + 15 * s) (h_bound : n ≤ 59) :
    n = 5 ∨ n = 20 ∨ n = 35 ∨ n = 50 := by
  obtain ⟨s, rfl⟩ := h_form
  -- 5 + 15s ≤ 59 → s ≤ 3
  have hs : s ≤ 3 := by omega
  interval_cases s <;> omega

/-- **Phase 3 主結論** (sorry, 縮減版).

`traceNumber_mem_candidates` の証明は以下に分解される:
- (A) 11 * traceNumber = 25 + 15 * (a_7 - c_7) ∧ (a_7 - c_7) ≡ 2 (mod 11)
  (rep theory: σ on V_7 の Q[C_11] 分解 + spectral decomp; ~300 行).
- (B) traceNumber ≤ 59 (4-cycle bound: no_4_cycle + orbit counting; ~300 行).
- 上記 + `eq_five_plus_fifteen_mul_of_modular` + `mem_candidates_of_form` で結論.

(A), (B) のいずれも本セッションでは未実装. -/
theorem traceNumber_mem_candidates :
    h.traceNumber = 5 ∨ h.traceNumber = 20 ∨
      h.traceNumber = 35 ∨ h.traceNumber = 50 := by
  -- 次セッション以降の作業: (A) と (B) を埋める.
  -- 実装後の組立は以下のとおり:
  -- have h_rep : (11 * h.traceNumber : ℤ) = 25 + 15 * (a_7 - c_7) := <Phase 3 rep theory>
  -- have h_mod : (a_7 - c_7) % 11 = 2 := <from spectral decomp>
  -- have h_form := traceNumber.eq_five_plus_fifteen_mul_of_modular h_rep h_mod
  -- have h_bound : h.traceNumber ≤ 59 := <4-cycle bound>
  -- exact traceNumber.mem_candidates_of_form h_form h_bound
  sorry

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
