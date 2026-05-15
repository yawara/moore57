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

/-- **Phase 3 主結論** (sorry): `n ∈ {5, 20, 35, 50}`. -/
theorem traceNumber_mem_candidates :
    h.traceNumber = 5 ∨ h.traceNumber = 20 ∨
      h.traceNumber = 35 ∨ h.traceNumber = 50 := by
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
