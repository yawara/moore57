import Moore57.Order22OnMoore57.BasicStructure
import Moore57.Order22OnMoore57.TraceNumber

/-!
# 自然言語証明 §2: trace 数の組合せ的定義と一定性

`Tk h k` を `#{x : Γ.Adj x (σ^k x)}` で定義する.

主結果:
* `traceNumber_eq_Tk_one_div_eleven`: 定義に従う `traceNumber h = T_1 / 11`.
* `eleven_dvd_Tk` (sorry): `k ≠ 0 (mod 11)` のとき `11 ∣ T_k`
  (orbit 寄与は 0 か 11).
* `Tk_constant` (sorry): `T_k = T_1` for k = 1..10
  (有理 C_11 表現の指標値が非自明元上で一定).
* `Tk_eq_eleven_mul_traceNumber`: 上記 2 つから `T_k = 11 * n`
  (Phase 3-4 が使う形).
-/

namespace Moore57

namespace Order22ActsOnMoore57

open SimpleGraph Finset

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

variable (h : Order22ActsOnMoore57 V Γ)

/-- `T_k` の組合せ的定義: `x ~ σ^k x` を満たす `x` の個数.

自然言語証明では `T_k = tr(A σ^k)` (行列 trace) として導入されるが,
組合せ的には隣接対の数になる. trace としての側面は Phase 3 (複素 spectral)
で使う. -/
noncomputable def Tk (k : ℕ) : ℕ :=
  (Finset.univ.filter (fun x : V => Γ.Adj x ((h.σ ^ k) x))).card

/-- `traceNumber h = T_1 / 11` (定義の薄い書き換え). -/
theorem traceNumber_eq_Tk_one_div_eleven : h.traceNumber = h.Tk 1 / 11 := by
  show (Finset.univ.filter (fun x : V => Γ.Adj x (h.σ x))).card / 11
    = (Finset.univ.filter (fun x : V => Γ.Adj x ((h.σ ^ 1) x))).card / 11
  simp [pow_one]

/-- **(Phase 2 残務)** `T_k` の 11 整除性.

各長さ 11 の σ-軌道は内部 slope-k 辺を持つかどうかで丁度 11 か 0 を寄与する.
σ の不動点では `σ^k x = x` だが Γ は loopless なので寄与しない.
よって `T_k` は長さ 11 軌道の寄与のみで, 11 の倍数. -/
theorem eleven_dvd_Tk {k : ℕ} (hk : k % 11 ≠ 0) : 11 ∣ h.Tk k := by
  sorry

/-- **(Phase 2 残務)** `T_k = T_1` for k = 1..10.

自然言語証明 §2 の rationality 引数: A の各有理固有空間 (E_57, E_7, E_{-8})
は σ-不変な Q[C_11]-加群. C_11 の有理既約表現は trivial 1 と 10 次元 Φ のみ,
Φ の character 値は非自明元上で常に -1. よって `tr(A σ^k)` は k = 1..10 で一定. -/
theorem Tk_constant {k : ℕ} (hk1 : 1 ≤ k) (hk2 : k ≤ 10) :
    h.Tk k = h.Tk 1 := by
  sorry

/-- 結論 (Phase 3-4 で利用): `T_k = 11 n` for k = 1..10.

`Tk_constant` と `traceNumber` の定義から従う. -/
theorem Tk_eq_eleven_mul_traceNumber {k : ℕ} (hk1 : 1 ≤ k) (hk2 : k ≤ 10) :
    h.Tk k = 11 * h.traceNumber := by
  rw [h.Tk_constant hk1 hk2, h.traceNumber_eq_Tk_one_div_eleven]
  have hdvd : 11 ∣ h.Tk 1 := h.eleven_dvd_Tk (by decide)
  omega

end Order22ActsOnMoore57

end Moore57
