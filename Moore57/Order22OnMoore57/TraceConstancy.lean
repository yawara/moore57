import Moore57.Order22OnMoore57.BasicStructure
import Moore57.Order22OnMoore57.TraceNumber
import Mathlib.GroupTheory.Perm.Cycle.Type

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

/-- `σ^n x = x` if `σ x = x`, 任意の `n` で. -/
private theorem σ_pow_fix {x : V} (hx : h.σ x = x) (n : ℕ) :
    (h.σ ^ n) x = x := by
  induction n with
  | zero => simp
  | succ m ih =>
    rw [pow_succ', Equiv.Perm.mul_apply, ih, hx]

/-- `T_k` の 11 整除性 (orbit 論証).

`S = {x : Γ.Adj x (σ^k x)}` は σ-不変. σ を `Subtype S` に制限すると
位数 11 の置換 τ. τ の不動点は σ 不動点 ∩ S だが,
σ 不動点では `σ^k x = x` で `Γ.Adj x x = False` (loopless) ゆえ S に属さず空.
よって `S.card ≡ 0 (mod 11)`. -/
theorem eleven_dvd_Tk {k : ℕ} (hk : k % 11 ≠ 0) : 11 ∣ h.Tk k := by
  classical
  haveI : Fact (Nat.Prime 11) := ⟨by decide⟩
  -- σ-不変な述語 p
  let p : V → Prop := fun x => Γ.Adj x ((h.σ ^ k) x)
  -- σ と σ^k は可換
  have hcomm : ∀ x : V, (h.σ ^ k) (h.σ x) = h.σ ((h.σ ^ k) x) := fun x => by
    have heq : h.σ ^ k * h.σ = h.σ * h.σ ^ k := by
      rw [← pow_succ, ← pow_succ']
    have := congrArg (· x) heq
    simpa [Equiv.Perm.mul_apply] using this
  -- p の σ-不変性 (subtypePerm の要求形: p (σ x) ↔ p x)
  have hp_iff : ∀ x : V, p (h.σ x) ↔ p x := fun x => by
    show Γ.Adj (h.σ x) ((h.σ ^ k) (h.σ x)) ↔ Γ.Adj x ((h.σ ^ k) x)
    rw [hcomm x]
    exact (h.σ_aut x ((h.σ ^ k) x)).symm
  -- σ を Subtype p に制限
  let τ : Equiv.Perm (Subtype p) := h.σ.subtypePerm hp_iff
  -- τ^11 = 1
  have hτ_pow : τ ^ 11 ^ 1 = 1 := by
    ext ⟨w, _⟩
    show (h.σ ^ 11) w = w
    rw [h.σ_pow_eleven]; rfl
  -- 主補題: |Subtype p| ≡ |τ.supportᶜ| (mod 11)
  have hmod := Equiv.Perm.card_compl_support_modEq
    (α := Subtype p) (p := 11) (n := 1) (σ := τ) hτ_pow
  -- τ の不動点は無い: |τ.supportᶜ| = 0
  have hfix_empty : τ.supportᶜ.card = 0 := by
    rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
    rintro ⟨w, hwp⟩ hw
    rw [Finset.mem_compl, Equiv.Perm.mem_support] at hw
    push_neg at hw
    -- hw : τ ⟨w, hwp⟩ = ⟨w, hwp⟩ ⟹ σ w = w
    have hwfix : h.σ w = w := congrArg Subtype.val hw
    -- σ w = w → σ^k w = w
    have hkfix : (h.σ ^ k) w = w := h.σ_pow_fix hwfix k
    -- hwp : Γ.Adj w (σ^k w) = Γ.Adj w w (loopless 矛盾)
    have hwp' : Γ.Adj w ((h.σ ^ k) w) := hwp
    rw [hkfix] at hwp'
    exact SimpleGraph.irrefl Γ hwp'
  rw [hfix_empty] at hmod
  -- |Subtype p| = Tk k
  have hcard : Fintype.card (Subtype p) = h.Tk k := by
    rw [Fintype.card_subtype]
    rfl
  rw [hcard] at hmod
  exact Nat.modEq_zero_iff_dvd.mp hmod.symm

/-- **(Phase 2 残務)** `T_k = T_1` for k = 1..10.

自然言語証明 §2 の rationality 引数: A の各有理固有空間 (E_57, E_7, E_{-8})
は σ-不変な Q[C_11]-加群. C_11 の有理既約表現は trivial 1 と 10 次元 Φ のみ,
Φ の character 値は非自明元上で常に -1. よって `tr(A σ^k)` は k = 1..10 で一定. -/
theorem Tk_constant {k : ℕ} (hk1 : 1 ≤ k) (hk2 : k ≤ 10) :
    h.Tk k = h.Tk 1 := by
  sorry

/-- k = 1 の特別ケース (sorry-free, `eleven_dvd_Tk` のみに依存). -/
theorem Tk_one_eq_eleven_mul_traceNumber : h.Tk 1 = 11 * h.traceNumber := by
  rw [h.traceNumber_eq_Tk_one_div_eleven]
  have hdvd : 11 ∣ h.Tk 1 := h.eleven_dvd_Tk (by decide)
  omega

/-- 結論 (Phase 3-4 で利用): `T_k = 11 n` for k = 1..10.

`Tk_constant` と `traceNumber` の定義から従う.
k = 1 では `Tk_one_eq_eleven_mul_traceNumber` で sorry なしに導出可. -/
theorem Tk_eq_eleven_mul_traceNumber {k : ℕ} (hk1 : 1 ≤ k) (hk2 : k ≤ 10) :
    h.Tk k = 11 * h.traceNumber := by
  rw [h.Tk_constant hk1 hk2]
  exact h.Tk_one_eq_eleven_mul_traceNumber

end Order22ActsOnMoore57

end Moore57
