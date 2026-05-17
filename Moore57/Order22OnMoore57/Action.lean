import Moore57.Moore57Graph.Moore57Definition
import Moore57.Moore57Graph.Aut.FixedSubgraphData
import Moore57.Moore57Graph.Aut.InvolutionFixIsK155
import Moore57.Foundations.GroupAction.FixedPoints
import Mathlib.GroupTheory.Perm.Cycle.Type

/-!
# 位数 22 の自己同型群が Moore57 に作用するデータ (Tier 3)

自然言語証明 `no_aut_order_22_moore57.md` を符号化する出発点.

`Order22ActsOnMoore57` 構造体は次の状況を保持する:

* `σ ∈ Aut(Γ)` は位数 11 (`σ^11 = 1`, `σ ≠ 1`),
* `τ ∈ Aut(Γ)` は involution (`τ^2 = 1`, `τ ≠ 1`),
* `⟨σ, τ⟩` は位数 22: cyclic か dihedral のいずれか
  (Sylow 解析より, 位数 22 の群では Sylow 11-部分群 `⟨σ⟩` が正規で,
  involution `τ` は σ を σ または σ⁻¹ に共役で送る).

加えて, 自然言語証明が外部入力として置く固定部分グラフ事実を
データフィールドとして保持する:

* `σ_fix : C5FixedData Γ σ` — Fix(σ) ≅ C_5.

τ 側 (Fix(τ) ≅ K_{1,55}) は `aut_involution_nonempty_K155FixedData`
([Moore57Graph/Aut/InvolutionFixIsK155.lean]) から **derive** され,
構造体フィールドではなく `Order22ActsOnMoore57.τ_fix` (noncomputable def)
として提供される (Cameron Theorem 3.13 を経由).

これらの入力が満たされる前提で, `Order22OnMoore57.NoGo` で
非存在 `¬ Nonempty (Order22ActsOnMoore57 V Γ)` を主張する (conditional theorem).
σ_fix 側の入力を自前で構成する Tier-2 補題は別途整備する (現状は未形式化).
-/

namespace Moore57

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- 位数 22 の自己同型群 (cyclic C_22 か dihedral D_11) が Moore57 上に
作用するデータ.

外部入力 (Fix(σ) ≅ C_5) を構造体のフィールドとして保持しており,
conditional theorem の前提を符号化する.

Fix(τ) ≅ K_{1,55} については, involution + Moore57 + ≠1 から
`aut_involution_nonempty_K155FixedData` (sorry-free) で自動的に
derive されるため, structure フィールドからは外している
(後段の `τ_fix` def を参照).
-/
structure Order22ActsOnMoore57
    (V : Type*) [Fintype V] [DecidableEq V]
    (Γ : SimpleGraph V) [DecidableRel Γ.Adj] where
  /-- Γ は Moore graph of degree 57. -/
  isMoore : IsMoore57 Γ
  /-- 位数 11 の自己同型. -/
  σ : Equiv.Perm V
  /-- σ は辺を保つ. -/
  σ_aut : ∀ v w : V, Γ.Adj v w ↔ Γ.Adj (σ v) (σ w)
  /-- σ^11 = 1. -/
  σ_pow_eleven : σ ^ 11 = 1
  /-- σ ≠ 1 (合わせて σ の位数は厳密に 11). -/
  σ_ne_one : σ ≠ 1
  /-- Involution. -/
  τ : Equiv.Perm V
  /-- τ は辺を保つ. -/
  τ_aut : ∀ v w : V, Γ.Adj v w ↔ Γ.Adj (τ v) (τ w)
  /-- τ^2 = 1. -/
  τ_pow_two : τ ^ 2 = 1
  /-- τ ≠ 1 (合わせて τ の位数は厳密に 2). -/
  τ_ne_one : τ ≠ 1
  /-- ⟨σ, τ⟩ が位数 22 になる関係: cyclic (στ = τσ) または dihedral (τστ = σ⁻¹).
  Sylow 解析より, 位数 22 の群ではこの二択しかない. -/
  στ_relation : σ * τ = τ * σ ∨ τ * σ * τ = σ⁻¹
  /-- 外部入力 1: Fix(σ) は 5-cycle. -/
  σ_fix : C5FixedData Γ σ
  /-- 外部入力 2 (Phase 5.2 geometric content):
  dihedral case (`τστ = σ⁻¹`) では `Fix(τ) ∩ S = {x : τx = x ∧ x ~ σx}` の濃度が偶数.

  自然言語証明 §5.2 で示されている: F_{x_0} = {p, q} ⊔ L (|L| = 54) という
  K_{1,55} 中心の隣接構造と, slope d の matching `π_d` の `ρ_d = θ · π_d`
  不動点が常に L に 2 個あることから, この濃度は丁度 2 (偶数).

  cyclic case (`στ = τσ`) では `cyclic_no_τ_fixed_adj_σ` により濃度は 0 (偶数).
  従って常に偶数性を仮定する形でフィールド化する.

  本フィールドは将来的に F_x ファイバー構造 (`branchFiberMatchingEquiv` 等)
  からの構成的証明で置き換える予定. -/
  fix_τ_adj_σ_card_even : 2 ∣ (Finset.univ.filter
    (fun x : V => τ x = x ∧ Γ.Adj x (σ x))).card

namespace Order22ActsOnMoore57

variable (h : Order22ActsOnMoore57 V Γ)

/-- σ の任意冪は辺を保つ. -/
theorem σ_pow_aut (n : ℕ) :
    ∀ v w : V, Γ.Adj v w ↔ Γ.Adj ((h.σ ^ n) v) ((h.σ ^ n) w) := by
  induction n with
  | zero => intros; simp
  | succ n ih =>
      intro v w
      rw [pow_succ]
      simp only [Equiv.Perm.mul_apply]
      rw [h.σ_aut v w]
      exact ih (h.σ v) (h.σ w)

/-- τ involutive. -/
theorem τ_involutive : Function.Involutive (h.τ : V → V) := by
  intro v
  have hsq : h.τ ^ 2 = 1 := h.τ_pow_two
  have : (h.τ * h.τ) v = (1 : Equiv.Perm V) v := by
    rw [show h.τ * h.τ = h.τ ^ 2 from (pow_two _).symm, hsq]
  simpa using this

/-- τ-固定部分グラフが K_{1,55}: `aut_involution_nonempty_K155FixedData`
(Cameron Theorem 3.13 / Higman, sorry-free) から自動的に derive される.

旧版では構造体の外部入力フィールドとして保持していたが,
involution + Moore57 + ≠1 から構成可能なので, derived def に格上げ. -/
noncomputable def τ_fix : K155FixedData Γ h.τ :=
  (Moore57.aut_involution_nonempty_K155FixedData
    h.isMoore h.τ h.τ_aut h.τ_involutive h.τ_ne_one).some

end Order22ActsOnMoore57

end Moore57
