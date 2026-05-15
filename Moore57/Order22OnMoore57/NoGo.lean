import Moore57.Order22OnMoore57.Action

/-!
# 位数 22 の自己同型群は Moore57 に作用しない (conditional)

自然言語証明 `no_aut_order_22_moore57.md` の主結論.

外部入力 (Fix(σ) ≅ C_5, Fix(τ) ≅ K_{1,55}) を `Order22ActsOnMoore57` 構造体の
フィールドとして仮定した下での conditional theorem.

証明本体は未完成 (自然言語証明 §2-§6 の形式化が必要):
* §2: trace number `n` の定義と一定性.
* §3: 複素 spectral 制限で `n ∈ {5, 20, 35, 50}`.
* §4: modular F_11 trace で `n ≡ 5 (mod 11)`, 合わせて `n = 5`.
* §5: involution の偶パリティ強制 (cyclic case + dihedral case の二分).
* §6: 5 が奇で矛盾.
-/

namespace Moore57

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- **主定理 (conditional)**: 固定部分グラフの外部入力
(Fix(σ) ≅ C_5, Fix(τ) ≅ K_{1,55}) を仮定すれば,
位数 22 の自己同型群は Moore57 graph 上に作用しない. -/
theorem no_Order22_acts_on_Moore57 :
    ¬ Nonempty (Order22ActsOnMoore57 V Γ) := by
  sorry

end Moore57
