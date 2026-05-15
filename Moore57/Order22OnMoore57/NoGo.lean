import Moore57.Order22OnMoore57.TraceNumber
import Moore57.Order22OnMoore57.Parity

/-!
# 位数 22 の自己同型群は Moore57 に作用しない (conditional)

自然言語証明 `no_aut_order_22_moore57.md` §6 の最終組み立て.

`Order22ActsOnMoore57` から `traceNumber h = 5` (Phase 2-4) と
`Even (traceNumber h)` (Phase 5) を組み合わせれば即矛盾.
5 は奇なので両立しえない.
-/

namespace Moore57

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

namespace Order22ActsOnMoore57

/-- §6: trace number が同時に 5 かつ偶であることは不可能. -/
theorem false_of_raw_action (h : Order22ActsOnMoore57 V Γ) : False := by
  have h5 : h.traceNumber = 5 := h.traceNumber_eq_five
  have heven : Even h.traceNumber := h.traceNumber_even
  rw [h5] at heven
  exact (by decide : ¬ Even (5 : ℕ)) heven

end Order22ActsOnMoore57

/-- **主定理 (conditional)**: 固定部分グラフの外部入力
(Fix(σ) ≅ C_5, Fix(τ) ≅ K_{1,55}) を仮定すれば,
位数 22 の自己同型群は Moore57 graph 上に作用しない. -/
theorem no_Order22_acts_on_Moore57 :
    ¬ Nonempty (Order22ActsOnMoore57 V Γ) := by
  rintro ⟨h⟩
  exact h.false_of_raw_action

end Moore57
