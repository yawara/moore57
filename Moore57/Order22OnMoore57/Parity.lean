import Moore57.Order22OnMoore57.BasicStructure
import Moore57.Order22OnMoore57.TraceNumber

/-!
# 自然言語証明 §5: involution による parity 強制

`Order22ActsOnMoore57` の `στ_relation` が cyclic (`στ = τσ`) か
dihedral (`τστ = σ⁻¹`) かに応じて, それぞれ §5.1 / §5.2 で
`n` が偶数になることを示す.

主結論 (sorry の集合):
* `traceNumber_even_of_cyclic` (sorry, §5.1): στ = τσ の場合, n は偶数.
* `traceNumber_even_of_dihedral` (sorry, §5.2): τστ = σ⁻¹ の場合, n は偶数.
* `traceNumber_even` (上の二つから case dispatch): 常に n は偶数.

証明スケッチ:
* §5.1 cyclic case (στ = τσ):
  - u が fixed star の中心 (5 blocks B_1..B_5 が pointwise fixed).
  - τ-stable な長さ 11 軌道は σ-translation と可換な 2 次元の作用を受け,
    位数 2 の translation は trivial. よって pointwise fixed.
  - pointwise fixed な長さ 11 軌道は N(u) 内の B_i に限るが, これらは
    独立点軌道で内部辺なし.
  - よって内部辺を持つ軌道は τ-pair で 2 個ずつ. n は偶数.
* §5.2 dihedral case (τστ = σ⁻¹):
  - u が fixed star の葉 (中心は B_0 内の τ-stable 頂点 x_0).
  - 残り 4 個の block は τ-pair で対.
  - 特殊 block B_0 は内部辺寄与が 2 (slope-d ごとに丁度 2 個).
  - よって 2 + (4 個の対の寄与, これも偶数) = 偶数.
-/

namespace Moore57

namespace Order22ActsOnMoore57

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

variable (h : Order22ActsOnMoore57 V Γ)

/-- **Phase 5.1 主結論** (sorry): cyclic case で n は偶数. -/
theorem traceNumber_even_of_cyclic (hcomm : h.σ * h.τ = h.τ * h.σ) :
    Even h.traceNumber := by
  sorry

/-- **Phase 5.2 主結論** (sorry): dihedral case で n は偶数. -/
theorem traceNumber_even_of_dihedral (hdihe : h.τ * h.σ * h.τ = h.σ⁻¹) :
    Even h.traceNumber := by
  sorry

/-- **Phase 5 統合結論**: n は偶数 (cyclic / dihedral の場合分け). -/
theorem traceNumber_even : Even h.traceNumber := by
  rcases h.στ_relation with hcomm | hdihe
  · exact h.traceNumber_even_of_cyclic hcomm
  · exact h.traceNumber_even_of_dihedral hdihe

end Order22ActsOnMoore57

end Moore57
