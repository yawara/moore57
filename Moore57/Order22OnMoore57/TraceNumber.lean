import Moore57.Order22OnMoore57.Action

/-!
# Trace number `n` (自然言語証明 §2)

`Order22ActsOnMoore57` から自然言語証明の `n` を定義する.

自然言語証明では `T_k = tr(A σ^k)` (k = 1..10) は σ-不変性と rationality より
すべて同じ値 `11n` を取る. ここで n は σ-orbit のうちある slope k で内部辺を
持つものの個数. 本ファイルでは k = 1 を採用して

  `n := #{x ∈ V | x ~ σ x} / 11`

と定義する. 各長さ 11 軌道は内部辺を持つ場合に丁度 11 を, 持たない場合に 0 を
寄与する.

## 結論として保持する 2 つの sorry

* `traceNumber_eq_five` — §2-§4 から導かれる `n = 5`.
* `traceNumber_even`    — §5 (involution の場合分け) から導かれる `Even n`.

両者は当面 `sorry` で型だけ供給し, Phase 1-5 で順次実装する.
-/

namespace Moore57

namespace Order22ActsOnMoore57

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- 自然言語証明の trace number `n`.

`x ~ σ x` を満たす頂点 `x` の個数を 11 で割ったもの.
σ の各長さ 11 軌道は slope 1 で内部辺を持つかどうかに応じて
11 か 0 を寄与するので, この割り算は割り切れる. -/
noncomputable def traceNumber (h : Order22ActsOnMoore57 V Γ) : ℕ :=
  (Finset.univ.filter (fun x : V => Γ.Adj x (h.σ x))).card / 11

/-- **Phase 2-4 の結論 (要証明)**: `n = 5`.

自然言語証明 §2-§4: 複素 trace 制限で `n ∈ {5, 20, 35, 50}`,
さらに F_11 モジュラ trace で `n ≡ 5 (mod 11)`, 合わせて `n = 5`. -/
theorem traceNumber_eq_five (h : Order22ActsOnMoore57 V Γ) :
    h.traceNumber = 5 := by
  sorry

-- `traceNumber_even` (Phase 5) は `Parity.lean` に分離.

end Order22ActsOnMoore57

end Moore57
