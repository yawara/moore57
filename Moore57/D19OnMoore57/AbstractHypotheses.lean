import Moore57.Moore57Graph.Moore57Definition
import Moore57.D19OnMoore57.Counting.AbstractCounting

/-!
# Abstract D₁₉ hypotheses and the contradiction (Tier 3)

This file extracts the abstract version of the D₁₉ non-existence statements
from the original `D19Contradiction.lean`:

* `D19ConcreteHypotheses` — concrete orbit data structure.
* `D19ConcreteHypotheses.not_nonempty` — concrete data is empty under Moore57.
* `no_D19_subgroup` — abstract `D19Hypotheses` is empty.
* `no_D19_concrete_hypotheses` — Moore57 ⊕ concrete D₁₉ data is contradictory.

Used directly by the main theorem chain.
-/

open Finset SimpleGraph

namespace Moore57

/-! ## 具体軌道データからの矛盾

`D19Hypotheses` は Section 6 の抽象計数に合わせて差集合を `Fin 18` で表している.
一方, Section 5 の 4-cycle 論証は差を `ZMod 19` の非零元として扱う方が自然である.

以下の `D19ConcreteHypotheses` は, `D_{19}` 作用から構成されるべき軌道データのうち,
Section 5 と Section 6 に必要な部分だけを `ZMod 19` 上で保持する.
この構造が与えられれば, `D_q` は `W` から定義し, `|D_q|≤2` は
`Dq_card_le_two_of_moore` から導く.
-/

/-- Section 5/6 に必要な具体的軌道データ.

各 `q : Fin 56` について `W q : ZMod 19 → V` は同じ $B$-側 19-cycle の頂点列を表す.
内部差集合 `D q` は `internalDiffSet Γ (W q)` として下で定義する.

`traceChar` と `a1_contribution` は Section 4 の入力を最終計数に接続するための
データである. `traceChar` は Higman 跡公式そのものではなく, 回転置換の固定点数,
`a1` の組合せ的意味, および表現論側の指標値だけを保持する.
ここから `Nd_lower` は下の定理 `Nd_lower` で証明するため, 具体構造のフィールド
としては仮定しない. -/
structure D19ConcreteHypotheses
    {V : Type*} [Fintype V] [DecidableEq V]
    (Γ : SimpleGraph V) [DecidableRel Γ.Adj] where
  /-- 非自明回転に対する $a_1(r^d)$. -/
  a1 : ZMod 19 → ℕ
  /-- 各 `d : ZMod 19` に対応する回転置換. -/
  rotation : ZMod 19 → Equiv.Perm V
  W : Fin 56 → ZMod 19 → V
  W_injective : ∀ q : Fin 56, Function.Injective (W q)
  /-- Section 4 の表現論側データ. Higman 跡公式は Lean 内で適用する. -/
  traceChar : TraceCharacterData Γ rotation a1
  /-- 系 3.6 と $B,C$ 側の軌道寄与:
  $a_1(r^d)=38+38N_d$. -/
  a1_contribution :
    ∀ d : ZMod 19, d ≠ 0 →
      a1 d =
        38 + 38 *
          ((Finset.univ : Finset (Fin 56)).filter
            (fun q => d ∈ internalDiffSet Γ (W q))).card

namespace D19ConcreteHypotheses

variable {V : Type*} [Fintype V] [DecidableEq V]
    {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- 具体軌道データから定義される内部差集合. -/
noncomputable def D (h : D19ConcreteHypotheses Γ) (q : Fin 56) : Finset (ZMod 19) :=
  internalDiffSet Γ (h.W q)

/-- 定義された内部差集合には零差は入らない. -/
theorem D_zero (h : D19ConcreteHypotheses Γ) (q : Fin 56) :
    (0 : ZMod 19) ∉ h.D q :=
  internalDiffSet_zero (h.W q)

/-- 定義された内部差集合の隣接性. -/
theorem D_adj (h : D19ConcreteHypotheses Γ) (q : Fin 56) (d : ZMod 19)
    (hd : d ∈ h.D q) :
    ∀ i : ZMod 19, Γ.Adj (h.W q i) (h.W q (i + d)) :=
  internalDiffSet_adj (h.W q) hd

/-- 定義された内部差集合は符号反転で閉じている. -/
theorem D_symm (h : D19ConcreteHypotheses Γ) (q : Fin 56) (d : ZMod 19)
    (hd : d ∈ h.D q) :
    -d ∈ h.D q :=
  internalDiffSet_symm (h.W q) hd

/-- 具体軌道データでは, Section 5 の上界 `|D_q|≤2` は 4-cycle 禁止から証明できる. -/
theorem Dq_le_two (hΓ : IsMoore57 Γ) (h : D19ConcreteHypotheses Γ) :
    ∀ q : Fin 56, (h.D q).card ≤ 2 := by
  intro q
  exact Dq_card_le_two_of_moore hΓ (h.W q) (h.W_injective q) (h.D q)
    (h.D_zero q) (h.D_adj q) (h.D_symm q)

/-- 具体軌道データの Section 4 入力から, 算術補題用の
`TraceRepresentationData` を導く. -/
def traceRep (h : D19ConcreteHypotheses Γ) (hΓ : IsMoore57 Γ) :
    TraceRepresentationData h.a1 :=
  h.traceChar.toTraceRepresentationData hΓ

/-- 具体軌道データでは, Section 4 の下界 `N_d≥8` は
跡公式・表現論の算術補題から証明できる. -/
theorem Nd_lower (hΓ : IsMoore57 Γ) (h : D19ConcreteHypotheses Γ) :
    ∀ d : ZMod 19, d ≠ 0 →
      8 ≤ ((Finset.univ : Finset (Fin 56)).filter (fun q => d ∈ h.D q)).card :=
  Nd_lower_of_trace_representation h.D h.a1 (h.traceRep hΓ) (by
    intro d hd
    simpa [D] using h.a1_contribution d hd)

/-- 具体軌道データは存在しない. Section 5 の上界と Section 6 の計数を組み合わせる. -/
theorem not_nonempty (hΓ : IsMoore57 Γ) : ¬ Nonempty (D19ConcreteHypotheses Γ) := by
  rintro ⟨h⟩
  exact counting_contradiction_zmod h.D (fun q => h.D_zero q) (h.Dq_le_two hΓ) (h.Nd_lower hΓ)

end D19ConcreteHypotheses

/-! ## 主定理: 計数データの非存在 -/

/-- 主定理 (定理 6.1) の「抽象版」.

`D19Hypotheses` 型のデータが存在すれば, 計数論証で矛盾するため, そのような
データは存在しない.

これは自然言語の証明全体を抽象的に反映している:

* Sections 1–4 (固定点一意性, 枝・葉構造, 跡公式) ↦ `D19Hypotheses` の各フィールド.
* Section 5 (補題 5.2) ↦ `Dq_le_two` フィールド (独立に `Dq_le_two_of_no_four_cycle` でも証明).
* Section 6 (主計数論証) ↦ `D19Hypotheses.contradiction`.
-/
theorem no_D19_subgroup : ¬ Nonempty D19Hypotheses := by
  rintro ⟨h⟩; exact h.contradiction

/-! ### 具体版: Moore graph と具体軌道データの両立不能性 -/

/-- Moore57 上では Section 5/6 用の具体軌道データは存在しない.

これは `D19ConcreteHypotheses` を主定理の仮定として使う代わりに, その非存在を
直接述べる形である. `D_{19}` 作用そのものからこのデータを構成する Sections 1–4 の
幾何的部分は, ここではまだ主張しない. -/
theorem no_D19_concrete_hypotheses
    {V : Type*} [Fintype V] [DecidableEq V]
    {Γ : SimpleGraph V} [DecidableRel Γ.Adj]
    (hΓ : IsMoore57 Γ) : ¬ Nonempty (D19ConcreteHypotheses Γ) :=
  D19ConcreteHypotheses.not_nonempty hΓ

end Moore57
