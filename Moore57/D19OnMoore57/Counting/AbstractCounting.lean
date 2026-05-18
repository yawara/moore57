import Mathlib.Combinatorics.SimpleGraph.StronglyRegular
import Mathlib.GroupTheory.SpecificGroups.Dihedral
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Moore57.Foundations.GroupAction.FixedPoints
import Moore57.Foundations.GraphTheory.AdjacentMovedCount
import Moore57.Moore57Graph.Moore57Definition

/-!
# Abstract counting and arithmetic core (Tier 3)

This file extracts the Section 5 + Section 6 + Section 4 arithmetic content
from the original `D19Contradiction.lean`:

* `counting_contradiction`, `counting_contradiction_zmod` — Section 6 abstract
  counting lemma.
* `TraceRepresentationData`, `TraceCharacterData` — Section 4
  representation-theoretic input bundles.
* `a1_rotation_candidates_of_trace_representation`,
  `count_lower_of_a1_candidates`, `Nd_lower_of_trace_representation` —
  Section 4 arithmetic.
* `D19Hypotheses` + `contradiction` — abstract D₁₉ hypotheses.
* `Dq_le_two_of_no_four_cycle`, `Dq_card_le_two_of_moore` — Section 5
  (4-cycle obstruction).
* `internalDiffSet` — concrete difference set definition.

Used downstream by `D19OnMoore57/AbstractHypotheses` and the main theorem.
-/

open Finset SimpleGraph

namespace Moore57

/-! ## Section 6 の核: 抽象計数補題 -/

/-- 抽象計数補題.

仮定:
* `D : Fin 56 → Finset (Fin 18)` 各 $q$ に対し $D_q\subseteq\mathbb Z_{19}^{\ast}$.
* `hSize`: 各 $q$ について $|D_q|\le 2$ (補題 5.2).
* `hCount`: 各 $d$ について $|\{q:d\in D_q\}|\ge 8$ (系 4.5).

結論: 矛盾. なぜなら
$$\sum_q|D_q|=\sum_d|\{q:d\in D_q\}|\ge 18\cdot 8=144$$
かつ
$$\sum_q|D_q|\le 56\cdot 2=112.$$
-/
theorem counting_contradiction
    (D : Fin 56 → Finset (Fin 18))
    (hSize : ∀ q : Fin 56, (D q).card ≤ 2)
    (hCount : ∀ d : Fin 18,
      8 ≤ ((Finset.univ : Finset (Fin 56)).filter (fun q => d ∈ D q)).card) :
    False := by
  set total : ℕ := ∑ q : Fin 56, (D q).card with htotal
  -- 上界: $\sum_q|D_q|\le 56\cdot 2=112$
  have h_upper : total ≤ 112 := by
    have h1 : total ≤ ∑ _q : Fin 56, 2 := Finset.sum_le_sum (fun q _ => hSize q)
    simpa [Finset.sum_const, Finset.card_univ, Fintype.card_fin] using h1
  -- 双対計数: $\sum_q|D_q|=\sum_d|\{q:d\in D_q\}|$
  have h_swap :
      total
      = ∑ d : Fin 18, ((Finset.univ : Finset (Fin 56)).filter (fun q => d ∈ D q)).card := by
    have h_card : ∀ q : Fin 56,
        (D q).card
        = ((Finset.univ : Finset (Fin 18)).filter (fun d => d ∈ D q)).card := by
      intro q; rw [Finset.filter_univ_mem]
    calc total
        = ∑ q : Fin 56, ((Finset.univ : Finset (Fin 18)).filter (fun d => d ∈ D q)).card :=
            Finset.sum_congr rfl (fun q _ => h_card q)
      _ = ∑ q : Fin 56, ∑ d : Fin 18, (if d ∈ D q then (1 : ℕ) else 0) := by
            simp_rw [Finset.card_filter]
      _ = ∑ d : Fin 18, ∑ q : Fin 56, (if d ∈ D q then (1 : ℕ) else 0) :=
            Finset.sum_comm
      _ = ∑ d : Fin 18, ((Finset.univ : Finset (Fin 56)).filter (fun q => d ∈ D q)).card := by
            simp_rw [Finset.card_filter]
  -- 下界: $\sum_d N_d\ge 18\cdot 8=144$
  have h_lower : 144 ≤ total := by
    rw [h_swap]
    have h1 : ∑ _d : Fin 18, 8
              ≤ ∑ d : Fin 18,
                  ((Finset.univ : Finset (Fin 56)).filter (fun q => d ∈ D q)).card :=
      Finset.sum_le_sum (fun d _ => hCount d)
    simpa [Finset.sum_const, Finset.card_univ, Fintype.card_fin] using h1
  omega

/-- `ZMod 19` の非零元を直接添字にした抽象計数補題.

`D19Hypotheses` では非零差を `Fin 18` に畳み込んでいるが, 実際の軌道論証では
差は自然に `ZMod 19` の非零元として現れる. この形にしておくと,
`Dq_card_le_two_of_moore` で得た `|D_q| ≤ 2` をそのまま使える. -/
theorem counting_contradiction_zmod
    (D : Fin 56 → Finset (ZMod 19))
    (hZero : ∀ q : Fin 56, (0 : ZMod 19) ∉ D q)
    (hSize : ∀ q : Fin 56, (D q).card ≤ 2)
    (hCount : ∀ d : ZMod 19, d ≠ 0 →
      8 ≤ ((Finset.univ : Finset (Fin 56)).filter (fun q => d ∈ D q)).card) :
    False := by
  classical
  let nonzero : Finset (ZMod 19) := (Finset.univ : Finset (ZMod 19)).erase 0
  have h_nonzero_card : nonzero.card = 18 := by
    simp [nonzero, ZMod.card]
  set total : ℕ := ∑ q : Fin 56, (D q).card with htotal
  -- 上界: $\sum_q|D_q|\le 56\cdot 2=112$
  have h_upper : total ≤ 112 := by
    have h1 : total ≤ ∑ _q : Fin 56, 2 := Finset.sum_le_sum (fun q _ => hSize q)
    simpa [Finset.sum_const, Finset.card_univ, Fintype.card_fin] using h1
  -- 双対計数: 零差が入らないので `ZMod 19` の非零元だけを足せばよい.
  have h_swap :
      total
      = ∑ d ∈ nonzero,
          ((Finset.univ : Finset (Fin 56)).filter (fun q => d ∈ D q)).card := by
    have h_card : ∀ q : Fin 56,
        (D q).card = (nonzero.filter (fun d => d ∈ D q)).card := by
      intro q
      have h_subset : D q ⊆ nonzero := by
        intro d hd
        have hd0 : d ≠ 0 := by
          intro h
          exact hZero q (h ▸ hd)
        simp [nonzero, hd0]
      rw [filter_mem_eq_inter, Finset.inter_eq_right.mpr h_subset]
    calc total
        = ∑ q : Fin 56, (nonzero.filter (fun d => d ∈ D q)).card :=
            Finset.sum_congr rfl (fun q _ => h_card q)
      _ = ∑ q : Fin 56, ∑ d ∈ nonzero, (if d ∈ D q then (1 : ℕ) else 0) := by
            simp_rw [Finset.card_filter]
      _ = ∑ d ∈ nonzero, ∑ q : Fin 56, (if d ∈ D q then (1 : ℕ) else 0) := by
            rw [Finset.sum_comm]
      _ = ∑ d ∈ nonzero,
            ((Finset.univ : Finset (Fin 56)).filter (fun q => d ∈ D q)).card := by
            simp_rw [Finset.card_filter]
  -- 下界: 非零差は 18 個で, 各差が少なくとも 8 回出る.
  have h_lower : 144 ≤ total := by
    rw [h_swap]
    have h1 : ∑ _d ∈ nonzero, 8
              ≤ ∑ d ∈ nonzero,
                  ((Finset.univ : Finset (Fin 56)).filter (fun q => d ∈ D q)).card := by
      refine Finset.sum_le_sum ?_
      intro d hd
      exact hCount d (by simpa [nonzero] using hd)
    simpa [Finset.sum_const, h_nonzero_card] using h1
  omega

/-! ## Section 4 の算術部分: 跡公式と表現論的制約

以下では, 自然言語証明の Section 4 のうち, 最終計数で必要になる算術的帰結を
Lean 内で証明する.

`TraceRepresentationData a1` は次の入力だけを保持する:

* `a1 d`: 非自明回転 $r^d$ に対する $a_1(r^d)$.
* `alpha,beta,gamma`: $7$-固有空間の有理 $D_{19}$ 表現
  $\alpha\mathbf1+\beta\varepsilon+\gamma\rho$ の重複度.
* `reflection`: 反射の指標値 $\alpha-\beta=33$.
* `dimension`: $7$-固有空間の次元
  $\alpha+\beta+18\gamma=1729$.
* `minus8_trivial_nonneg`, `minus8_sign_nonneg`: 頂点表現
  $114\mathbf1+58\varepsilon+171\rho$ から定数表現と $7$-固有空間を除いた
  $(-8)$-固有空間の係数が非負であることのうち, ここで必要な二つの不等式
  $\alpha\le113$, $\beta\le58$.
* `rotation_trace`: 非自明回転に対する Higman 型跡公式と有理表現の指標値から得る
  $a_1(r^d)-57=15(\alpha+\beta-\gamma)$.

これらから, 命題 4.4 の候補
`a1 d ∈ {57,342,627,912}` と, 系 4.5 の下界 `N_d ≥ 8` を導く.
-/

/-- Section 4.4 の純算術核.

跡公式・表現論の等式と $(-8)$-固有空間側の非負性から,
非自明回転の $a_1$ 値は `57,342,627,912` のいずれかに限られる. -/
theorem a1_rotation_candidates_of_trace_representation
    (alpha beta gamma a1 : ℕ)
    (hreflection : (alpha : ℤ) - (beta : ℤ) = 33)
    (hdimension : alpha + beta + 18 * gamma = 1729)
    (hminus8_trivial : alpha ≤ 113)
    (hminus8_sign : beta ≤ 58)
    (htrace : (a1 : ℤ) - 57 =
      15 * ((alpha : ℤ) + (beta : ℤ) - (gamma : ℤ))) :
    a1 = 57 ∨ a1 = 342 ∨ a1 = 627 ∨ a1 = 912 := by
  omega

/-- 非自明回転に対する Section 4 の跡公式・表現論データ. -/
structure TraceRepresentationData (a1 : ZMod 19 → ℕ) where
  /-- 自明有理表現の重複度 $\alpha$. -/
  alpha : ℕ
  /-- 符号表現の重複度 $\beta$. -/
  beta : ℕ
  /-- 18 次元有理既約表現の重複度 $\gamma$. -/
  gamma : ℕ
  /-- 反射の指標値: $\alpha-\beta=33$. -/
  reflection : (alpha : ℤ) - (beta : ℤ) = 33
  /-- $7$-固有空間の次元: $\alpha+\beta+18\gamma=1729$. -/
  dimension : alpha + beta + 18 * gamma = 1729
  /-- $(-8)$-固有空間の自明表現係数の非負性: $113-\alpha\ge0$. -/
  minus8_trivial_nonneg : alpha ≤ 113
  /-- $(-8)$-固有空間の符号表現係数の非負性: $58-\beta\ge0$. -/
  minus8_sign_nonneg : beta ≤ 58
  /-- 非自明回転に対する Higman 型跡公式と表現論的指標値の一致. -/
  rotation_trace :
    ∀ d : ZMod 19, d ≠ 0 →
      (a1 d : ℤ) - 57 =
        15 * ((alpha : ℤ) + (beta : ℤ) - (gamma : ℤ))

namespace TraceRepresentationData

variable {a1 : ZMod 19 → ℕ}

/-- 命題 4.4: 非自明回転の $a_1$ 値の候補. -/
theorem a1_candidates (h : TraceRepresentationData a1) {d : ZMod 19} (hd : d ≠ 0) :
    a1 d = 57 ∨ a1 d = 342 ∨ a1 d = 627 ∨ a1 d = 912 :=
  a1_rotation_candidates_of_trace_representation
    h.alpha h.beta h.gamma (a1 d)
    h.reflection h.dimension h.minus8_trivial_nonneg h.minus8_sign_nonneg
    (h.rotation_trace d hd)

end TraceRepresentationData

/-- Moore graph 上の実際の回転置換と, $7$-固有空間の指標値を結びつける Section 4
のデータ.

ここでは `TraceRepresentationData.rotation_trace` の整数等式を直接仮定しない.
代わりに, 各非自明回転 `rotation d` について

* 固定点数が `1`,
* `a1 d` が `adjacentMovedCount Γ (rotation d)` であること,
* 表現論側の指標値
  `trace (E7Matrix Γ * permMatrix (rotation d)) = α + β - γ`

を仮定する. Higman 跡公式そのものは
`rotation_trace_eq_of_higman_character` で Lean 内で適用する. -/
structure TraceCharacterData
    {V : Type*} [Fintype V] [DecidableEq V]
    (Γ : SimpleGraph V) [DecidableRel Γ.Adj]
    (rotation : ZMod 19 → Equiv.Perm V)
    (a1 : ZMod 19 → ℕ) where
  /-- 自明有理表現の重複度 $\alpha$. -/
  alpha : ℕ
  /-- 符号表現の重複度 $\beta$. -/
  beta : ℕ
  /-- 18 次元有理既約表現の重複度 $\gamma$. -/
  gamma : ℕ
  /-- 反射の指標値: $\alpha-\beta=33$. -/
  reflection : (alpha : ℤ) - (beta : ℤ) = 33
  /-- $7$-固有空間の次元: $\alpha+\beta+18\gamma=1729$. -/
  dimension : alpha + beta + 18 * gamma = 1729
  /-- $(-8)$-固有空間の自明表現係数の非負性: $113-\alpha\ge0$. -/
  minus8_trivial_nonneg : alpha ≤ 113
  /-- $(-8)$-固有空間の符号表現係数の非負性: $58-\beta\ge0$. -/
  minus8_sign_nonneg : beta ≤ 58
  /-- 非自明回転は唯一の固定頂点を持つ. -/
  rotation_fixed :
    ∀ d : ZMod 19, d ≠ 0 → fixedVertexCount (rotation d) = 1
  /-- `a1 d` は回転 `rotation d` が隣接頂点へ送る頂点数である. -/
  rotation_a1 :
    ∀ d : ZMod 19, d ≠ 0 → adjacentMovedCount Γ (rotation d) = a1 d
  /-- 表現論側の指標値. Higman 跡公式はここでは仮定しない. -/
  rotation_character :
    ∀ d : ZMod 19, d ≠ 0 →
      Matrix.trace (E7Matrix Γ * permMatrix (rotation d)) =
        (alpha : ℚ) + (beta : ℚ) - (gamma : ℚ)

namespace TraceCharacterData

variable {V : Type*} [Fintype V] [DecidableEq V]
    {Γ : SimpleGraph V} [DecidableRel Γ.Adj]
    {rotation : ZMod 19 → Equiv.Perm V}
    {a1 : ZMod 19 → ℕ}

/-- `TraceCharacterData` から, 算術補題が要求する `TraceRepresentationData` を作る.

この変換で Higman 跡公式を使うため, 具体的な Moore graph 仮定 `hΓ` が必要になる. -/
def toTraceRepresentationData
    (h : TraceCharacterData Γ rotation a1) (hΓ : IsMoore57 Γ) :
    TraceRepresentationData a1 where
  alpha := h.alpha
  beta := h.beta
  gamma := h.gamma
  reflection := h.reflection
  dimension := h.dimension
  minus8_trivial_nonneg := h.minus8_trivial_nonneg
  minus8_sign_nonneg := h.minus8_sign_nonneg
  rotation_trace := by
    intro d hd
    exact rotation_trace_eq_of_higman_character hΓ (rotation d)
      (h.rotation_fixed d hd) (h.rotation_a1 d hd) (h.rotation_character d hd)

end TraceCharacterData

/-- Section 4.5 の最終算術.

`a1 = 38 + 38N` と候補 `57,342,627,912` を組み合わせると,
実際に可能なのは `N=8` または `N=23` だけである. -/
theorem count_lower_of_a1_candidates
    {a1 N : ℕ}
    (hcand : a1 = 57 ∨ a1 = 342 ∨ a1 = 627 ∨ a1 = 912)
    (hcontribution : a1 = 38 + 38 * N) :
    8 ≤ N := by
  rcases hcand with h57 | h342 | h627 | h912
  · omega
  · omega
  · omega
  · omega

/-- 系 4.5: 跡公式・表現論の候補と寄与公式から `N_d ≥ 8` を導く. -/
theorem Nd_lower_of_trace_representation
    (D : Fin 56 → Finset (ZMod 19))
    (a1 : ZMod 19 → ℕ)
    (traceRep : TraceRepresentationData a1)
    (hContribution :
      ∀ d : ZMod 19, d ≠ 0 →
        a1 d =
          38 + 38 *
            ((Finset.univ : Finset (Fin 56)).filter (fun q => d ∈ D q)).card) :
    ∀ d : ZMod 19, d ≠ 0 →
      8 ≤ ((Finset.univ : Finset (Fin 56)).filter (fun q => d ∈ D q)).card := by
  intro d hd
  let N : ℕ := ((Finset.univ : Finset (Fin 56)).filter (fun q => d ∈ D q)).card
  change 8 ≤ N
  have hcand : a1 d = 57 ∨ a1 d = 342 ∨ a1 d = 627 ∨ a1 d = 912 :=
    traceRep.a1_candidates hd
  have hcontribution : a1 d = 38 + 38 * N := by
    simpa [N] using hContribution d hd
  exact count_lower_of_a1_candidates hcand hcontribution

/-! ## $D_{19}$ 作用の構造データ

`D19Hypotheses` は Sections 1–4 で確立される構造を束ねた仮定の集合である.

* `D` — 各 $B,C$-軌道 $q$ について「内部差集合」$D_q\subseteq\mathbb Z_{19}^{\ast}$.
  すなわち軌道 $Q_q$ における $b_i\sim b_{i+d}$ となる $d$ の集合.
* `Nd_lower` — 系 4.5 から得られる下界 ($N_d\ge 8$).
* `Dq_le_two` — 補題 5.2 の結論 ($|D_q|\le 2$).

軌道は補題 4.3 で $56$ 個と判明しているので, ここでは `Fin 56` で添字付けする.
-/

/-- $\Gamma$ が `IsMoore57` であって, かつ $D_{19}\le\operatorname{Aut}(\Gamma)$
を仮定する場合に Sections 1–4 から得られる構造データの束.

このデータは以下の自然言語的事実に対応する:

1. $r$ の唯一固定点 $u$ が存在し, $D_{19}$ 全体で固定される (命題 1.3).
2. $N(u)$ は $19$-軌道 $A$, $B$, $C$ に分かれ, $t$ は $A$ を反転して $B,C$ を交換する (命題 2.3).
3. $B,C$-側の葉は $56$ 個のサイズ $38$ 軌道に分かれる.
4. 各軌道 $q$ について, $b_i^q\sim b_{i+d}^q$ となる差 $d\in\mathbb Z_{19}^{\ast}$
   の集合を $D_q$ とすると, $D_q$ は $\pm$ 対称.
5. 系 4.5 (跡公式と表現論) より, 各 $d\ne 0$ について $D_q$ にその $d$ を含む軌道
   の数 $N_d\ge 8$.
6. $\Gamma$ が三角形・$4$-cycle を持たないこと, 及び各軌道内で $b_0,b_a,b_{a+b},b_b$
   が互いに異なる頂点になること (Section 5).

ここでは, それらを `D19Hypotheses` の各フィールドとしてまとめる.
-/
structure D19Hypotheses where
  /-- 各軌道 $q\in\mathrm{Fin}\,56$ について, その「内部差集合」 $D_q\subseteq\mathbb Z_{19}^{\ast}$.
  $\mathbb Z_{19}^{\ast}=\mathbb Z/19\setminus\{0\}\simeq\mathrm{Fin}\,18$.

  軌道集合は補題 4.3 から得られる $56$ 個 ($\dfrac{2\cdot 19\cdot 56}{38}=56$) の
  サイズ $38$ 軌道全体である. これを `Fin 56` で添字付けする. -/
  D : Fin 56 → Finset (Fin 18)
  /-- 系 4.5 の下界: 各 $d\ne 0$ について $D_q$ が $d$ を含む軌道の数は $8$ 以上. -/
  Nd_lower :
    ∀ d : Fin 18,
      8 ≤ ((Finset.univ : Finset (Fin 56)).filter (fun q => d ∈ D q)).card
  /-- 補題 5.2 の結論: 各軌道 $q$ について $|D_q|\le 2$.

  これは「$4$-cycle なし」から導かれる. 別個の関数
  `Dq_le_two_of_no_four_cycle` で抽象的に証明可能.
  -/
  Dq_le_two : ∀ q : Fin 56, (D q).card ≤ 2

namespace D19Hypotheses

/-- `D19Hypotheses` から矛盾を導く. 計数論証 (Section 6) に帰着. -/
theorem contradiction (h : D19Hypotheses) : False :=
  counting_contradiction h.D h.Dq_le_two h.Nd_lower

end D19Hypotheses

/-! ## 補題 5.2 の独立証明 (4-cycle 禁止から $|D_q|\le 2$)

$D_{19}$ 軌道の片側 $B$-側のみに着目する. 軌道 $Q_q$ における $B$-側の頂点
$b_0^q,\dots,b_{18}^q\in V$ を, $r$-作用が $b_i^q\mapsto b_{i+1}^q$ となる
ように添字付ける. 「内部差」$d$ とは, $b_i^q\sim b_{i+d}^q$ が成り立つような
$d\in\mathbb Z_{19}^{\ast}$ である. これは $i$ によらない (なぜなら $r$ は
グラフ自己同型だから).

$D_q$ にいくつ要素が入るか: もし相異なる二つの値 $a,b\in D_q$ で $a\ne\pm b$
なるものがあれば, 4 頂点 $b_0,b_a,b_{a+b},b_b$ が $4$-cycle を成し, $\mu=1$ に
反する. これが補題 5.2 の主張である.

ここではその抽象版として, 一般の有限頂点集合 $W$, $r:W\to W$ が位数 $19$ の置換,
4-cycle なし条件を仮定して証明する.

抽象構造 `D19Hypotheses` ではこの結論を `Dq_le_two` フィールドとして保持する.
一方, 具体構造 `D19ConcreteHypotheses` では以下の補題を使ってこの結論を導く.
-/

/-- 補題 5.2 の抽象形.

仮定:
* 頂点集合 $V$, 隣接関係 $\mathrm{Adj}$.
* $4$-cycle 禁止: $4$ 頂点 $x_0,x_1,x_2,x_3$ が相異なり, $x_0\sim x_1\sim x_2\sim x_3\sim x_0$
  なら矛盾.
* 軌道 $W:\mathrm{Fin}\,19\to V$ は単射.
* 「差 $d\in\mathbb Z_{19}^{\ast}$ が $D$ に属するとき, 任意の $i$ について $W(i)\sim W(i+d)$」.

結論: $D$ 内に $a\ne 0$ が含まれるとき, $D\subseteq\{a,-a\}$ (つまり $|D|\le 2$).
-/
theorem Dq_le_two_of_no_four_cycle
    {V : Type*} (Adj : V → V → Prop)
    (W : ZMod 19 → V) (hInj : Function.Injective W)
    (no_four_cycle : ∀ x0 x1 x2 x3 : V,
      x0 ≠ x1 → x0 ≠ x2 → x0 ≠ x3 → x1 ≠ x2 → x1 ≠ x3 → x2 ≠ x3 →
      Adj x0 x1 → Adj x1 x2 → Adj x2 x3 → Adj x3 x0 → False)
    (D : Finset (ZMod 19))
    (hZero : (0 : ZMod 19) ∉ D)
    (hAdj : ∀ d ∈ D, ∀ i : ZMod 19, Adj (W i) (W (i + d)))
    (hSym : ∀ d ∈ D, -d ∈ D)
    (a b : ZMod 19) (haD : a ∈ D) (hbD : b ∈ D)
    (hab : a ≠ b) (habn : a ≠ -b) : False := by
  -- $a, b \in D$ で $a \ne \pm b$ なら 4-cycle が出る
  have ha0 : a ≠ 0 := fun h => hZero (h ▸ haD)
  have hb0 : b ≠ 0 := fun h => hZero (h ▸ hbD)
  -- 4 頂点 W(0), W(a), W(a+b), W(b) を考える
  -- これらが相異なることを示す
  have ne01 : (0 : ZMod 19) ≠ a := fun h => ha0 h.symm
  have ne0ab : (0 : ZMod 19) ≠ a + b := by
    intro h
    -- 0 = a + b ⇒ a = -b, 仮定に反する
    exact habn (eq_neg_of_add_eq_zero_left h.symm)
  have ne0b : (0 : ZMod 19) ≠ b := fun h => hb0 h.symm
  have neaab : a ≠ a + b := by
    intro h
    -- a = a + b ⇒ b = 0
    apply hb0
    have h' : a + b = a + 0 := by rw [add_zero]; exact h.symm
    exact add_left_cancel h'
  have neab : a ≠ b := hab
  have neabb : a + b ≠ b := by
    intro h
    -- a + b = b ⇒ a = 0
    apply ha0
    have h' : a + b = 0 + b := by rw [zero_add]; exact h
    exact add_right_cancel h'
  -- 単射性で V 上の頂点も相異なる
  have hne01 : W 0 ≠ W a := fun h => ne01 (hInj h)
  have hne0ab : W 0 ≠ W (a + b) := fun h => ne0ab (hInj h)
  have hne0b : W 0 ≠ W b := fun h => ne0b (hInj h)
  have hneaab : W a ≠ W (a + b) := fun h => neaab (hInj h)
  have hneab : W a ≠ W b := fun h => neab (hInj h)
  have hneabb : W (a + b) ≠ W b := fun h => neabb (hInj h)
  -- 辺の存在: $d=a$ について $W(i)\sim W(i+a)$, $d=b$ について $W(i)\sim W(i+b)$
  -- W(0) ~ W(a)
  have h01 : Adj (W 0) (W a) := by
    have := hAdj a haD 0
    simpa using this
  -- W(a) ~ W(a+b)
  have h12 : Adj (W a) (W (a + b)) := hAdj b hbD a
  -- W(a+b) ~ W(b)
  -- これは d = -a について: W(b) ~ W(b + (-a)) = W(b - a). しかし我々は a+b の方が欲しい.
  -- 言い換えると, W(a+b) ~ W(b) ⇔ W(b) ~ W(a+b) ⇔ W(b) ~ W(b + a).
  -- つまり d = a で i = b. これは hAdj a haD b で得られる.
  have h23 : Adj (W (a + b)) (W b) := by
    have hba : Adj (W b) (W (b + a)) := hAdj a haD b
    have : W (b + a) = W (a + b) := by rw [add_comm]
    rw [this] at hba
    -- 対称性が必要. しかし Adj は方向性ありで定義された.
    -- このため対称性を仮定として追加する必要がある (or W(a+b) ~ W(b) を直接示す).
    -- ここでは hSym を使う代替策として, d = -a を考える.
    -- W(a+b) ~ W(a+b + (-a)) = W(b) は hAdj (-a) (hSym a haD) (a+b) で得られる.
    have h_neg_a_in_D : -a ∈ D := hSym a haD
    have hne_a := hAdj (-a) h_neg_a_in_D (a + b)
    have : (a + b) + (-a) = b := by ring
    rw [this] at hne_a
    exact hne_a
  -- W(b) ~ W(0)
  have h30 : Adj (W b) (W 0) := by
    have h_neg_b_in_D : -b ∈ D := hSym b hbD
    have hne := hAdj (-b) h_neg_b_in_D b
    have : b + (-b) = 0 := by ring
    rw [this] at hne
    exact hne
  -- 4-cycle: W(0) ~ W(a) ~ W(a+b) ~ W(b) ~ W(0)
  exact no_four_cycle (W 0) (W a) (W (a + b)) (W b)
    hne01 hne0ab hne0b hneaab hneab hneabb h01 h12 h23 h30

/-- 補題 5.2 の `card ≤ 2` 版.

`Dq_le_two_of_no_four_cycle` は「`a ≠ ± b` なら 4-cycle が出る」ことを示す
局所補題である. この補題はそこから実際に `D.card ≤ 2` を導く. -/
theorem Dq_card_le_two_of_no_four_cycle
    {V : Type*} (Adj : V → V → Prop)
    (W : ZMod 19 → V) (hInj : Function.Injective W)
    (no_four_cycle : ∀ x0 x1 x2 x3 : V,
      x0 ≠ x1 → x0 ≠ x2 → x0 ≠ x3 → x1 ≠ x2 → x1 ≠ x3 → x2 ≠ x3 →
      Adj x0 x1 → Adj x1 x2 → Adj x2 x3 → Adj x3 x0 → False)
    (D : Finset (ZMod 19))
    (hZero : (0 : ZMod 19) ∉ D)
    (hAdj : ∀ d ∈ D, ∀ i : ZMod 19, Adj (W i) (W (i + d)))
    (hSym : ∀ d ∈ D, -d ∈ D) :
    D.card ≤ 2 := by
  classical
  have hpair : ∀ a ∈ D, ∀ b ∈ D, b = a ∨ b = -a := by
    intro a ha b hb
    by_cases hba : b = a
    · exact Or.inl hba
    · by_cases hbneg : b = -a
      · exact Or.inr hbneg
      · exact False.elim
          (Dq_le_two_of_no_four_cycle Adj W hInj no_four_cycle D hZero hAdj hSym
            b a hb ha hba hbneg)
  by_cases hD : D.Nonempty
  · rcases hD with ⟨a, ha⟩
    have hsubset : D ⊆ ({a, -a} : Finset (ZMod 19)) := by
      intro b hb
      rcases hpair a ha b hb with hba | hba
      · simp [hba]
      · simp [hba]
    exact (Finset.card_le_card hsubset).trans Finset.card_le_two
  · have hEmpty : D = ∅ := Finset.not_nonempty_iff_eq_empty.mp hD
    simp [hEmpty]

set_option linter.unusedDecidableInType false in
/-- Moore graph 上の軌道データに対する補題 5.2.

`IsMoore57.no_four_cycle` と `Dq_card_le_two_of_no_four_cycle` を組み合わせた形.
従って, 単一軌道内の「4-cycle 障害」そのものは追加仮定なしで証明済みである. -/
theorem Dq_card_le_two_of_moore
    {V : Type*} [Fintype V] [DecidableEq V]
    {Γ : SimpleGraph V} [DecidableRel Γ.Adj]
    (hΓ : IsMoore57 Γ)
    (W : ZMod 19 → V) (hInj : Function.Injective W)
    (D : Finset (ZMod 19))
    (hZero : (0 : ZMod 19) ∉ D)
    (hAdj : ∀ d ∈ D, ∀ i : ZMod 19, Γ.Adj (W i) (W (i + d)))
    (hSym : ∀ d ∈ D, -d ∈ D) :
    D.card ≤ 2 :=
  Dq_card_le_two_of_no_four_cycle
    (Adj := Γ.Adj) W hInj (fun _ _ _ _ => hΓ.no_four_cycle) D hZero hAdj hSym

/-- 1 つの $B$-側 19-cycle `W` から定まる内部差集合.

`d` がこの集合に入るとは, `d≠0` かつ全ての `i` で
`W i ~ W (i+d)` となることを意味する. -/
noncomputable def internalDiffSet
    {V : Type*} (Γ : SimpleGraph V) [DecidableRel Γ.Adj]
    (W : ZMod 19 → V) : Finset (ZMod 19) := by
  classical
  exact ((Finset.univ : Finset (ZMod 19)).erase 0).filter
    (fun d => ∀ i : ZMod 19, Γ.Adj (W i) (W (i + d)))

/-- 内部差集合には零差は入らない. -/
theorem internalDiffSet_zero
    {V : Type*} {Γ : SimpleGraph V} [DecidableRel Γ.Adj]
    (W : ZMod 19 → V) :
    (0 : ZMod 19) ∉ internalDiffSet Γ W := by
  classical
  simp [internalDiffSet]

/-- 内部差集合の定義から得られる隣接性. -/
theorem internalDiffSet_adj
    {V : Type*} {Γ : SimpleGraph V} [DecidableRel Γ.Adj]
    (W : ZMod 19 → V) {d : ZMod 19}
    (hd : d ∈ internalDiffSet Γ W) :
    ∀ i : ZMod 19, Γ.Adj (W i) (W (i + d)) := by
  classical
  have hd' :
      d ≠ 0 ∧ ∀ i : ZMod 19, Γ.Adj (W i) (W (i + d)) := by
    simpa [internalDiffSet] using hd
  exact hd'.2

/-- 無向性により, 内部差集合は符号反転で閉じている. -/
theorem internalDiffSet_symm
    {V : Type*} {Γ : SimpleGraph V} [DecidableRel Γ.Adj]
    (W : ZMod 19 → V) {d : ZMod 19}
    (hd : d ∈ internalDiffSet Γ W) :
    -d ∈ internalDiffSet Γ W := by
  classical
  have hd0 : d ≠ 0 := by
    have hd' :
        d ≠ 0 ∧ ∀ i : ZMod 19, Γ.Adj (W i) (W (i + d)) := by
      simpa [internalDiffSet] using hd
    exact hd'.1
  have hAdj : ∀ i : ZMod 19, Γ.Adj (W i) (W (i + d)) :=
    internalDiffSet_adj W hd
  have hneg0 : -d ≠ 0 := by
    intro h
    apply hd0
    simpa using congrArg Neg.neg h
  rw [internalDiffSet]
  rw [Finset.mem_filter]
  refine ⟨?_, ?_⟩
  · simp [hneg0]
  · intro i
    have h := (hAdj (i + -d)).symm
    simpa [add_assoc] using h

end Moore57
