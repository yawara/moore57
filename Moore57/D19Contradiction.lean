import Mathlib.Combinatorics.SimpleGraph.StronglyRegular
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.GroupTheory.SpecificGroups.Dihedral
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Moore graph of degree 57 contradicts $D_{19}$ as automorphism subgroup

仮想的な Moore graph $\Gamma$ of degree $57$ and diameter $2$ について,
$D_{19}\le\operatorname{Aut}(\Gamma)$ が不可能であることを証明する.

対応する自然言語証明は `moore57_d19_contradiction.md` に詳述されている.

## 構成

* `Moore57.IsMoore57` — Moore graph of degree $57$.
  Mathlib の `SimpleGraph.IsSRGWith 3250 57 0 1` の略記.
* `Moore57.D19Hypotheses` — $D_{19}$ 作用の下で成立する構造データ.
  自然言語証明の Sections 1–4 の主張を仮定として束ねる.
* `Moore57.Dq_card_le_two_of_moore` — Section 5 (補題 5.2) の形式化.
  $4$-cycle 禁止から $|D_q|\le 2$ を導く.
* `Moore57.counting_contradiction` — Section 6 の核となる抽象計数補題.
* `Moore57.D19Hypotheses.contradiction` — `D19Hypotheses` から `False`.
* `Moore57.D19ConcreteHypotheses.contradiction` — 具体軌道データから `False`.
* `Moore57.no_D19_subgroup` — 主定理: $\Gamma$ に `D19Hypotheses` 型のデータが
  存在しないことを述べる. `D_{19}\le\operatorname{Aut}(\Gamma)` が不可能で
  あることの形式的記述.

## 形式化方針

Sections 1–4 (固定点の一意性, 枝・葉の構造, 跡公式と表現論) は深い議論を含む
ため, 現時点ではそれらの結論のうち軌道データの構成と `Nd_lower` を
`D19ConcreteHypotheses` への変換公理として受け入れる.

それに対し, Section 5 の $4$-cycle 障害および Section 6 の計数論証は
組合せ的・初等的であり, ここで完全に形式化する.
-/

open Finset SimpleGraph

namespace Moore57

/-! ### 仮想 Moore graph -/

/-- Moore graph of degree $57$, diameter $2$. パラメータ $(3250,57,0,1)$ の強正則
グラフ. $\lambda=0$: 三角形なし. $\mu=1$: 任意の非隣接二点は一意の共通近傍を持つ
(ゆえに $4$-cycle なし). -/
abbrev IsMoore57 {V : Type*} [Fintype V] (Γ : SimpleGraph V) [DecidableRel Γ.Adj] : Prop :=
  Γ.IsSRGWith 3250 57 0 1

namespace IsMoore57

/-- Moore graph パラメータ $(3250,57,0,1)$ から三角形禁止を取り出す. -/
theorem no_triangle {V : Type*} [Fintype V] [DecidableEq V]
    {Γ : SimpleGraph V} [DecidableRel Γ.Adj]
    (hΓ : IsMoore57 Γ) {x y z : V}
    (hxy : Γ.Adj x y) (hyz : Γ.Adj y z) (hzx : Γ.Adj z x) : False := by
  have hcard : Fintype.card (Γ.commonNeighbors x y) = 0 := hΓ.of_adj x y hxy
  have hmem : z ∈ Γ.commonNeighbors x y := by
    rw [SimpleGraph.mem_commonNeighbors]
    exact ⟨hzx.symm, hyz⟩
  have hpos : 0 < Fintype.card (Γ.commonNeighbors x y) := by
    rw [Fintype.card_pos_iff]
    exact ⟨⟨z, hmem⟩⟩
  omega

/-- Moore graph パラメータ $(3250,57,0,1)$ から 4-cycle 禁止を取り出す.

ここでの 4-cycle は `x0 ~ x1 ~ x2 ~ x3 ~ x0` かつ 4 頂点が相異なるもの.
対角 `x0,x2` は三角形禁止により非隣接で, `x1,x3` が 2 つの共通近傍に
なるため, `μ = 1` に反する. -/
theorem no_four_cycle {V : Type*} [Fintype V] [DecidableEq V]
    {Γ : SimpleGraph V} [DecidableRel Γ.Adj]
    (hΓ : IsMoore57 Γ) {x0 x1 x2 x3 : V}
    (_h01ne : x0 ≠ x1) (h02 : x0 ≠ x2) (_h03 : x0 ≠ x3)
    (_h12ne : x1 ≠ x2) (h13 : x1 ≠ x3) (_h23ne : x2 ≠ x3)
    (h01 : Γ.Adj x0 x1) (h12 : Γ.Adj x1 x2)
    (h23 : Γ.Adj x2 x3) (h30 : Γ.Adj x3 x0) : False := by
  have h02_not_adj : ¬ Γ.Adj x0 x2 := by
    intro h
    exact hΓ.no_triangle h01 h12 h.symm
  have hcard : Fintype.card (Γ.commonNeighbors x0 x2) = 1 :=
    hΓ.of_not_adj h02 h02_not_adj
  have hpair_subset : ({x1, x3} : Finset V) ⊆ (Γ.commonNeighbors x0 x2).toFinset := by
    intro x hx
    rw [Set.mem_toFinset]
    rw [SimpleGraph.mem_commonNeighbors]
    rw [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact ⟨h01, h12.symm⟩
    · exact ⟨h30.symm, h23⟩
  have htwo : 2 ≤ Fintype.card (Γ.commonNeighbors x0 x2) := by
    rw [← Set.toFinset_card]
    have hcardpair : ({x1, x3} : Finset V).card = 2 := by
      simp [h13]
    exact hcardpair ▸ Finset.card_le_card hpair_subset
  omega

end IsMoore57

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

/-- Moore graph 上の軌道データに対する補題 5.2.

`IsMoore57.no_four_cycle` と `Dq_card_le_two_of_no_four_cycle` を組み合わせた形.
従って, 単一軌道内の「4-cycle 障害」そのものは `d19ConcreteHypotheses_of_action`
型の公理とは独立に証明済みである. -/
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

/-! ## 具体軌道データからの矛盾

`D19Hypotheses` は Section 6 の抽象計数に合わせて差集合を `Fin 18` で表している.
一方, Section 5 の 4-cycle 論証は差を `ZMod 19` の非零元として扱う方が自然である.

以下の `D19ConcreteHypotheses` は, `D_{19}` 作用から構成されるべき軌道データのうち,
Section 5 と Section 6 に必要な部分だけを `ZMod 19` 上で保持する.
この構造が与えられれば, `|D_q|≤2` は仮定ではなく `Dq_card_le_two_of_moore` から導く.
-/

/-- Section 5/6 に必要な具体的軌道データ.

各 `q : Fin 56` について `W q : ZMod 19 → V` は同じ $B$-側 19-cycle の頂点列を表す.
`D q` はその軌道内で `W q i ~ W q (i+d)` となる非零差の集合である.
`Nd_lower` は跡公式・表現論から来る下界であり, この構造ではまだ仮定として残す. -/
structure D19ConcreteHypotheses
    {V : Type*} [Fintype V] [DecidableEq V]
    (Γ : SimpleGraph V) [DecidableRel Γ.Adj] where
  D : Fin 56 → Finset (ZMod 19)
  W : Fin 56 → ZMod 19 → V
  W_injective : ∀ q : Fin 56, Function.Injective (W q)
  D_zero : ∀ q : Fin 56, (0 : ZMod 19) ∉ D q
  D_symm : ∀ q : Fin 56, ∀ d : ZMod 19, d ∈ D q → -d ∈ D q
  D_adj :
    ∀ q : Fin 56, ∀ d : ZMod 19, d ∈ D q →
      ∀ i : ZMod 19, Γ.Adj (W q i) (W q (i + d))
  Nd_lower :
    ∀ d : ZMod 19, d ≠ 0 →
      8 ≤ ((Finset.univ : Finset (Fin 56)).filter (fun q => d ∈ D q)).card

namespace D19ConcreteHypotheses

variable {V : Type*} [Fintype V] [DecidableEq V]
    {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- 具体軌道データでは, Section 5 の上界 `|D_q|≤2` は 4-cycle 禁止から証明できる. -/
theorem Dq_le_two (hΓ : IsMoore57 Γ) (h : D19ConcreteHypotheses Γ) :
    ∀ q : Fin 56, (h.D q).card ≤ 2 := by
  intro q
  exact Dq_card_le_two_of_moore hΓ (h.W q) (h.W_injective q) (h.D q)
    (h.D_zero q) (h.D_adj q) (h.D_symm q)

/-- 具体軌道データからの矛盾. Section 5 の上界と Section 6 の計数を組み合わせる. -/
theorem contradiction (hΓ : IsMoore57 Γ) (h : D19ConcreteHypotheses Γ) : False :=
  counting_contradiction_zmod h.D h.D_zero (h.Dq_le_two hΓ) h.Nd_lower

end D19ConcreteHypotheses

/-! ## 主定理: $D_{19}\le\operatorname{Aut}(\Gamma)$ は不可能 -/

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

/-! ### 具体版: Moore graph + $D_{19}$ 作用との接続 -/

/-- 「Moore graph $\Gamma$ of degree $57$ に $D_{19}$ が忠実に作用する」状況を
表現するデータ. 主定理 (定理 6.1) を `IsMoore57` と `MulAction` の言葉で述べる
ための基底.

* `Γ` — 仮想 Moore graph $(3250,57,0,1)$.
* `smul` — $D_{19}$ の頂点集合への作用.
* `smul_adj` — 作用は隣接関係を保つ.
* `faithful` — 作用は忠実 ($D_{19}\hookrightarrow\operatorname{Aut}(\Gamma)$).
-/
structure D19ActsOnMoore57
    (V : Type*) [Fintype V] [DecidableEq V]
    (Γ : SimpleGraph V) [DecidableRel Γ.Adj] where
  /-- $\Gamma$ が Moore graph of degree $57$. -/
  isMoore : IsMoore57 Γ
  /-- $D_{19}$ の $V$ への作用. -/
  smul : DihedralGroup 19 → V → V
  /-- 単位元の作用は恒等. -/
  one_smul : ∀ v, smul 1 v = v
  /-- 作用は群の演算と整合. -/
  mul_smul : ∀ g g' v, smul (g * g') v = smul g (smul g' v)
  /-- 作用は隣接関係を保つ. -/
  smul_adj : ∀ g v w, Γ.Adj v w ↔ Γ.Adj (smul g v) (smul g w)
  /-- 作用は忠実 ($D_{19}\hookrightarrow\operatorname{Aut}(\Gamma)$). -/
  faithful : ∀ g g' : DihedralGroup 19,
    (∀ v, smul g v = smul g' v) → g = g'

namespace D19ActsOnMoore57

variable {V : Type*} [Fintype V] [DecidableEq V]
    {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- `IsMoore57` から頂点数 $3250$ を取り出す補助補題. -/
theorem card_vertices (h : D19ActsOnMoore57 V Γ) : Fintype.card V = 3250 :=
  h.isMoore.card

/-- `D19ActsOnMoore57` に含まれる作用データから各群元の頂点集合上の同値を作る. -/
noncomputable def smulEquiv (h : D19ActsOnMoore57 V Γ) (g : DihedralGroup 19) : V ≃ V where
  toFun := h.smul g
  invFun := h.smul g⁻¹
  left_inv := by
    intro v
    rw [← h.mul_smul, inv_mul_cancel, h.one_smul]
  right_inv := by
    intro v
    rw [← h.mul_smul, mul_inv_cancel, h.one_smul]

/-- 各群元の作用は全単射である. -/
theorem smul_bijective (h : D19ActsOnMoore57 V Γ) (g : DihedralGroup 19) :
    Function.Bijective (h.smul g) :=
  (h.smulEquiv g).bijective

/-- 隣接保存性から, 各群元はグラフ自己同型を与える. -/
noncomputable def smulIso (h : D19ActsOnMoore57 V Γ) (g : DihedralGroup 19) : Γ ≃g Γ where
  toEquiv := h.smulEquiv g
  map_rel_iff' := by
    intro v w
    exact (h.smul_adj g v w).symm

end D19ActsOnMoore57

/-- Sections 1–4 の議論から `D19ConcreteHypotheses` への変換 (本ファイルの範囲外).

仮想 Moore graph $\Gamma$ に $D_{19}$ が忠実に作用するなら, 自然言語証明の
Sections 1–4 の議論 (固定点一意性, 枝・葉構造の決定, 跡公式と表現論的制約)
を経由して, `D19ConcreteHypotheses` 型のデータが構成できる.

その構成は深い議論を含み, 本ファイルではまだ公理として受け入れる.

具体的には, この公理は次の事実を要約している:

* 命題 1.3: 位数 $19$ の元 $r$ は唯一の固定頂点 $u$ を持つ.
* 命題 2.3: $N(u)$ は $r$ の $19$-軌道 $A,B,C$ に分かれ, 反射 $t$ は $A$ を反転して
  $B,C$ を交換する.
* 補題 4.3 + 系 4.5: $B,C$-側のサイズ $38$ 軌道は $56$ 個ある. 各 $d\in\mathbb Z_{19}^{\ast}$
  について, $D_q$ に $d$ を含む軌道数 $N_d\ge 8$.

補題 5.2 の局所的な 4-cycle 論証自体は `Dq_card_le_two_of_moore` で証明済みである.
従ってこの公理には `|D_q|≤2` は含めず, 軌道データ `D,W` の構成と
跡公式・表現論からの `Nd_lower` の導出だけを残している.
-/
axiom d19ConcreteHypotheses_of_action
    {V : Type*} [Fintype V] [DecidableEq V]
    {Γ : SimpleGraph V} [DecidableRel Γ.Adj]
    (h : D19ActsOnMoore57 V Γ) :
    Nonempty (D19ConcreteHypotheses Γ)

/-- **主定理 (定理 6.1)**: 仮想 Moore graph $\Gamma$ of degree $57$ について,
$D_{19}$ が $\Gamma$ の自己同型群の部分群として忠実に作用することは不可能.

すなわち, $D_{19}\le\operatorname{Aut}(\Gamma)$ は成り立たない. -/
theorem no_D19_acts_on_Moore57
    {V : Type*} [Fintype V] [DecidableEq V]
    {Γ : SimpleGraph V} [DecidableRel Γ.Adj]
    (h : D19ActsOnMoore57 V Γ) : False :=
  let ⟨hyp⟩ := d19ConcreteHypotheses_of_action h
  hyp.contradiction h.isMoore

/-- **系 6.2**: $\operatorname{Aut}(\Gamma)\simeq D_{19}$ は不可能.

$\operatorname{Aut}(\Gamma)\simeq D_{19}$ なら $D_{19}$ が忠実に作用するため,
定理 6.1 (`no_D19_acts_on_Moore57`) に反する. -/
theorem no_aut_iso_D19
    {V : Type*} [Fintype V] [DecidableEq V]
    {Γ : SimpleGraph V} [DecidableRel Γ.Adj]
    (h : D19ActsOnMoore57 V Γ) : False :=
  no_D19_acts_on_Moore57 h

end Moore57
