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
* `Moore57.D19Hypotheses.Dq_le_two` — Section 5 (補題 5.2) の形式化.
  $4$-cycle 禁止から $|D_q|\le 2$ を導く.
* `Moore57.counting_contradiction` — Section 6 の核となる抽象計数補題.
* `Moore57.D19Hypotheses.contradiction` — `D19Hypotheses` から `False`.
* `Moore57.no_D19_subgroup` — 主定理: $\Gamma$ に `D19Hypotheses` 型のデータが
  存在しないことを述べる. `D_{19}\le\operatorname{Aut}(\Gamma)` が不可能で
  あることの形式的記述.

## 形式化方針

Sections 1–4 (固定点の一意性, 枝・葉の構造, 跡公式と表現論) は深い議論を含む
ため, それらの結論を `D19Hypotheses` 構造の仮定として受け入れる.

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

実際には `D19Hypotheses` の `Dq_le_two` フィールドにこの結論をすでに含めている
ため, 以下は独立した形での補題 5.2 の形式化である.
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

/-- Sections 1–4 の議論から `D19Hypotheses` への変換 (本ファイルの範囲外).

仮想 Moore graph $\Gamma$ に $D_{19}$ が忠実に作用するなら, 自然言語証明の
Sections 1–4 の議論 (固定点一意性, 枝・葉構造の決定, 跡公式と表現論的制約)
を経由して, `D19Hypotheses` 型のデータが構成できる.

その構成は深い議論を含み, 本ファイルでは公理として受け入れる.

具体的には, この公理は次の事実を要約している:

* 命題 1.3: 位数 $19$ の元 $r$ は唯一の固定頂点 $u$ を持つ.
* 命題 2.3: $N(u)$ は $r$ の $19$-軌道 $A,B,C$ に分かれ, 反射 $t$ は $A$ を反転して
  $B,C$ を交換する.
* 補題 4.3 + 系 4.5: $B,C$-側のサイズ $38$ 軌道は $56$ 個ある. 各 $d\in\mathbb Z_{19}^{\ast}$
  について, $D_q$ に $d$ を含む軌道数 $N_d\ge 8$.
* 補題 5.2: 各軌道 $q$ について $|D_q|\le 2$.
-/
axiom d19Hypotheses_of_action
    {V : Type*} [Fintype V] [DecidableEq V]
    {Γ : SimpleGraph V} [DecidableRel Γ.Adj]
    (h : D19ActsOnMoore57 V Γ) :
    Nonempty D19Hypotheses

/-- **主定理 (定理 6.1)**: 仮想 Moore graph $\Gamma$ of degree $57$ について,
$D_{19}$ が $\Gamma$ の自己同型群の部分群として忠実に作用することは不可能.

すなわち, $D_{19}\le\operatorname{Aut}(\Gamma)$ は成り立たない. -/
theorem no_D19_acts_on_Moore57
    {V : Type*} [Fintype V] [DecidableEq V]
    {Γ : SimpleGraph V} [DecidableRel Γ.Adj]
    (h : D19ActsOnMoore57 V Γ) : False :=
  let ⟨hyp⟩ := d19Hypotheses_of_action h
  hyp.contradiction

/-- **系 6.2**: $\operatorname{Aut}(\Gamma)\simeq D_{19}$ は不可能.

$\operatorname{Aut}(\Gamma)\simeq D_{19}$ なら $D_{19}$ が忠実に作用するため,
定理 6.1 (`no_D19_acts_on_Moore57`) に反する. -/
theorem no_aut_iso_D19
    {V : Type*} [Fintype V] [DecidableEq V]
    {Γ : SimpleGraph V} [DecidableRel Γ.Adj]
    (h : D19ActsOnMoore57 V Γ) : False :=
  no_D19_acts_on_Moore57 h

end Moore57
