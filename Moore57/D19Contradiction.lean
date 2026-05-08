import Mathlib.Combinatorics.SimpleGraph.StronglyRegular
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Data.Matrix.PEquiv
import Mathlib.GroupTheory.SpecificGroups.Dihedral
import Mathlib.GroupTheory.Perm.Cycle.Type
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

Sections 1–3 と Section 4 の幾何・表現論データを具体軌道データへ接続する構成は
深い議論を含むため, 現時点では `D19ConcreteHypotheses` への変換公理として受け入れる.
ただし Higman 型跡公式は `E7Matrix` と `Matrix.trace` で Lean 内に展開し,
Section 4 から最終計数に使う下界 `Nd_lower` 自体は, 表現論側の
`TraceCharacterData` と寄与公式から Lean 内で証明する.

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

/-! ## Section 4 の行列的準備: Moore graph の跡公式 -/

section HigmanTrace

variable {V : Type*} [DecidableEq V]

/-- 有理係数の全ての成分が `1` である行列 `J`. -/
noncomputable def allOnesMatrix (V : Type*) : Matrix V V ℚ :=
  Matrix.of fun _ _ => (1 : ℚ)

/-- 置換 `σ` に付随する置換行列.

この向きでは `(A * permMatrix σ)` の対角成分が `A v (σ v)` になる. -/
noncomputable def permMatrix (σ : Equiv.Perm V) : Matrix V V ℚ :=
  σ.symm.toPEquiv.toMatrix

/-- Moore graph の $7$-固有空間への射影として使う行列. -/
noncomputable def E7Matrix (Γ : SimpleGraph V) [DecidableRel Γ.Adj] : Matrix V V ℚ :=
  (1 / 15 : ℚ) • (Γ.adjMatrix ℚ + (8 : ℚ) • (1 : Matrix V V ℚ))
    - (1 / 750 : ℚ) • allOnesMatrix V

/-- `J = 1 + A + Aᶜ` を有理係数行列として書き直した形. -/
theorem compl_adjMatrix_eq_allOnes_sub_one_sub_adjMatrix
    (Γ : SimpleGraph V) [DecidableRel Γ.Adj] :
    Γᶜ.adjMatrix ℚ = allOnesMatrix V - 1 - Γ.adjMatrix ℚ := by
  ext v w
  by_cases hvw : v = w
  · subst w
    simp [allOnesMatrix]
  · by_cases hadj : Γ.Adj v w
    · simp [allOnesMatrix, hvw, hadj]
    · simp [allOnesMatrix, hvw, hadj]

variable [Fintype V]

/-- 置換の固定頂点数. -/
def fixedVertexCount (σ : Equiv.Perm V) : ℕ :=
  ((Finset.univ : Finset V).filter fun v => σ v = v).card

/-- `σ` が頂点を隣接頂点に送る頂点数. これは論文中の `a₁(σ)`. -/
def adjacentMovedCount (Γ : SimpleGraph V) [DecidableRel Γ.Adj] (σ : Equiv.Perm V) : ℕ :=
  ((Finset.univ : Finset V).filter fun v => Γ.Adj v (σ v)).card

/-- Moore graph パラメータから得る隣接行列関係
`A^2 = 56 I - A + J`. -/
theorem IsMoore57.adjMatrix_sq_eq
    {Γ : SimpleGraph V} [DecidableRel Γ.Adj] (hΓ : IsMoore57 Γ) :
    Γ.adjMatrix ℚ ^ 2 =
      (56 : ℚ) • (1 : Matrix V V ℚ) - Γ.adjMatrix ℚ + allOnesMatrix V := by
  ext v w
  have hentry := congrFun (congrFun (hΓ.matrix_eq (α := ℚ)) v) w
  rw [hentry]
  by_cases hvw : v = w
  · subst w
    norm_num [allOnesMatrix, Matrix.smul_apply, Matrix.ofNat_apply]
  · by_cases hadj : Γ.Adj v w
    · simp [allOnesMatrix, Matrix.smul_apply, Matrix.ofNat_apply, hvw, hadj]
    · simp [allOnesMatrix, Matrix.smul_apply, Matrix.ofNat_apply, hvw, hadj]

/-- 右から `permMatrix σ` を掛けると列が `σ` で置換される. -/
theorem mul_permMatrix_apply (M : Matrix V V ℚ) (σ : Equiv.Perm V) (v w : V) :
    (M * permMatrix σ) v w = M v (σ w) := by
  classical
  rw [Matrix.mul_apply]
  calc
    ∑ u : V, M v u * permMatrix σ u w
        = M v (σ w) * permMatrix σ (σ w) w := by
          refine Finset.sum_eq_single (σ w) ?_ ?_
          · intro u _ hu
            have hne : w ≠ σ.symm u := by
              intro h
              apply hu
              calc
                u = σ (σ.symm u) := (σ.apply_symm_apply u).symm
                _ = σ w := by rw [← h]
            have hne' : σ.symm u ≠ w := fun h => hne h.symm
            simp [permMatrix, hne']
          · intro h
            exact False.elim (h (Finset.mem_univ _))
    _ = M v (σ w) := by
          simp [permMatrix]

/-- 置換行列の跡は固定頂点数である. -/
theorem trace_permMatrix_eq_fixedVertexCount (σ : Equiv.Perm V) :
    Matrix.trace (permMatrix σ) = (fixedVertexCount σ : ℚ) := by
  classical
  rw [Matrix.trace]
  calc
    ∑ v : V, Matrix.diag (permMatrix σ) v
        = ∑ v : V, if σ v = v then (1 : ℚ) else 0 := by
          refine Finset.sum_congr rfl ?_
          intro v _
          have h := mul_permMatrix_apply (M := (1 : Matrix V V ℚ)) σ v v
          simpa [Matrix.diag, Matrix.one_mul, Matrix.one_apply, eq_comm] using h
    _ = (fixedVertexCount σ : ℚ) := by
          simp [fixedVertexCount]

/-- `trace (A * P_σ)` は `v ~ σ v` となる頂点数である. -/
theorem trace_adjMatrix_mul_permMatrix_eq_adjacentMovedCount
    (Γ : SimpleGraph V) [DecidableRel Γ.Adj] (σ : Equiv.Perm V) :
    Matrix.trace (Γ.adjMatrix ℚ * permMatrix σ) =
      (adjacentMovedCount Γ σ : ℚ) := by
  classical
  rw [Matrix.trace]
  calc
    ∑ v : V, Matrix.diag (Γ.adjMatrix ℚ * permMatrix σ) v
        = ∑ v : V, if Γ.Adj v (σ v) then (1 : ℚ) else 0 := by
          refine Finset.sum_congr rfl ?_
          intro v _
          change (Γ.adjMatrix ℚ * permMatrix σ) v v =
            if Γ.Adj v (σ v) then (1 : ℚ) else 0
          rw [mul_permMatrix_apply]
          simp
    _ = (adjacentMovedCount Γ σ : ℚ) := by
          simp [adjacentMovedCount]

/-- `J P_σ = J` から従う跡の形. -/
theorem trace_allOnes_mul_permMatrix (σ : Equiv.Perm V) :
    Matrix.trace (allOnesMatrix V * permMatrix σ) = (Fintype.card V : ℚ) := by
  classical
  rw [Matrix.trace]
  calc
    ∑ v : V, Matrix.diag (allOnesMatrix V * permMatrix σ) v
        = ∑ _v : V, (1 : ℚ) := by
          refine Finset.sum_congr rfl ?_
          intro v _
          change (allOnesMatrix V * permMatrix σ) v v = (1 : ℚ)
          rw [mul_permMatrix_apply]
          simp [allOnesMatrix]
    _ = (Fintype.card V : ℚ) := by
          simp

/-- `E₇` と置換行列の跡を `a₀`, `a₁` で展開する一般形. -/
theorem trace_E7Matrix_mul_permMatrix
    (Γ : SimpleGraph V) [DecidableRel Γ.Adj] (σ : Equiv.Perm V) :
    Matrix.trace (E7Matrix Γ * permMatrix σ) =
      ((adjacentMovedCount Γ σ : ℚ) + 8 * (fixedVertexCount σ : ℚ)) / 15
        - (Fintype.card V : ℚ) / 750 := by
  classical
  simp [E7Matrix, Matrix.sub_mul, Matrix.add_mul,
    trace_adjMatrix_mul_permMatrix_eq_adjacentMovedCount,
    trace_permMatrix_eq_fixedVertexCount, trace_allOnes_mul_permMatrix]
  ring

/-- Moore57 用の Higman 型跡公式:
`trace (E₇ P_σ) = (8 a₀(σ) + a₁(σ) - 65) / 15`. -/
theorem IsMoore57.higman_trace_formula
    {Γ : SimpleGraph V} [DecidableRel Γ.Adj] (hΓ : IsMoore57 Γ) (σ : Equiv.Perm V) :
    Matrix.trace (E7Matrix Γ * permMatrix σ) =
      (8 * (fixedVertexCount σ : ℚ) + (adjacentMovedCount Γ σ : ℚ) - 65) / 15 := by
  rw [Moore57.trace_E7Matrix_mul_permMatrix, hΓ.card]
  ring

/-- 非自明回転で `a₀ = 1` が分かっており, さらに表現論側から
`trace (E₇ P_σ) = α + β - γ` が分かれば, 旧 `rotation_trace` フィールドの
整数等式は Higman 跡公式から導ける. -/
theorem rotation_trace_eq_of_higman_character
    {Γ : SimpleGraph V} [DecidableRel Γ.Adj] (hΓ : IsMoore57 Γ) (σ : Equiv.Perm V)
    {alpha beta gamma a1 : ℕ}
    (ha0 : fixedVertexCount σ = 1)
    (ha1 : adjacentMovedCount Γ σ = a1)
    (hchar : Matrix.trace (E7Matrix Γ * permMatrix σ) =
      (alpha : ℚ) + (beta : ℚ) - (gamma : ℚ)) :
    (a1 : ℤ) - 57 =
      15 * ((alpha : ℤ) + (beta : ℤ) - (gamma : ℤ)) := by
  have hq :
      ((a1 : ℚ) - 57) / 15 =
        (alpha : ℚ) + (beta : ℚ) - (gamma : ℚ) := by
    rw [← hchar, hΓ.higman_trace_formula σ, ha0, ha1]
    ring
  have hq' :
      (a1 : ℚ) - 57 =
        15 * ((alpha : ℚ) + (beta : ℚ) - (gamma : ℚ)) := by
    calc
      (a1 : ℚ) - 57 = 15 * (((a1 : ℚ) - 57) / 15) := by ring
      _ = 15 * ((alpha : ℚ) + (beta : ℚ) - (gamma : ℚ)) := by rw [hq]
  apply (Int.cast_injective (α := ℚ))
  norm_num
  exact hq'

end HigmanTrace

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

/-! ### $D_{19}$ の小さな指標値関数

ここでは mathlib の重い表現論 API に入らず, 自然言語証明で使う三つの有理既約指標
`1`, `ε`, `ρ` の値だけを class-function 風の関数として置く. -/

/-- $D_{19}$ の自明指標. -/
def d19TrivCharacter (_g : DihedralGroup 19) : ℤ :=
  1

/-- $D_{19}$ の符号指標. 回転で `1`, 反射で `-1`. -/
def d19SignCharacter : DihedralGroup 19 → ℤ
  | DihedralGroup.r _ => 1
  | DihedralGroup.sr _ => -1

/-- $D_{19}$ の 18 次元有理既約指標.

値は `ρ(1)=18`, 非自明回転で `-1`, 反射で `0`. -/
def d19RhoCharacter : DihedralGroup 19 → ℤ
  | DihedralGroup.r d => if d = 0 then 18 else -1
  | DihedralGroup.sr _ => 0

/-- `α⋅1 + β⋅ε + γ⋅ρ` の指標値関数. -/
def d19LinearCharacter (alpha beta gamma : ℕ) (g : DihedralGroup 19) : ℤ :=
  (alpha : ℤ) * d19TrivCharacter g
    + (beta : ℤ) * d19SignCharacter g
    + (gamma : ℤ) * d19RhoCharacter g

@[simp] theorem d19TrivCharacter_apply (g : DihedralGroup 19) :
    d19TrivCharacter g = 1 :=
  rfl

@[simp] theorem d19SignCharacter_rotation (d : ZMod 19) :
    d19SignCharacter (DihedralGroup.r d) = 1 :=
  rfl

@[simp] theorem d19SignCharacter_reflection (d : ZMod 19) :
    d19SignCharacter (DihedralGroup.sr d) = -1 :=
  rfl

@[simp] theorem d19RhoCharacter_one :
    d19RhoCharacter (DihedralGroup.r (0 : ZMod 19)) = 18 := by
  simp [d19RhoCharacter]

@[simp] theorem d19RhoCharacter_rotation_ne {d : ZMod 19} (hd : d ≠ 0) :
    d19RhoCharacter (DihedralGroup.r d) = -1 := by
  simp [d19RhoCharacter, hd]

@[simp] theorem d19RhoCharacter_reflection (d : ZMod 19) :
    d19RhoCharacter (DihedralGroup.sr d) = 0 :=
  rfl

/-- 線形結合指標の単位元での値. -/
theorem d19LinearCharacter_one (alpha beta gamma : ℕ) :
    d19LinearCharacter alpha beta gamma (1 : DihedralGroup 19) =
      (alpha : ℤ) + (beta : ℤ) + 18 * (gamma : ℤ) := by
  change d19LinearCharacter alpha beta gamma (DihedralGroup.r (0 : ZMod 19)) =
    (alpha : ℤ) + (beta : ℤ) + 18 * (gamma : ℤ)
  simp only [d19LinearCharacter, d19TrivCharacter_apply,
    d19SignCharacter_rotation, d19RhoCharacter_one]
  ring_nf

/-- 線形結合指標の反射での値. -/
theorem d19LinearCharacter_reflection (alpha beta gamma : ℕ) (d : ZMod 19) :
    d19LinearCharacter alpha beta gamma (DihedralGroup.sr d) =
      (alpha : ℤ) - (beta : ℤ) := by
  simp [d19LinearCharacter]
  ring_nf

/-- 線形結合指標の非自明回転での値. -/
theorem d19LinearCharacter_rotation_ne
    (alpha beta gamma : ℕ) {d : ZMod 19} (hd : d ≠ 0) :
    d19LinearCharacter alpha beta gamma (DihedralGroup.r d) =
      (alpha : ℤ) + (beta : ℤ) - (gamma : ℤ) := by
  simp [d19LinearCharacter, d19RhoCharacter_rotation_ne hd]
  ring_nf

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

/-- 具体軌道データからの矛盾. Section 5 の上界と Section 6 の計数を組み合わせる. -/
theorem contradiction (hΓ : IsMoore57 Γ) (h : D19ConcreteHypotheses Γ) : False :=
  counting_contradiction_zmod h.D (fun q => h.D_zero q) (h.Dq_le_two hΓ) (h.Nd_lower hΓ)

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

/-- 単位元の作用同値は恒等置換である. -/
@[simp] theorem smulEquiv_one (h : D19ActsOnMoore57 V Γ) :
    h.smulEquiv 1 = 1 := by
  ext v
  change h.smul 1 v = v
  exact h.one_smul v

/-- `smulEquiv` は積を置換の積に送る. -/
theorem smulEquiv_mul (h : D19ActsOnMoore57 V Γ) (g g' : DihedralGroup 19) :
    h.smulEquiv (g * g') = h.smulEquiv g * h.smulEquiv g' := by
  ext v
  change h.smul (g * g') v = h.smul g (h.smul g' v)
  exact h.mul_smul g g' v

/-- `smulEquiv` は冪と整合する. -/
theorem smulEquiv_pow (h : D19ActsOnMoore57 V Γ) (g : DihedralGroup 19) (n : ℕ) :
    h.smulEquiv (g ^ n) = h.smulEquiv g ^ n := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      rw [pow_succ, pow_succ, h.smulEquiv_mul, ih]

/-- 隣接保存性から, 各群元はグラフ自己同型を与える. -/
noncomputable def smulIso (h : D19ActsOnMoore57 V Γ) (g : DihedralGroup 19) : Γ ≃g Γ where
  toEquiv := h.smulEquiv g
  map_rel_iff' := by
    intro v w
    exact (h.smul_adj g v w).symm

/-- 作用から得られる回転 `r^d` の頂点置換. -/
noncomputable def rotation (h : D19ActsOnMoore57 V Γ) (d : ZMod 19) : Equiv.Perm V :=
  h.smulEquiv (DihedralGroup.r d)

/-- 作用から定まる非自明回転用の `a₁` 関数. -/
noncomputable def a1 (h : D19ActsOnMoore57 V Γ) (d : ZMod 19) : ℕ :=
  adjacentMovedCount Γ (h.rotation d)

/-- 零回転は恒等置換である. -/
@[simp] theorem rotation_zero (h : D19ActsOnMoore57 V Γ) :
    h.rotation 0 = 1 := by
  ext v
  change h.smul (DihedralGroup.r (0 : ZMod 19)) v = v
  simpa [DihedralGroup.r_zero] using h.one_smul v

/-- 回転の加法は置換の積に対応する. -/
theorem rotation_add (h : D19ActsOnMoore57 V Γ) (d e : ZMod 19) :
    h.rotation (d + e) = h.rotation d * h.rotation e := by
  ext v
  change h.smul (DihedralGroup.r (d + e)) v =
    h.smul (DihedralGroup.r d) (h.smul (DihedralGroup.r e) v)
  rw [← DihedralGroup.r_mul_r d e, h.mul_smul]

/-- 任意の回転置換の 19 乗は恒等置換である. -/
theorem rotation_pow_nineteen (h : D19ActsOnMoore57 V Γ) (d : ZMod 19) :
    h.rotation d ^ 19 = 1 := by
  change h.smulEquiv (DihedralGroup.r d) ^ 19 = 1
  rw [← h.smulEquiv_pow (DihedralGroup.r d) 19]
  rw [DihedralGroup.r_pow]
  have h19 : ((19 : ℕ) : ZMod 19) = 0 := ZMod.natCast_self 19
  rw [h19, mul_zero, DihedralGroup.r_zero, h.smulEquiv_one]

/-- 忠実性より, 非零回転は頂点上の恒等置換として作用しない. -/
theorem rotation_ne_one (h : D19ActsOnMoore57 V Γ) {d : ZMod 19} (hd : d ≠ 0) :
    h.rotation d ≠ 1 := by
  intro hrot
  have hgroup : DihedralGroup.r d = (1 : DihedralGroup 19) := by
    apply h.faithful (DihedralGroup.r d) 1
    intro v
    have hv : h.smul (DihedralGroup.r d) v = v := by
      have hv' : h.rotation d v = (1 : Equiv.Perm V) v := by
        simp [hrot]
      simpa [rotation] using hv'
    simpa [h.one_smul] using hv
  have hd0 : d = 0 := by
    have hgroup' : DihedralGroup.r d = DihedralGroup.r (0 : ZMod 19) := by
      simpa [DihedralGroup.r_zero] using hgroup
    exact DihedralGroup.r.inj hgroup'
  exact hd hd0

/-- 回転の固定点数は `support` の補集合の濃度としても書ける. -/
theorem fixedVertexCount_eq_support_compl_card (σ : Equiv.Perm V) :
    fixedVertexCount σ = σ.supportᶜ.card := by
  classical
  simp [fixedVertexCount, Equiv.Perm.support]

/-- 19 乗が恒等になることから, 回転の固定点数は全頂点数と mod 19 で一致する. -/
theorem fixedVertexCount_rotation_modEq_card
    (h : D19ActsOnMoore57 V Γ) (d : ZMod 19) :
    Fintype.card V ≡ fixedVertexCount (h.rotation d) [MOD 19] := by
  classical
  haveI : Fact (Nat.Prime 19) := ⟨by decide⟩
  have hpow : h.rotation d ^ 19 ^ 1 = 1 := by
    simpa using h.rotation_pow_nineteen d
  have hmod := Equiv.Perm.card_compl_support_modEq
    (α := V) (p := 19) (n := 1) (σ := h.rotation d) hpow
  simpa [fixedVertexCount_eq_support_compl_card] using hmod.symm

/-- Moore57 の頂点数を使うと, 回転の固定点数は `1 mod 19`. -/
theorem fixedVertexCount_rotation_modEq_one
    (h : D19ActsOnMoore57 V Γ) (d : ZMod 19) :
    fixedVertexCount (h.rotation d) ≡ 1 [MOD 19] := by
  have hmod := h.fixedVertexCount_rotation_modEq_card d
  have hcard : Fintype.card V ≡ 1 [MOD 19] := by
    rw [h.card_vertices]
    norm_num [Nat.ModEq]
  exact hmod.symm.trans hcard

/-- 非零性を使わなくても, 各回転は少なくとも 1 個の固定点を持つ. -/
theorem fixedVertexCount_rotation_pos
    (h : D19ActsOnMoore57 V Γ) (d : ZMod 19) :
    0 < fixedVertexCount (h.rotation d) := by
  by_contra hpos
  have hzero : fixedVertexCount (h.rotation d) = 0 := Nat.eq_zero_of_not_pos hpos
  have hmod := h.fixedVertexCount_rotation_modEq_one d
  rw [hzero] at hmod
  norm_num [Nat.ModEq] at hmod

/-- 非零回転が全頂点を固定することはない. -/
theorem fixedVertexCount_rotation_lt_card
    (h : D19ActsOnMoore57 V Γ) {d : ZMod 19} (hd : d ≠ 0) :
    fixedVertexCount (h.rotation d) < Fintype.card V := by
  classical
  have hle :
      fixedVertexCount (h.rotation d) ≤ Fintype.card V := by
    simpa [fixedVertexCount] using
      (Finset.card_filter_le (Finset.univ : Finset V)
        (fun v => h.rotation d v = v))
  exact lt_of_le_of_ne hle (by
    intro hcard
    apply h.rotation_ne_one hd
    ext v
    have hall :
        ∀ x ∈ (Finset.univ : Finset V), h.rotation d x = x := by
      exact (Finset.card_filter_eq_iff
        (s := (Finset.univ : Finset V))
        (p := fun x => h.rotation d x = x)).1
          (by simpa [fixedVertexCount] using hcard)
    exact hall v (Finset.mem_univ v))

end D19ActsOnMoore57

/-- 具体軌道データつきの主矛盾.

未形式化の Sections 1–4 を隠さず, そこから構成されるべき
`D19ConcreteHypotheses` を明示引数として受け取る形にしている. -/
theorem no_D19_acts_on_Moore57
    {V : Type*} [Fintype V] [DecidableEq V]
    {Γ : SimpleGraph V} [DecidableRel Γ.Adj]
    (h : D19ActsOnMoore57 V Γ) (hyp : D19ConcreteHypotheses Γ) : False :=
  hyp.contradiction h.isMoore

/-- **系 6.2**: $\operatorname{Aut}(\Gamma)\simeq D_{19}$ は不可能.

具体軌道データが得られている場合の条件付き版. -/
theorem no_aut_iso_D19
    {V : Type*} [Fintype V] [DecidableEq V]
    {Γ : SimpleGraph V} [DecidableRel Γ.Adj]
    (h : D19ActsOnMoore57 V Γ) (hyp : D19ConcreteHypotheses Γ) : False :=
  no_D19_acts_on_Moore57 h hyp

end Moore57
