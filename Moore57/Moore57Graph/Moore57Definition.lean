import Mathlib.Combinatorics.SimpleGraph.StronglyRegular
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Data.Matrix.PEquiv
import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Moore57.Foundations.GroupAction.FixedPoints
import Moore57.Foundations.GraphTheory.AdjacentMovedCount

/-!
# Moore graph of degree 57: core definitions and SRG facts (Tier 2)

This file extracts the D₁₉-action-independent content from the original
`D19Contradiction.lean`:

* `IsMoore57` — Moore graph of degree 57 abbreviation.
* Basic SRG facts: `no_triangle`, `no_four_cycle`, branch-fiber lemmas.
* Matrix definitions: `allOnesMatrix`, `permMatrix`, `E7Matrix`.
* Higman trace formula for Moore57.

Nothing here references `D19ActsOnMoore57`.
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

/-! ### Section 2: 固定点まわりの枝と fiber -/

/-- 中心 `u` の隣接頂点 `b` に対応する fiber.

自然言語証明の `L_b` に対応し, `b` の近傍から中心 `u` を除いた有限集合である.
`u ~ b` のとき, 三角形禁止により各元は自動的に `u` と非隣接になる. -/
def branchFiber {V : Type*} [Fintype V] [DecidableEq V]
    (Γ : SimpleGraph V) [DecidableRel Γ.Adj] (u b : V) : Finset V :=
  (Γ.neighborFinset b).erase u

@[simp] theorem mem_branchFiber {V : Type*} [Fintype V] [DecidableEq V]
    {Γ : SimpleGraph V} [DecidableRel Γ.Adj] {u b x : V} :
    x ∈ branchFiber Γ u b ↔ x ≠ u ∧ Γ.Adj b x := by
  rw [branchFiber, Finset.mem_erase, SimpleGraph.mem_neighborFinset]

namespace IsMoore57

/-- Moore57 では各枝 fiber のサイズは `56`. -/
theorem branchFiber_card {V : Type*} [Fintype V] [DecidableEq V]
    {Γ : SimpleGraph V} [DecidableRel Γ.Adj]
    (hΓ : IsMoore57 Γ) {u b : V} (hub : Γ.Adj u b) :
    (branchFiber Γ u b).card = 56 := by
  rw [branchFiber, Finset.card_erase_of_mem]
  · rw [SimpleGraph.card_neighborFinset_eq_degree, hΓ.regular.degree_eq b]
  · simpa [SimpleGraph.mem_neighborFinset] using hub.symm

/-- 枝 fiber の元は中心 `u` とは隣接しない. -/
theorem not_adj_center_of_mem_branchFiber {V : Type*} [Fintype V] [DecidableEq V]
    {Γ : SimpleGraph V} [DecidableRel Γ.Adj]
    (hΓ : IsMoore57 Γ) {u b x : V} (hub : Γ.Adj u b)
    (hx : x ∈ branchFiber Γ u b) :
    ¬ Γ.Adj u x := by
  intro hux
  exact hΓ.no_triangle hub (mem_branchFiber.mp hx).2 hux.symm

/-- 中心 `u` の相異なる二つの枝は互いに隣接しない. -/
theorem not_adj_of_center_neighbors {V : Type*} [Fintype V] [DecidableEq V]
    {Γ : SimpleGraph V} [DecidableRel Γ.Adj]
    (hΓ : IsMoore57 Γ) {u b c : V}
    (hub : Γ.Adj u b) (huc : Γ.Adj u c) (_hbc : b ≠ c) :
    ¬ Γ.Adj b c := by
  intro hbcAdj
  exact hΓ.no_triangle hub hbcAdj huc.symm

/-- 中心 `u` と非隣接な頂点は, 一意の枝 fiber に属する. -/
theorem existsUnique_branch_of_not_adj_center
    {V : Type*} [Fintype V] [DecidableEq V]
    {Γ : SimpleGraph V} [DecidableRel Γ.Adj]
    (hΓ : IsMoore57 Γ) {u x : V}
    (hux : u ≠ x) (hnot : ¬ Γ.Adj u x) :
    ∃! b : V, Γ.Adj u b ∧ x ∈ branchFiber Γ u b := by
  have hcard : Fintype.card (Γ.commonNeighbors u x) = 1 :=
    hΓ.of_not_adj hux hnot
  rcases Fintype.card_eq_one_iff.mp hcard with ⟨b, hb_unique⟩
  have hb_mem : (b : V) ∈ Γ.commonNeighbors u x := b.property
  have hb_adj : Γ.Adj u (b : V) ∧ Γ.Adj x (b : V) := by
    rw [SimpleGraph.mem_commonNeighbors] at hb_mem
    exact hb_mem
  refine ⟨b, ?_, ?_⟩
  · refine ⟨hb_adj.1, ?_⟩
    rw [mem_branchFiber]
    exact ⟨hux.symm, hb_adj.2.symm⟩
  · intro y hy
    have hy_mem : y ∈ Γ.commonNeighbors u x := by
      rw [SimpleGraph.mem_commonNeighbors]
      exact ⟨hy.1, (mem_branchFiber.mp hy.2).2.symm⟩
    exact congrArg Subtype.val (hb_unique ⟨y, hy_mem⟩)

/-- `L_b` の点は, 別の枝 `c` とは隣接しない. -/
theorem not_adj_other_branch_of_mem_branchFiber
    {V : Type*} [Fintype V] [DecidableEq V]
    {Γ : SimpleGraph V} [DecidableRel Γ.Adj]
    (hΓ : IsMoore57 Γ) {u b c x : V}
    (hub : Γ.Adj u b) (huc : Γ.Adj u c) (hbc : b ≠ c)
    (hx : x ∈ branchFiber Γ u b) :
    ¬ Γ.Adj x c := by
  intro hxc
  have hx_not_adj_u : ¬ Γ.Adj u x :=
    hΓ.not_adj_center_of_mem_branchFiber hub hx
  have hcard : Fintype.card (Γ.commonNeighbors u x) = 1 :=
    hΓ.of_not_adj (mem_branchFiber.mp hx).1.symm hx_not_adj_u
  have hpair_subset : ({b, c} : Finset V) ⊆ (Γ.commonNeighbors u x).toFinset := by
    intro y hy
    rw [Set.mem_toFinset]
    rw [SimpleGraph.mem_commonNeighbors]
    rw [Finset.mem_insert, Finset.mem_singleton] at hy
    rcases hy with rfl | rfl
    · exact ⟨hub, (mem_branchFiber.mp hx).2.symm⟩
    · exact ⟨huc, hxc⟩
  have htwo : 2 ≤ Fintype.card (Γ.commonNeighbors u x) := by
    rw [← Set.toFinset_card]
    have hcardpair : ({b, c} : Finset V).card = 2 := by
      simp [hbc]
    exact hcardpair ▸ Finset.card_le_card hpair_subset
  omega

/-- 異なる枝の fiber 間では, 片側の各点に対して反対側の隣接点が一意に存在する.

これは自然言語証明の「異なる fiber 間には完全マッチングが入る」の片方向版である.
逆方向は `b` と `c` を入れ替えることで得られる. -/
theorem existsUnique_adjacent_in_branchFiber
    {V : Type*} [Fintype V] [DecidableEq V]
    {Γ : SimpleGraph V} [DecidableRel Γ.Adj]
    (hΓ : IsMoore57 Γ) {u b c x : V}
    (hub : Γ.Adj u b) (huc : Γ.Adj u c) (hbc : b ≠ c)
    (hx : x ∈ branchFiber Γ u b) :
    ∃! y : V, y ∈ branchFiber Γ u c ∧ Γ.Adj x y := by
  have hxc_not_adj : ¬ Γ.Adj x c :=
    hΓ.not_adj_other_branch_of_mem_branchFiber hub huc hbc hx
  have hxc_ne : x ≠ c := by
    intro hxc_eq
    exact hΓ.not_adj_of_center_neighbors hub huc hbc
      (by simpa [hxc_eq] using (mem_branchFiber.mp hx).2)
  have hcard : Fintype.card (Γ.commonNeighbors x c) = 1 :=
    hΓ.of_not_adj hxc_ne hxc_not_adj
  rcases Fintype.card_eq_one_iff.mp hcard with ⟨w, hw_unique⟩
  have hw_mem : (w : V) ∈ Γ.commonNeighbors x c := w.property
  have hw_adj : Γ.Adj x (w : V) ∧ Γ.Adj c (w : V) := by
    rw [SimpleGraph.mem_commonNeighbors] at hw_mem
    exact hw_mem
  refine ⟨w, ?_, ?_⟩
  · refine ⟨?_, hw_adj.1⟩
    rw [mem_branchFiber]
    refine ⟨?_, hw_adj.2⟩
    intro hwu
    have hux : Γ.Adj u x := by
      simpa [hwu] using hw_adj.1.symm
    exact hΓ.not_adj_center_of_mem_branchFiber hub hx hux
  · intro y hy
    have hy_mem : y ∈ Γ.commonNeighbors x c := by
      rw [SimpleGraph.mem_commonNeighbors]
      exact ⟨hy.2, (mem_branchFiber.mp hy.1).2⟩
    exact congrArg Subtype.val (hw_unique ⟨y, hy_mem⟩)

/-- 異なる枝の fiber 間では, 右側の各点に対して左側の隣接点も一意に存在する. -/
theorem existsUnique_adjacent_in_branchFiber_left
    {V : Type*} [Fintype V] [DecidableEq V]
    {Γ : SimpleGraph V} [DecidableRel Γ.Adj]
    (hΓ : IsMoore57 Γ) {u b c y : V}
    (hub : Γ.Adj u b) (huc : Γ.Adj u c) (hbc : b ≠ c)
    (hy : y ∈ branchFiber Γ u c) :
    ∃! x : V, x ∈ branchFiber Γ u b ∧ Γ.Adj x y := by
  rcases hΓ.existsUnique_adjacent_in_branchFiber huc hub hbc.symm hy with ⟨x, hx, huniq⟩
  refine ⟨x, ⟨hx.1, hx.2.symm⟩, ?_⟩
  intro z hz
  exact huniq z ⟨hz.1, hz.2.symm⟩

/-- 異なる枝の fiber 間の完全マッチングを, 両側の一意性としてまとめた形. -/
theorem existsUnique_adjacent_between_branchFibers
    {V : Type*} [Fintype V] [DecidableEq V]
    {Γ : SimpleGraph V} [DecidableRel Γ.Adj]
    (hΓ : IsMoore57 Γ) {u b c : V}
    (hub : Γ.Adj u b) (huc : Γ.Adj u c) (hbc : b ≠ c) :
    (∀ x : V, x ∈ branchFiber Γ u b →
      ∃! y : V, y ∈ branchFiber Γ u c ∧ Γ.Adj x y) ∧
    (∀ y : V, y ∈ branchFiber Γ u c →
      ∃! x : V, x ∈ branchFiber Γ u b ∧ Γ.Adj x y) := by
  exact ⟨
    fun x hx => hΓ.existsUnique_adjacent_in_branchFiber hub huc hbc hx,
    fun y hy => hΓ.existsUnique_adjacent_in_branchFiber_left hub huc hbc hy⟩

/-- 固定した左側の点に隣接する右側 fiber の点は高々一つ. -/
theorem eq_of_mem_branchFiber_of_adj
    {V : Type*} [Fintype V] [DecidableEq V]
    {Γ : SimpleGraph V} [DecidableRel Γ.Adj]
    (hΓ : IsMoore57 Γ) {u b c x y z : V}
    (hub : Γ.Adj u b) (huc : Γ.Adj u c) (hbc : b ≠ c)
    (hx : x ∈ branchFiber Γ u b)
    (hy : y ∈ branchFiber Γ u c) (hz : z ∈ branchFiber Γ u c)
    (hxy : Γ.Adj x y) (hxz : Γ.Adj x z) :
    y = z := by
  rcases hΓ.existsUnique_adjacent_in_branchFiber hub huc hbc hx with ⟨w, _hw, huniq⟩
  exact (huniq y ⟨hy, hxy⟩).trans (huniq z ⟨hz, hxz⟩).symm

/-- 固定した右側の点に隣接する左側 fiber の点は高々一つ. -/
theorem eq_of_mem_branchFiber_of_adj_left
    {V : Type*} [Fintype V] [DecidableEq V]
    {Γ : SimpleGraph V} [DecidableRel Γ.Adj]
    (hΓ : IsMoore57 Γ) {u b c x z y : V}
    (hub : Γ.Adj u b) (huc : Γ.Adj u c) (hbc : b ≠ c)
    (hx : x ∈ branchFiber Γ u b) (hz : z ∈ branchFiber Γ u b)
    (hy : y ∈ branchFiber Γ u c)
    (hxy : Γ.Adj x y) (hzy : Γ.Adj z y) :
    x = z := by
  rcases hΓ.existsUnique_adjacent_in_branchFiber_left hub huc hbc hy with ⟨w, _hw, huniq⟩
  exact (huniq x ⟨hx, hxy⟩).trans (huniq z ⟨hz, hzy⟩).symm

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

end Moore57
