import Mathlib.GroupTheory.SpecificGroups.Dihedral
import Moore57.Moore57Graph.Moore57Definition
import Moore57.Foundations.GraphTheory.AdjacentMovedCount
import Moore57.Foundations.GroupAction.FixedPoints

/-!
# D₁₉ action structure on Moore57 graphs (Tier 3)

This file extracts the `D19ActsOnMoore57` structure from the original
`D19Contradiction.lean`:

* `D19ActsOnMoore57` — Moore graph of degree 57 with a faithful D₁₉ action.
* `rotation`, `a1`, `smulEquiv`, `smulIso` — derived action data.
* Basic action lemmas.
-/

open Finset SimpleGraph

namespace Moore57

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

end Moore57
