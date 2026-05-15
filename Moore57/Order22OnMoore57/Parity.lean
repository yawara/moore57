import Moore57.Order22OnMoore57.BasicStructure
import Moore57.Order22OnMoore57.TraceNumber
import Moore57.Order22OnMoore57.TraceConstancy

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

/-! ### Cyclic case helpers -/

/-- σ と τ が可換なとき, σ は τ の固定点を τ の固定点に送る. -/
theorem σ_τ_fixed_of_τ_fixed (hcomm : h.σ * h.τ = h.τ * h.σ)
    {x : V} (hx : h.τ x = x) : h.τ (h.σ x) = h.σ x := by
  have hcomm_x : (h.σ * h.τ) x = (h.τ * h.σ) x := by rw [hcomm]
  simp only [Equiv.Perm.mul_apply, hx] at hcomm_x
  exact hcomm_x.symm

/-- 循環 case (στ = τσ) では σ は star の中心を固定する.

degree 論証: σ(center) = leaf j と仮定すると, 各 leaf i について
σ(leaf i) ∈ Fix(τ) かつ σ(leaf i) は σ(center) = leaf j と隣接.
no_leaf_leaf より σ(leaf i) = center. しかし σ 単射ゆえ 55 個全部
center に送るのは不可能. -/
theorem cyclic_σ_center_eq_center (hcomm : h.σ * h.τ = h.τ * h.σ) :
    h.σ h.τ_fix.center = h.τ_fix.center := by
  have hσcen_fix : h.τ (h.σ h.τ_fix.center) = h.σ h.τ_fix.center :=
    h.σ_τ_fixed_of_τ_fixed hcomm h.τ_fix.center_fixed
  rcases h.τ_fix.span _ hσcen_fix with h_cen | ⟨j, h_leaf⟩
  · exact h_cen
  · exfalso
    -- 各 leaf i について σ(leaf i) = center
    have key : ∀ i : Fin 55, h.σ (h.τ_fix.leaf i) = h.τ_fix.center := by
      intro i
      have hτ_fix_σi : h.τ (h.σ (h.τ_fix.leaf i)) = h.σ (h.τ_fix.leaf i) :=
        h.σ_τ_fixed_of_τ_fixed hcomm (h.τ_fix.leaf_fixed i)
      have hadj_i : Γ.Adj (h.τ_fix.leaf j) (h.σ (h.τ_fix.leaf i)) := by
        have := (h.σ_aut h.τ_fix.center (h.τ_fix.leaf i)).mp (h.τ_fix.adj_center i)
        rw [h_leaf] at this
        exact this
      rcases h.τ_fix.span _ hτ_fix_σi with h_cen' | ⟨k, h_leaf_k⟩
      · exact h_cen'
      · exfalso; rw [h_leaf_k] at hadj_i
        exact h.τ_fix.no_leaf_leaf j k hadj_i
    -- σ inj 矛盾: σ(leaf 0) = σ(leaf 1) = center だが leaf 0 ≠ leaf 1
    have h01 : h.σ (h.τ_fix.leaf 0) = h.σ (h.τ_fix.leaf 1) := by
      rw [key 0, key 1]
    have h_leaf_eq : h.τ_fix.leaf 0 = h.τ_fix.leaf 1 := h.σ.injective h01
    have h_fin_eq : (0 : Fin 55) = 1 := h.τ_fix.leaf_injective h_leaf_eq
    exact absurd h_fin_eq (by decide)

/-- 循環 case: y ∈ Fix(τ) かつ y ~ σ y は矛盾. -/
theorem cyclic_no_τ_fixed_adj_σ (hcomm : h.σ * h.τ = h.τ * h.σ)
    {y : V} (hy_τ : h.τ y = y) (hy_adj : Γ.Adj y (h.σ y)) : False := by
  rcases h.τ_fix.span y hy_τ with hy_cen | ⟨i, hy_leaf⟩
  · -- y = center. σ y = σ center = center. y ~ y loopless 矛盾.
    have hσy : h.σ y = y := by
      rw [hy_cen]; exact h.cyclic_σ_center_eq_center hcomm
    rw [hσy] at hy_adj
    exact SimpleGraph.irrefl Γ hy_adj
  · -- y = leaf i. σ y ∈ Fix(τ).
    have hσy_fix : h.τ (h.σ y) = h.σ y := h.σ_τ_fixed_of_τ_fixed hcomm hy_τ
    rcases h.τ_fix.span _ hσy_fix with hσy_cen | ⟨k, hσy_leaf⟩
    · -- σ y = center. σ(leaf i) = center だが σ(center) = center, σ inj で leaf i = center 矛盾.
      have h_cen_fix : h.σ h.τ_fix.center = h.τ_fix.center :=
        h.cyclic_σ_center_eq_center hcomm
      have hσy_eq : h.σ y = h.σ h.τ_fix.center := by
        rw [hσy_cen]; exact h_cen_fix.symm
      have h_eq : y = h.τ_fix.center := h.σ.injective hσy_eq
      rw [hy_leaf] at h_eq
      exact h.τ_fix.center_ne_leaf i h_eq.symm
    · -- σ y = leaf k. leaf i ~ leaf k 矛盾 (no_leaf_leaf).
      rw [hy_leaf] at hy_adj hσy_leaf
      rw [hσy_leaf] at hy_adj
      exact h.τ_fix.no_leaf_leaf i k hy_adj

/-- **Phase 5.1 主結論**: cyclic case で n は偶数.

|S| = 11n (S = {x : x ~ σ x}). τ は S を保つ involution.
S の τ-不動点は `cyclic_no_τ_fixed_adj_σ` により無し.
よって `Equiv.Perm.card_compl_support_modEq` (p=2) で |S| ≡ 0 (mod 2).
11 が奇なので n も偶. -/
theorem traceNumber_even_of_cyclic (hcomm : h.σ * h.τ = h.τ * h.σ) :
    Even h.traceNumber := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨by decide⟩
  -- |S| = 11 * n
  have hTk1 : h.Tk 1 = 11 * h.traceNumber := h.Tk_one_eq_eleven_mul_traceNumber
  -- τ は S を保つ
  let p : V → Prop := fun x => Γ.Adj x (h.σ x)
  have hτ_iff : ∀ x : V, p (h.τ x) ↔ p x := fun x => by
    show Γ.Adj (h.τ x) (h.σ (h.τ x)) ↔ Γ.Adj x (h.σ x)
    have hcomm_x : h.σ (h.τ x) = h.τ (h.σ x) := by
      have := congrArg (· x) hcomm
      simpa [Equiv.Perm.mul_apply] using this
    rw [hcomm_x]
    exact (h.τ_aut x (h.σ x)).symm
  let τS : Equiv.Perm (Subtype p) := h.τ.subtypePerm hτ_iff
  have hτS_pow : τS ^ 2 ^ 1 = 1 := by
    ext ⟨w, _⟩
    show (h.τ ^ 2) w = w
    rw [h.τ_pow_two]; rfl
  have hmod := Equiv.Perm.card_compl_support_modEq
    (α := Subtype p) (p := 2) (n := 1) (σ := τS) hτS_pow
  -- S 上 τS の不動点なし
  have hfix_empty : τS.supportᶜ.card = 0 := by
    rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
    rintro ⟨w, hwp⟩ hw
    rw [Finset.mem_compl, Equiv.Perm.mem_support] at hw
    push_neg at hw
    have hwfix_τ : h.τ w = w := congrArg Subtype.val hw
    have hw_adj : Γ.Adj w (h.σ w) := hwp
    exact h.cyclic_no_τ_fixed_adj_σ hcomm hwfix_τ hw_adj
  rw [hfix_empty] at hmod
  -- |Subtype p| = Tk 1
  have hcard : Fintype.card (Subtype p) = h.Tk 1 := by
    show Fintype.card {x : V // Γ.Adj x (h.σ x)} = h.Tk 1
    rw [Fintype.card_subtype]
    show (Finset.univ.filter fun x : V => Γ.Adj x (h.σ x)).card =
      (Finset.univ.filter fun x : V => Γ.Adj x ((h.σ ^ 1) x)).card
    simp [pow_one]
  rw [hcard] at hmod
  -- hmod : 0 ≡ Tk 1 [MOD 2], すなわち Tk 1 % 2 = 0
  have hTk1_even : h.Tk 1 % 2 = 0 := by
    have : (0 : ℕ) % 2 = h.Tk 1 % 2 := hmod
    omega
  -- traceNumber は Tk 1 / 11 で, Tk 1 = 11 * n, 11 odd, 11n even ⟹ n even
  have hmul_even : (11 * h.traceNumber) % 2 = 0 := by
    rw [← hTk1]; exact hTk1_even
  have hn_even : h.traceNumber % 2 = 0 := by omega
  exact ⟨h.traceNumber / 2, by omega⟩

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
