import Moore57.Order22OnMoore57.BasicStructure
import Moore57.Foundations.GroupAction.InvolutionParity

/-!
# Step 1 (Dihedral): τ|Fix(σ) は反射 (C_5 の 1 反射点)

dihedral case (`τστ = σ⁻¹`) において,
* τ は Fix(σ) = C_5 を保つ (`τ_preserves_σ_fix`).
* τ は involution.
* C_5 上の τ は graph automorphism = D_5 の元.
* 5 個の頂点に対する involution → 不動点数 ∈ {1, 3, 5}.
* case 3 排除 → cycle-edge 破壊 (D_5 involution は反射のみ).
* case 5 排除 → C_5 ⊂ Fix(τ) = K_{1,55} の中に 5-cycle が入る矛盾.
* 結論: τ の C_5 上の不動点は丁度 1 個 `u_τ`.

派生定数:
* `u_τ` : 唯一の τ-不動点 (∈ Fix(σ)).
* `a_τ = next(u_τ)`, `d_τ = prev(u_τ)` : τ で swap される cycle 隣接.
* `b_τ = next^2(u_τ)`, `c_τ = prev^2(u_τ)` : τ で swap される.

これらを scaffold (sorry あり) として提供し, 後続ファイル
(`DihedralCenterInNeighborhood.lean` 以降) に API を露出する.
-/

namespace Moore57

namespace Order22ActsOnMoore57

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]
variable (h : Order22ActsOnMoore57 V Γ)

/-! ## Helper: Fin 5 上の cycle-aut involution の分類 -/

/-- 任意の Fin 5 上 involution + cycle-preserving 函数は,
identity か unique-fixed-point の反射のいずれか. -/
theorem Fin5_cycle_involution_classify
    (f : Fin 5 → Fin 5) (hinv : ∀ x, f (f x) = x)
    (hcycle : ∀ i, f (i + 1) = f i + 1 ∨ f (i + 1) = f i - 1) :
    (∀ i, f i = i) ∨
    (∃ idx : Fin 5,
      (∀ j, f j = j ↔ j = idx) ∧
      f (idx + 1) = idx + 4 ∧
      f (idx + 2) = idx + 3 ∧
      f (idx + 4) = idx + 1 ∧
      f (idx + 3) = idx + 2) := by
  -- 5 元集合上の cycle-preserving involution は D_5 の元 (10 通り):
  --   identity (5 fixed) + 5 reflections (1 fixed each).
  -- 全列挙で `native_decide` 検証.
  revert f hinv hcycle
  native_decide

/-! ## τ-誘導 Fin 5 上 cycle 関数 -/

/-- τ-誘導 Fin 5 上の関数: σ_fix.v が Fix(σ) との bijection を与えるので,
τ (σ_fix.v i) ∈ Fix(σ) を σ_fix.v で送り戻す形. -/
noncomputable def dihedral_τC5_fn (hdihe : h.τ * h.σ * h.τ = h.σ⁻¹) (i : Fin 5) : Fin 5 := by
  classical
  have h_τfix : h.σ (h.τ (h.σ_fix.v i)) = h.τ (h.σ_fix.v i) :=
    h.τ_preserves_σ_fix (h.σ_fix.v_fixed i)
  exact (h.σ_fix.span _ h_τfix).choose

theorem dihedral_τC5_fn_spec
    (hdihe : h.τ * h.σ * h.τ = h.σ⁻¹) (i : Fin 5) :
    h.τ (h.σ_fix.v i) = h.σ_fix.v (h.dihedral_τC5_fn hdihe i) := by
  classical
  have h_τfix : h.σ (h.τ (h.σ_fix.v i)) = h.τ (h.σ_fix.v i) :=
    h.τ_preserves_σ_fix (h.σ_fix.v_fixed i)
  exact (h.σ_fix.span _ h_τfix).choose_spec

theorem dihedral_τC5_fn_involutive
    (hdihe : h.τ * h.σ * h.τ = h.σ⁻¹) :
    ∀ i, h.dihedral_τC5_fn hdihe (h.dihedral_τC5_fn hdihe i) = i := by
  intro i
  apply h.σ_fix.v_injective
  rw [← h.dihedral_τC5_fn_spec hdihe, ← h.dihedral_τC5_fn_spec hdihe]
  exact h.τ_involutive _

theorem dihedral_τC5_fn_cycle
    (hdihe : h.τ * h.σ * h.τ = h.σ⁻¹) (i : Fin 5) :
    h.dihedral_τC5_fn hdihe (i + 1) = h.dihedral_τC5_fn hdihe i + 1 ∨
    h.dihedral_τC5_fn hdihe (i + 1) = h.dihedral_τC5_fn hdihe i - 1 := by
  -- Γ.Adj (σ_fix.v i) (σ_fix.v (i+1))
  have h_adj : Γ.Adj (h.σ_fix.v i) (h.σ_fix.v (i+1)) := h.σ_fix.cycle_adj i
  -- τ は Γ aut
  have h_τadj : Γ.Adj (h.τ (h.σ_fix.v i)) (h.τ (h.σ_fix.v (i+1))) :=
    (h.τ_aut _ _).mp h_adj
  -- τ (σ_fix.v ·) = σ_fix.v (τC5 ·)
  rw [h.dihedral_τC5_fn_spec hdihe, h.dihedral_τC5_fn_spec hdihe] at h_τadj
  exact h.σ_fix.cycle_only _ _ h_τadj

/-- τ-誘導関数の id-or-reflection 二択. -/
theorem dihedral_τC5_fn_classify
    (hdihe : h.τ * h.σ * h.τ = h.σ⁻¹) :
    (∀ i, h.dihedral_τC5_fn hdihe i = i) ∨
    (∃ idx : Fin 5,
      (∀ j, h.dihedral_τC5_fn hdihe j = j ↔ j = idx) ∧
      h.dihedral_τC5_fn hdihe (idx + 1) = idx + 4 ∧
      h.dihedral_τC5_fn hdihe (idx + 2) = idx + 3 ∧
      h.dihedral_τC5_fn hdihe (idx + 4) = idx + 1 ∧
      h.dihedral_τC5_fn hdihe (idx + 3) = idx + 2) :=
  Fin5_cycle_involution_classify _
    (h.dihedral_τC5_fn_involutive hdihe)
    (h.dihedral_τC5_fn_cycle hdihe)

/-! ## id case 排除: Fix(σ) ⊂ Fix(τ) は K_{1,55} と矛盾 -/

theorem dihedral_τC5_fn_ne_id
    (hdihe : h.τ * h.σ * h.τ = h.σ⁻¹) :
    ¬ (∀ i, h.dihedral_τC5_fn hdihe i = i) := by
  intro hAll
  -- すべての σ_fix.v i が τ-不動点 ⟹ Fix(σ) ⊂ Fix(τ) = K_{1,55}.
  -- 5 元 cycle 中 ≤ 1 center, ≥ 4 leaves. 隣接 leaf-leaf が必ず存在 ⟹ no_leaf_leaf 矛盾.
  have h_all_τfix : ∀ i : Fin 5, h.τ (h.σ_fix.v i) = h.σ_fix.v i := by
    intro i
    rw [h.dihedral_τC5_fn_spec hdihe, hAll i]
  -- Fix(τ) 内 = center or leaf
  -- 各 σ_fix.v i は K_{1,55} の center か leaf
  -- 中心は K155FixedData.span から
  have h_classify : ∀ i : Fin 5,
      h.σ_fix.v i = h.τ_fix.center ∨ ∃ j : Fin 55, h.σ_fix.v i = h.τ_fix.leaf j := by
    intro i; exact h.τ_fix.span _ (h_all_τfix i)
  -- 5 元から center を引いて ≥ 4 leaves. 隣接 leaf 同士は cycle_adj だが no_leaf_leaf 矛盾.
  -- 鳩巣: 5 個のうち center は高々 1.
  -- 0-1, 1-2, 2-3, 3-4, 4-0 は cycle 隣接. 5 edge.
  -- center が高々 1 vertex なら, 高々 2 edge が center 経由. 残り 3 edge は leaf-leaf.
  -- それを使って矛盾.
  -- 簡単のため: 0 と 1 を見る. 高々 1 center. case 分岐.
  rcases h_classify 0 with h0c | ⟨j0, h0l⟩
  · -- 0 が center. 1 は leaf (∵ center は一意).
    rcases h_classify 1 with h1c | ⟨j1, h1l⟩
    · -- 0, 1 共に center: 0 = 1 ∈ V (両者 = h.τ_fix.center).
      have : h.σ_fix.v 0 = h.σ_fix.v 1 := h0c.trans h1c.symm
      have : (0 : Fin 5) = 1 := h.σ_fix.v_injective this
      exact absurd this (by decide)
    · -- 0 = center, 1 = leaf j1. では 2 はどうか?
      rcases h_classify 2 with h2c | ⟨j2, h2l⟩
      · -- 0 = center, 2 = center: 0 = 2 in V.
        have : h.σ_fix.v 0 = h.σ_fix.v 2 := h0c.trans h2c.symm
        have : (0 : Fin 5) = 2 := h.σ_fix.v_injective this
        exact absurd this (by decide)
      · -- 0 = center, 1 = leaf, 2 = leaf. Edge 1-2 は cycle edge, leaf-leaf 矛盾.
        have h_adj12 : Γ.Adj (h.σ_fix.v 1) (h.σ_fix.v 2) := h.σ_fix.cycle_adj 1
        rw [h1l, h2l] at h_adj12
        exact h.τ_fix.no_leaf_leaf j1 j2 h_adj12
  · -- 0 = leaf j0. 残りで center は高々 1.
    rcases h_classify 1 with h1c | ⟨j1, h1l⟩
    · -- 0 = leaf, 1 = center. 2 はどうか?
      rcases h_classify 2 with h2c | ⟨_, _⟩
      · -- 1 = center, 2 = center: 矛盾.
        have : h.σ_fix.v 1 = h.σ_fix.v 2 := h1c.trans h2c.symm
        have : (1 : Fin 5) = 2 := h.σ_fix.v_injective this
        exact absurd this (by decide)
      · -- 0 = leaf, 1 = center, 2 = leaf. では 3, 4 を見て leaf-leaf 隣接を探す.
        rcases h_classify 3 with h3c | ⟨j3, h3l⟩
        · -- 1 = center, 3 = center: 矛盾.
          have : h.σ_fix.v 1 = h.σ_fix.v 3 := h1c.trans h3c.symm
          have : (1 : Fin 5) = 3 := h.σ_fix.v_injective this
          exact absurd this (by decide)
        · -- 0, 2, 3 が leaf. Edge 2-3 cycle, leaf-leaf 矛盾.
          rename_i j2 h2l
          have h_adj23 : Γ.Adj (h.σ_fix.v 2) (h.σ_fix.v 3) := h.σ_fix.cycle_adj 2
          rw [h2l, h3l] at h_adj23
          exact h.τ_fix.no_leaf_leaf j2 j3 h_adj23
    · -- 0 = leaf, 1 = leaf. Edge 0-1 cycle, leaf-leaf 矛盾.
      have h_adj01 : Γ.Adj (h.σ_fix.v 0) (h.σ_fix.v 1) := h.σ_fix.cycle_adj 0
      rw [h0l, h1l] at h_adj01
      exact h.τ_fix.no_leaf_leaf j0 j1 h_adj01

/-! ## τ-不動点インデックスの存在と一意性 -/

/-- dihedral case: C_5 = Fix(σ) 上の τ-不動点は丁度 1 個存在. -/
theorem dihedral_existsUnique_τFixedInC5
    (hdihe : h.τ * h.σ * h.τ = h.σ⁻¹) :
    ∃! i : Fin 5, h.τ (h.σ_fix.v i) = h.σ_fix.v i := by
  rcases h.dihedral_τC5_fn_classify hdihe with hId | ⟨idx, hUniq, _⟩
  · exact absurd hId (h.dihedral_τC5_fn_ne_id hdihe)
  · refine ⟨idx, ?_, ?_⟩
    · -- exists witness: τC5 idx = idx ⟹ τ (σ_fix.v idx) = σ_fix.v idx
      show h.τ (h.σ_fix.v idx) = h.σ_fix.v idx
      have hfix : h.dihedral_τC5_fn hdihe idx = idx := (hUniq idx).mpr rfl
      rw [h.dihedral_τC5_fn_spec hdihe, hfix]
    · -- uniqueness
      intro j hj
      -- hj : τ (σ_fix.v j) = σ_fix.v j ⟹ τC5 j = j
      have hτC5 : h.dihedral_τC5_fn hdihe j = j := by
        have hspec := h.dihedral_τC5_fn_spec hdihe j
        rw [hj] at hspec
        exact h.σ_fix.v_injective hspec.symm
      exact (hUniq j).mp hτC5

/-- 唯一の τ-不動点インデックス. -/
noncomputable def dihedral_τFixedIndex
    (hdihe : h.τ * h.σ * h.τ = h.σ⁻¹) : Fin 5 :=
  (h.dihedral_existsUnique_τFixedInC5 hdihe).choose

theorem dihedral_τFixedIndex_spec
    (hdihe : h.τ * h.σ * h.τ = h.σ⁻¹) :
    h.τ (h.σ_fix.v (h.dihedral_τFixedIndex hdihe)) =
      h.σ_fix.v (h.dihedral_τFixedIndex hdihe) :=
  (h.dihedral_existsUnique_τFixedInC5 hdihe).choose_spec.1

theorem dihedral_τFixedIndex_unique
    (hdihe : h.τ * h.σ * h.τ = h.σ⁻¹)
    (i : Fin 5) (hi : h.τ (h.σ_fix.v i) = h.σ_fix.v i) :
    i = h.dihedral_τFixedIndex hdihe :=
  (h.dihedral_existsUnique_τFixedInC5 hdihe).choose_spec.2 i hi

/-! ## 5 個の cycle 上頂点アクセサ -/

/-- 唯一の τ-不動点. -/
noncomputable def dihedral_uτ (hdihe : h.τ * h.σ * h.τ = h.σ⁻¹) : V :=
  h.σ_fix.v (h.dihedral_τFixedIndex hdihe)

/-- cycle 上 u_τ の次 (前進). -/
noncomputable def dihedral_aτ (hdihe : h.τ * h.σ * h.τ = h.σ⁻¹) : V :=
  h.σ_fix.v (h.dihedral_τFixedIndex hdihe + 1)

/-- u_τ の 2 つ先. -/
noncomputable def dihedral_bτ (hdihe : h.τ * h.σ * h.τ = h.σ⁻¹) : V :=
  h.σ_fix.v (h.dihedral_τFixedIndex hdihe + 2)

/-- u_τ の 2 つ前. -/
noncomputable def dihedral_cτ (hdihe : h.τ * h.σ * h.τ = h.σ⁻¹) : V :=
  h.σ_fix.v (h.dihedral_τFixedIndex hdihe + 3)

/-- cycle 上 u_τ の前 (後退). -/
noncomputable def dihedral_dτ (hdihe : h.τ * h.σ * h.τ = h.σ⁻¹) : V :=
  h.σ_fix.v (h.dihedral_τFixedIndex hdihe + 4)

/-! ## σ-不動性 (すべて Fix(σ) 内) -/

theorem dihedral_σ_uτ (hdihe : h.τ * h.σ * h.τ = h.σ⁻¹) :
    h.σ (h.dihedral_uτ hdihe) = h.dihedral_uτ hdihe :=
  h.σ_fix.v_fixed _
theorem dihedral_σ_aτ (hdihe : h.τ * h.σ * h.τ = h.σ⁻¹) :
    h.σ (h.dihedral_aτ hdihe) = h.dihedral_aτ hdihe :=
  h.σ_fix.v_fixed _
theorem dihedral_σ_bτ (hdihe : h.τ * h.σ * h.τ = h.σ⁻¹) :
    h.σ (h.dihedral_bτ hdihe) = h.dihedral_bτ hdihe :=
  h.σ_fix.v_fixed _
theorem dihedral_σ_cτ (hdihe : h.τ * h.σ * h.τ = h.σ⁻¹) :
    h.σ (h.dihedral_cτ hdihe) = h.dihedral_cτ hdihe :=
  h.σ_fix.v_fixed _
theorem dihedral_σ_dτ (hdihe : h.τ * h.σ * h.τ = h.σ⁻¹) :
    h.σ (h.dihedral_dτ hdihe) = h.dihedral_dτ hdihe :=
  h.σ_fix.v_fixed _

/-! ## τ-不動性と swap -/

@[simp] theorem dihedral_τ_uτ (hdihe : h.τ * h.σ * h.τ = h.σ⁻¹) :
    h.τ (h.dihedral_uτ hdihe) = h.dihedral_uτ hdihe :=
  h.dihedral_τFixedIndex_spec hdihe

/-- 分類定理由来の swap 構造を `dihedral_τFixedIndex` 周りに焼き直す helper. -/
private theorem dihedral_τC5_swap_at_τFixedIndex
    (hdihe : h.τ * h.σ * h.τ = h.σ⁻¹) :
    h.dihedral_τC5_fn hdihe (h.dihedral_τFixedIndex hdihe + 1) =
        h.dihedral_τFixedIndex hdihe + 4 ∧
    h.dihedral_τC5_fn hdihe (h.dihedral_τFixedIndex hdihe + 2) =
        h.dihedral_τFixedIndex hdihe + 3 ∧
    h.dihedral_τC5_fn hdihe (h.dihedral_τFixedIndex hdihe + 4) =
        h.dihedral_τFixedIndex hdihe + 1 ∧
    h.dihedral_τC5_fn hdihe (h.dihedral_τFixedIndex hdihe + 3) =
        h.dihedral_τFixedIndex hdihe + 2 := by
  rcases h.dihedral_τC5_fn_classify hdihe with hId | ⟨cidx, hUniq, hS1, hS2, hS3, hS4⟩
  · exact absurd hId (h.dihedral_τC5_fn_ne_id hdihe)
  · -- cidx は classification の不動点; これと dihedral_τFixedIndex hdihe が一致.
    have hcidx_fix_C5 : h.dihedral_τC5_fn hdihe cidx = cidx := (hUniq cidx).mpr rfl
    have hcidx_fix : h.τ (h.σ_fix.v cidx) = h.σ_fix.v cidx := by
      have := h.dihedral_τC5_fn_spec hdihe cidx
      rw [hcidx_fix_C5] at this
      exact this
    have heq : cidx = h.dihedral_τFixedIndex hdihe :=
      h.dihedral_τFixedIndex_unique hdihe cidx hcidx_fix
    rw [← heq]
    exact ⟨hS1, hS2, hS3, hS4⟩

theorem dihedral_τ_aτ (hdihe : h.τ * h.σ * h.τ = h.σ⁻¹) :
    h.τ (h.dihedral_aτ hdihe) = h.dihedral_dτ hdihe := by
  unfold dihedral_aτ dihedral_dτ
  rw [h.dihedral_τC5_fn_spec hdihe (h.dihedral_τFixedIndex hdihe + 1)]
  rw [(h.dihedral_τC5_swap_at_τFixedIndex hdihe).1]

theorem dihedral_τ_dτ (hdihe : h.τ * h.σ * h.τ = h.σ⁻¹) :
    h.τ (h.dihedral_dτ hdihe) = h.dihedral_aτ hdihe := by
  unfold dihedral_aτ dihedral_dτ
  rw [h.dihedral_τC5_fn_spec hdihe (h.dihedral_τFixedIndex hdihe + 4)]
  rw [(h.dihedral_τC5_swap_at_τFixedIndex hdihe).2.2.1]

theorem dihedral_τ_bτ (hdihe : h.τ * h.σ * h.τ = h.σ⁻¹) :
    h.τ (h.dihedral_bτ hdihe) = h.dihedral_cτ hdihe := by
  unfold dihedral_bτ dihedral_cτ
  rw [h.dihedral_τC5_fn_spec hdihe (h.dihedral_τFixedIndex hdihe + 2)]
  rw [(h.dihedral_τC5_swap_at_τFixedIndex hdihe).2.1]

theorem dihedral_τ_cτ (hdihe : h.τ * h.σ * h.τ = h.σ⁻¹) :
    h.τ (h.dihedral_cτ hdihe) = h.dihedral_bτ hdihe := by
  unfold dihedral_bτ dihedral_cτ
  rw [h.dihedral_τC5_fn_spec hdihe (h.dihedral_τFixedIndex hdihe + 3)]
  rw [(h.dihedral_τC5_swap_at_τFixedIndex hdihe).2.2.2]

/-! ## Cycle 隣接 -/

theorem dihedral_adj_uτ_aτ (hdihe : h.τ * h.σ * h.τ = h.σ⁻¹) :
    Γ.Adj (h.dihedral_uτ hdihe) (h.dihedral_aτ hdihe) := by
  unfold dihedral_uτ dihedral_aτ
  exact h.σ_fix.cycle_adj _

theorem dihedral_adj_aτ_bτ (hdihe : h.τ * h.σ * h.τ = h.σ⁻¹) :
    Γ.Adj (h.dihedral_aτ hdihe) (h.dihedral_bτ hdihe) := by
  unfold dihedral_aτ dihedral_bτ
  have h_step := h.σ_fix.cycle_adj (h.dihedral_τFixedIndex hdihe + 1)
  have h_eq : (h.dihedral_τFixedIndex hdihe + 1 + 1 : Fin 5) =
      h.dihedral_τFixedIndex hdihe + 2 := by
    rw [add_assoc]; rfl
  rwa [h_eq] at h_step

theorem dihedral_adj_bτ_cτ (hdihe : h.τ * h.σ * h.τ = h.σ⁻¹) :
    Γ.Adj (h.dihedral_bτ hdihe) (h.dihedral_cτ hdihe) := by
  unfold dihedral_bτ dihedral_cτ
  have h_step := h.σ_fix.cycle_adj (h.dihedral_τFixedIndex hdihe + 2)
  have h_eq : (h.dihedral_τFixedIndex hdihe + 2 + 1 : Fin 5) =
      h.dihedral_τFixedIndex hdihe + 3 := by
    rw [add_assoc]; rfl
  rwa [h_eq] at h_step

theorem dihedral_adj_cτ_dτ (hdihe : h.τ * h.σ * h.τ = h.σ⁻¹) :
    Γ.Adj (h.dihedral_cτ hdihe) (h.dihedral_dτ hdihe) := by
  unfold dihedral_cτ dihedral_dτ
  have h_step := h.σ_fix.cycle_adj (h.dihedral_τFixedIndex hdihe + 3)
  have h_eq : (h.dihedral_τFixedIndex hdihe + 3 + 1 : Fin 5) =
      h.dihedral_τFixedIndex hdihe + 4 := by
    rw [add_assoc]; rfl
  rwa [h_eq] at h_step

theorem dihedral_adj_dτ_uτ (hdihe : h.τ * h.σ * h.τ = h.σ⁻¹) :
    Γ.Adj (h.dihedral_dτ hdihe) (h.dihedral_uτ hdihe) := by
  unfold dihedral_dτ dihedral_uτ
  have h_step := h.σ_fix.cycle_adj (h.dihedral_τFixedIndex hdihe + 4)
  have h_eq : (h.dihedral_τFixedIndex hdihe + 4 + 1 : Fin 5) =
      h.dihedral_τFixedIndex hdihe := by
    have h5 : ((4 : Fin 5) + 1 : Fin 5) = 0 := by decide
    rw [add_assoc, h5, add_zero]
  rwa [h_eq] at h_step

/-! ## 5 頂点は相異 -/

theorem dihedral_uτ_ne_aτ (hdihe : h.τ * h.σ * h.τ = h.σ⁻¹) :
    h.dihedral_uτ hdihe ≠ h.dihedral_aτ hdihe := by
  intro heq
  unfold dihedral_uτ dihedral_aτ at heq
  have hidx : h.dihedral_τFixedIndex hdihe = h.dihedral_τFixedIndex hdihe + 1 :=
    h.σ_fix.v_injective heq
  have h0eq1 : (0 : Fin 5) = 1 := by
    have h' : h.dihedral_τFixedIndex hdihe + 0 = h.dihedral_τFixedIndex hdihe + 1 := by
      rw [add_zero]; exact hidx
    exact add_left_cancel h'
  exact absurd h0eq1 (by decide)

theorem dihedral_uτ_ne_bτ (hdihe : h.τ * h.σ * h.τ = h.σ⁻¹) :
    h.dihedral_uτ hdihe ≠ h.dihedral_bτ hdihe := by
  intro heq
  unfold dihedral_uτ dihedral_bτ at heq
  have hidx : h.dihedral_τFixedIndex hdihe = h.dihedral_τFixedIndex hdihe + 2 :=
    h.σ_fix.v_injective heq
  have h0eq2 : (0 : Fin 5) = 2 := by
    have h' : h.dihedral_τFixedIndex hdihe + 0 = h.dihedral_τFixedIndex hdihe + 2 := by
      rw [add_zero]; exact hidx
    exact add_left_cancel h'
  exact absurd h0eq2 (by decide)

theorem dihedral_uτ_ne_cτ (hdihe : h.τ * h.σ * h.τ = h.σ⁻¹) :
    h.dihedral_uτ hdihe ≠ h.dihedral_cτ hdihe := by
  intro heq
  unfold dihedral_uτ dihedral_cτ at heq
  have hidx : h.dihedral_τFixedIndex hdihe = h.dihedral_τFixedIndex hdihe + 3 :=
    h.σ_fix.v_injective heq
  have h0eq3 : (0 : Fin 5) = 3 := by
    have h' : h.dihedral_τFixedIndex hdihe + 0 = h.dihedral_τFixedIndex hdihe + 3 := by
      rw [add_zero]; exact hidx
    exact add_left_cancel h'
  exact absurd h0eq3 (by decide)

theorem dihedral_uτ_ne_dτ (hdihe : h.τ * h.σ * h.τ = h.σ⁻¹) :
    h.dihedral_uτ hdihe ≠ h.dihedral_dτ hdihe := by
  intro heq
  unfold dihedral_uτ dihedral_dτ at heq
  have hidx : h.dihedral_τFixedIndex hdihe = h.dihedral_τFixedIndex hdihe + 4 :=
    h.σ_fix.v_injective heq
  have h0eq4 : (0 : Fin 5) = 4 := by
    have h' : h.dihedral_τFixedIndex hdihe + 0 = h.dihedral_τFixedIndex hdihe + 4 := by
      rw [add_zero]; exact hidx
    exact add_left_cancel h'
  exact absurd h0eq4 (by decide)

theorem dihedral_aτ_ne_bτ (hdihe : h.τ * h.σ * h.τ = h.σ⁻¹) :
    h.dihedral_aτ hdihe ≠ h.dihedral_bτ hdihe := by
  intro heq
  unfold dihedral_aτ dihedral_bτ at heq
  have hidx : h.dihedral_τFixedIndex hdihe + 1 = h.dihedral_τFixedIndex hdihe + 2 :=
    h.σ_fix.v_injective heq
  have h1eq2 : (1 : Fin 5) = 2 := add_left_cancel hidx
  exact absurd h1eq2 (by decide)

theorem dihedral_aτ_ne_cτ (hdihe : h.τ * h.σ * h.τ = h.σ⁻¹) :
    h.dihedral_aτ hdihe ≠ h.dihedral_cτ hdihe := by
  intro heq
  unfold dihedral_aτ dihedral_cτ at heq
  have hidx : h.dihedral_τFixedIndex hdihe + 1 = h.dihedral_τFixedIndex hdihe + 3 :=
    h.σ_fix.v_injective heq
  have h1eq3 : (1 : Fin 5) = 3 := add_left_cancel hidx
  exact absurd h1eq3 (by decide)

theorem dihedral_aτ_ne_dτ (hdihe : h.τ * h.σ * h.τ = h.σ⁻¹) :
    h.dihedral_aτ hdihe ≠ h.dihedral_dτ hdihe := by
  intro heq
  unfold dihedral_aτ dihedral_dτ at heq
  have hidx : h.dihedral_τFixedIndex hdihe + 1 = h.dihedral_τFixedIndex hdihe + 4 :=
    h.σ_fix.v_injective heq
  have h1eq4 : (1 : Fin 5) = 4 := add_left_cancel hidx
  exact absurd h1eq4 (by decide)

theorem dihedral_bτ_ne_cτ (hdihe : h.τ * h.σ * h.τ = h.σ⁻¹) :
    h.dihedral_bτ hdihe ≠ h.dihedral_cτ hdihe := by
  intro heq
  unfold dihedral_bτ dihedral_cτ at heq
  have hidx : h.dihedral_τFixedIndex hdihe + 2 = h.dihedral_τFixedIndex hdihe + 3 :=
    h.σ_fix.v_injective heq
  have h2eq3 : (2 : Fin 5) = 3 := add_left_cancel hidx
  exact absurd h2eq3 (by decide)

theorem dihedral_bτ_ne_dτ (hdihe : h.τ * h.σ * h.τ = h.σ⁻¹) :
    h.dihedral_bτ hdihe ≠ h.dihedral_dτ hdihe := by
  intro heq
  unfold dihedral_bτ dihedral_dτ at heq
  have hidx : h.dihedral_τFixedIndex hdihe + 2 = h.dihedral_τFixedIndex hdihe + 4 :=
    h.σ_fix.v_injective heq
  have h2eq4 : (2 : Fin 5) = 4 := add_left_cancel hidx
  exact absurd h2eq4 (by decide)

theorem dihedral_cτ_ne_dτ (hdihe : h.τ * h.σ * h.τ = h.σ⁻¹) :
    h.dihedral_cτ hdihe ≠ h.dihedral_dτ hdihe := by
  intro heq
  unfold dihedral_cτ dihedral_dτ at heq
  have hidx : h.dihedral_τFixedIndex hdihe + 3 = h.dihedral_τFixedIndex hdihe + 4 :=
    h.σ_fix.v_injective heq
  have h3eq4 : (3 : Fin 5) = 4 := add_left_cancel hidx
  exact absurd h3eq4 (by decide)

/-! ## 対角非隣接 -/

theorem dihedral_not_adj_uτ_bτ (hdihe : h.τ * h.σ * h.τ = h.σ⁻¹) :
    ¬ Γ.Adj (h.dihedral_uτ hdihe) (h.dihedral_bτ hdihe) := by
  intro hadj
  unfold dihedral_uτ dihedral_bτ at hadj
  rcases h.σ_fix.cycle_only _ _ hadj with h1 | h2
  · -- idx + 2 = idx + 1
    have h2eq1 : (2 : Fin 5) = 1 := add_left_cancel h1
    exact absurd h2eq1 (by decide)
  · -- idx + 2 = idx - 1
    have h2' : h.dihedral_τFixedIndex hdihe + 2 =
        h.dihedral_τFixedIndex hdihe + (-1 : Fin 5) := by
      rw [← sub_eq_add_neg]; exact h2
    have h2eq_neg1 : (2 : Fin 5) = -1 := add_left_cancel h2'
    exact absurd h2eq_neg1 (by decide)

theorem dihedral_not_adj_uτ_cτ (hdihe : h.τ * h.σ * h.τ = h.σ⁻¹) :
    ¬ Γ.Adj (h.dihedral_uτ hdihe) (h.dihedral_cτ hdihe) := by
  intro hadj
  unfold dihedral_uτ dihedral_cτ at hadj
  rcases h.σ_fix.cycle_only _ _ hadj with h1 | h2
  · -- idx + 3 = idx + 1
    have h3eq1 : (3 : Fin 5) = 1 := add_left_cancel h1
    exact absurd h3eq1 (by decide)
  · -- idx + 3 = idx - 1
    have h2' : h.dihedral_τFixedIndex hdihe + 3 =
        h.dihedral_τFixedIndex hdihe + (-1 : Fin 5) := by
      rw [← sub_eq_add_neg]; exact h2
    have h3eq_neg1 : (3 : Fin 5) = -1 := add_left_cancel h2'
    exact absurd h3eq_neg1 (by decide)

/-! ## τ-不動点の特徴づけ: Fix(σ) ∩ Fix(τ) = {u_τ} -/

/-- Fix(σ) ∩ Fix(τ) は丁度 {u_τ}. -/
theorem dihedral_σFix_τFix_eq_uτ
    (hdihe : h.τ * h.σ * h.τ = h.σ⁻¹) (x : V)
    (hxσ : h.σ x = x) (hxτ : h.τ x = x) :
    x = h.dihedral_uτ hdihe := by
  rcases h.σ_fix.span x hxσ with ⟨i, hi⟩
  rw [hi]
  rw [hi] at hxτ
  have : i = h.dihedral_τFixedIndex hdihe := h.dihedral_τFixedIndex_unique hdihe i hxτ
  rw [this]
  rfl

end Order22ActsOnMoore57

end Moore57
