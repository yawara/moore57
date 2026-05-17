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

/-! ## τ-不動点インデックスの存在と一意性 -/

/-- dihedral case: C_5 = Fix(σ) 上の τ-不動点は丁度 1 個存在. -/
theorem dihedral_existsUnique_τFixedInC5
    (hdihe : h.τ * h.σ * h.τ = h.σ⁻¹) :
    ∃! i : Fin 5, h.τ (h.σ_fix.v i) = h.σ_fix.v i := by
  sorry

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

theorem dihedral_τ_aτ (hdihe : h.τ * h.σ * h.τ = h.σ⁻¹) :
    h.τ (h.dihedral_aτ hdihe) = h.dihedral_dτ hdihe := by
  sorry

theorem dihedral_τ_dτ (hdihe : h.τ * h.σ * h.τ = h.σ⁻¹) :
    h.τ (h.dihedral_dτ hdihe) = h.dihedral_aτ hdihe := by
  sorry

theorem dihedral_τ_bτ (hdihe : h.τ * h.σ * h.τ = h.σ⁻¹) :
    h.τ (h.dihedral_bτ hdihe) = h.dihedral_cτ hdihe := by
  sorry

theorem dihedral_τ_cτ (hdihe : h.τ * h.σ * h.τ = h.σ⁻¹) :
    h.τ (h.dihedral_cτ hdihe) = h.dihedral_bτ hdihe := by
  sorry

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
