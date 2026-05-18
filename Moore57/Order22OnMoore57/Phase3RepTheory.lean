import Moore57.Order22OnMoore57.TraceConstancy
import Moore57.Order22OnMoore57.ComplexRestriction

/-!
# 自然言語証明 §3 Step (A): C_11 表現論で `11 n = 25 + 15(a_7 - c_7)` と `(a_7-c_7) ≡ 2 (mod 11)`

`exists_dim_trace_decomp_of_idempotent_pow_eq_one` (汎用 helper) を Moore57 の
3 つの有理固有空間 E_57, E_7, E_{-8} に適用し, それぞれの自明部分次元
`a_λ` と Φ_11-成分の重複 `c_λ` を抽出. 主な等式は

* `Tk = adjacentMovedCount σ` の matrix trace bridge
* `A = 57 E_57 + 7 E_7 - 8 E_{-8}` の spectral decomp
* `trace(P_σ) = fixedVertexCount σ = 5` の固定点数等式
* `finrank V_7 = 1729`, `finrank V_{-8} = 1520`

を組み合わせて

  `11 n = 25 + 15 (a_7 - c_7)`

を導く. 次に `a_7 + 10 c_7 = 1729 ≡ 2 (mod 11)` から `(a_7 - c_7) ≡ 2 (mod 11)`,
これと `eq_five_plus_fifteen_mul_of_modular` で `∃ s, n = 5 + 15 s` を得る.
-/

namespace Moore57

open SimpleGraph Finset

section Idempotent

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

omit [Fintype V] in
/-- `permMatrix (1 : Equiv.Perm V) = 1` (Moore57 convention). -/
private theorem _root_.Moore57.permMatrix_one_eq_one_helper :
    (permMatrix (1 : Equiv.Perm V) : Matrix V V ℚ) = 1 := by
  change Equiv.Perm.permMatrix ℚ ((1 : Equiv.Perm V)⁻¹) = 1
  simp

/-- E_7 の toLin' は idempotent. -/
private theorem E7Matrix_toLin'_isIdempotentElem'' (hΓ : IsMoore57 Γ) :
    IsIdempotentElem ((E7Matrix Γ).toLin' : (V → ℚ) →ₗ[ℚ] (V → ℚ)) := by
  rw [IsIdempotentElem, Module.End.mul_eq_comp, ← Moore57.matrix_toLin'_mul,
    E7Matrix_mul_E7Matrix_eq_E7Matrix hΓ]

/-- E_{-8} の toLin' は idempotent. -/
private theorem EMinus8Matrix_toLin'_isIdempotentElem'' (hΓ : IsMoore57 Γ) :
    IsIdempotentElem ((EMinus8Matrix Γ).toLin' : (V → ℚ) →ₗ[ℚ] (V → ℚ)) := by
  rw [IsIdempotentElem, Module.End.mul_eq_comp, ← Moore57.matrix_toLin'_mul,
    EMinus8Matrix_mul_EMinus8Matrix_eq_EMinus8Matrix hΓ]

/-- Higman trace formula at the identity: `trace E_7 = 1729`. -/
theorem trace_E7Matrix_eq_1729_helper (hΓ : IsMoore57 Γ) :
    Matrix.trace (E7Matrix Γ : Matrix V V ℚ) = 1729 := by
  have hfmla := Moore57.trace_E7Matrix_mul_permMatrix Γ (1 : Equiv.Perm V)
  rw [Moore57.permMatrix_one_eq_one_helper, Matrix.mul_one] at hfmla
  rw [hfmla]
  -- adjacentMovedCount Γ 1 = 0, fixedVertexCount 1 = card V = 3250
  have h_a0 : adjacentMovedCount Γ (1 : Equiv.Perm V) = 0 := by
    classical
    unfold adjacentMovedCount
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro v _
    simp
  have h_a1 : fixedVertexCount (1 : Equiv.Perm V) = Fintype.card V := by
    classical
    unfold fixedVertexCount
    rw [Finset.filter_true_of_mem]
    · exact Finset.card_univ
    · intro v _
      rfl
  rw [h_a0, h_a1, hΓ.card]
  norm_num

/-- E_λ の rank = matrix trace.
イデンポテント `E.toLin'` の像の次元は `tr(E)` (matrix trace) に等しい. -/
theorem finrank_range_eq_matrix_trace
    (E : Matrix V V ℚ)
    (hE_idem : IsIdempotentElem (E.toLin' : (V → ℚ) →ₗ[ℚ] (V → ℚ))) :
    (Module.finrank ℚ (LinearMap.range E.toLin') : ℚ) = Matrix.trace E := by
  have hcomm_1 : Commute (E.toLin' : (V → ℚ) →ₗ[ℚ] (V → ℚ)) 1 := Commute.one_right _
  have hbridge :=
    Moore57.LinearMap.trace_restrict_range_eq_trace_comp_of_isIdempotentElem
      E.toLin' 1 hE_idem hcomm_1
  -- RHS = trace(E ∘ 1) = trace(E) = matrix trace
  have hRHS :
      LinearMap.trace ℚ (V → ℚ) (E.toLin' ∘ₗ (1 : (V → ℚ) →ₗ[ℚ] (V → ℚ))) =
        Matrix.trace E := by
    have h_comp_1 : (E.toLin' : (V → ℚ) →ₗ[ℚ] (V → ℚ)) ∘ₗ
        (1 : (V → ℚ) →ₗ[ℚ] (V → ℚ)) = E.toLin' := by
      ext v; simp
    rw [h_comp_1]
    exact Moore57.trace_toLin'_eq_matrix_trace E
  -- The hbridge LHS: trace of (1.restrict ...) on (range E.toLin').
  -- This is identity, so its trace = finrank.
  set hmaps_1 :
      Set.MapsTo (1 : (V → ℚ) →ₗ[ℚ] (V → ℚ))
        (LinearMap.range E.toLin') (LinearMap.range E.toLin') :=
    fun x hx => by
      change (1 : (V → ℚ) →ₗ[ℚ] (V → ℚ)) x ∈ LinearMap.range E.toLin'
      simpa using hx
  have h_restrict_id :
      (1 : (V → ℚ) →ₗ[ℚ] (V → ℚ)).restrict hmaps_1 =
        LinearMap.id := by
    refine LinearMap.ext fun v => ?_
    apply Subtype.ext
    change (1 : (V → ℚ) →ₗ[ℚ] (V → ℚ)) v.val = v.val
    simp
  have h_LHS_trace_id :
      LinearMap.trace ℚ (LinearMap.range E.toLin')
        ((1 : (V → ℚ) →ₗ[ℚ] (V → ℚ)).restrict hmaps_1) =
        (Module.finrank ℚ (LinearMap.range E.toLin') : ℚ) := by
    rw [h_restrict_id, LinearMap.trace_id]
  -- The hbridge has a specific (more complicated) MapsTo. Need to show it equals our hmaps_1.
  rw [show (1 : (V → ℚ) →ₗ[ℚ] (V → ℚ)).restrict (by
        intro x hx
        exact ((Module.End.mem_invtSubmodule_iff_mapsTo
          (f := (1 : (V → ℚ) →ₗ[ℚ] (V → ℚ)))).mp
          ((LinearMap.IsIdempotentElem.commute_iff hE_idem
            (T := (1 : (V → ℚ) →ₗ[ℚ] (V → ℚ)))).mp hcomm_1).1) hx)
      = (1 : (V → ℚ) →ₗ[ℚ] (V → ℚ)).restrict hmaps_1 from rfl] at hbridge
  rw [h_LHS_trace_id, hRHS] at hbridge
  exact hbridge

variable (Γ) in
/-- `finrank V_7 = 1729`. -/
theorem finrank_range_E7Matrix_eq_1729 (hΓ : IsMoore57 Γ) :
    Module.finrank ℚ (LinearMap.range (E7Matrix Γ).toLin') = 1729 := by
  have hE7_idem := E7Matrix_toLin'_isIdempotentElem'' hΓ
  have hQ := finrank_range_eq_matrix_trace (E7Matrix Γ) hE7_idem
  rw [trace_E7Matrix_eq_1729_helper hΓ] at hQ
  exact_mod_cast hQ

variable (Γ) in
/-- `finrank V_{-8} = 1520`. -/
theorem finrank_range_EMinus8Matrix_eq_1520 (hΓ : IsMoore57 Γ) :
    Module.finrank ℚ (LinearMap.range (EMinus8Matrix Γ).toLin') = 1520 := by
  have hEM8_idem := EMinus8Matrix_toLin'_isIdempotentElem'' hΓ
  -- Matrix.trace (E_-8) = 3250 - 1 - 1729 = 1520
  have h_trace_eq : Matrix.trace (EMinus8Matrix Γ : Matrix V V ℚ) = 1520 := by
    change Matrix.trace ((1 : Matrix V V ℚ) - E7Matrix Γ - E57Matrix V) = 1520
    rw [Matrix.trace_sub, Matrix.trace_sub]
    have htrI : Matrix.trace (1 : Matrix V V ℚ) = (Fintype.card V : ℚ) := by
      rw [Matrix.trace_one]
    rw [htrI, hΓ.card]
    rw [trace_E7Matrix_eq_1729_helper hΓ]
    have htrE57 : Matrix.trace (E57Matrix V : Matrix V V ℚ) = 1 := by
      have := Moore57.trace_E57Matrix_mul_permMatrix (Γ := Γ) hΓ (1 : Equiv.Perm V)
      rw [Moore57.permMatrix_one_eq_one_helper, Matrix.mul_one] at this
      exact this
    rw [htrE57]
    norm_num
  have hQ := finrank_range_eq_matrix_trace (EMinus8Matrix Γ) hEM8_idem
  rw [h_trace_eq] at hQ
  exact_mod_cast hQ

end Idempotent

namespace Order22ActsOnMoore57

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]
variable (h : Order22ActsOnMoore57 V Γ)

/-! ## (A-2) `fixedVertexCount h.σ = 5` from `C5FixedData` -/

/-- C_5 固定データから, σ の固定点集合は `v` の像と一致. -/
theorem fixedFinset_σ_eq_image :
    (Finset.univ.filter fun x : V => h.σ x = x) =
      Finset.univ.image h.σ_fix.v := by
  ext x
  simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · intro hfix
    obtain ⟨i, hi⟩ := h.σ_fix.span x hfix
    exact ⟨i, hi.symm⟩
  · rintro ⟨i, rfl⟩
    exact h.σ_fix.v_fixed i

/-- `fixedVertexCount h.σ = 5`. -/
theorem fixedVertexCount_σ_eq_five :
    Moore57.fixedVertexCount h.σ = 5 := by
  unfold fixedVertexCount
  rw [h.fixedFinset_σ_eq_image]
  rw [Finset.card_image_of_injective _ h.σ_fix.v_injective]
  simp

/-! ## (A-3) Spectral decomposition + dim-trace package -/

private theorem σ_lin_pow_eleven :
    ((permMatrix h.σ).toLin' : (V → ℚ) →ₗ[ℚ] (V → ℚ)) ^ 11 = 1 := by
  rw [← Matrix.toLin'_pow, Moore57.permMatrix_pow_eq, h.σ_pow_eleven,
      Moore57.permMatrix_one_eq_one_helper, Matrix.toLin'_one]
  rfl

/-- E_7 と permMatrix h.σ が toLin' で可換. -/
private theorem E7_commute_permMatrix_σ_toLin' :
    Commute ((E7Matrix Γ).toLin' : (V → ℚ) →ₗ[ℚ] (V → ℚ))
      (permMatrix h.σ).toLin' :=
  Moore57.toLin'_commute_of_mul_eq
    (E7Matrix_mul_permMatrix_eq_permMatrix_mul_E7Matrix Γ h.σ h.σ_aut)

/-- E_-8 と permMatrix h.σ が toLin' で可換. -/
private theorem EMinus8_commute_permMatrix_σ_toLin' :
    Commute ((EMinus8Matrix Γ).toLin' : (V → ℚ) →ₗ[ℚ] (V → ℚ))
      (permMatrix h.σ).toLin' :=
  Moore57.toLin'_commute_of_mul_eq
    (EMinus8Matrix_mul_permMatrix_eq_permMatrix_mul_EMinus8Matrix h.σ h.σ_aut)

/-- 行列 trace と linear-map trace の bridge: `tr(E * P_σ) = tr(E.toLin' ∘ σ_lin)`. -/
private theorem trace_E_perm_bridge (E : Matrix V V ℚ) :
    LinearMap.trace ℚ (V → ℚ)
        (E.toLin' ∘ₗ (permMatrix h.σ).toLin') =
      Matrix.trace (E * permMatrix h.σ) := by
  rw [show E.toLin' ∘ₗ (permMatrix h.σ).toLin' = (E * permMatrix h.σ).toLin' from
      (Moore57.matrix_toLin'_mul E (permMatrix h.σ)).symm]
  exact Moore57.trace_toLin'_eq_matrix_trace _

/-- **Phase 3 核心**: E_7 の Q[C_11]-分解から `tr(E_7 P_σ) = a_7 - c_7`,
`finrank V_7 = a_7 + 10 c_7 = 1729`. -/
theorem exists_a7_c7_decomp :
    ∃ a c : ℕ,
      a + 10 * c = 1729 ∧
      Matrix.trace ((E7Matrix Γ : Matrix V V ℚ) * permMatrix h.σ) = (a : ℚ) - c := by
  haveI : Fact (Nat.Prime 11) := ⟨by decide⟩
  obtain ⟨a, c, hdim, htrace⟩ :=
    Moore57.LinearMap.exists_dim_trace_decomp_of_idempotent_pow_eq_one
      11 (permMatrix h.σ).toLin' h.σ_lin_pow_eleven
      (E7Matrix Γ).toLin'
      (E7Matrix_toLin'_isIdempotentElem'' h.isMoore)
      h.E7_commute_permMatrix_σ_toLin'
  refine ⟨a, c, ?_, ?_⟩
  · -- a + 10c = 1729
    have hf : Module.finrank ℚ (LinearMap.range (E7Matrix Γ).toLin') = 1729 :=
      finrank_range_E7Matrix_eq_1729 Γ h.isMoore
    rw [hf] at hdim
    omega
  · -- trace(E_7 * P_σ) = a - c, k = 1
    have h_trace_E7_σ := htrace (k := 1) (by norm_num) (by norm_num)
    rw [pow_one] at h_trace_E7_σ
    rw [← h.trace_E_perm_bridge (E7Matrix Γ)]
    exact h_trace_E7_σ

/-- **Phase 3 核心 (E_{-8} 側)**: 同様の分解 + `finrank V_{-8} = 1520`. -/
theorem exists_aM8_cM8_decomp :
    ∃ a c : ℕ,
      a + 10 * c = 1520 ∧
      Matrix.trace ((EMinus8Matrix Γ : Matrix V V ℚ) * permMatrix h.σ) =
        (a : ℚ) - c := by
  haveI : Fact (Nat.Prime 11) := ⟨by decide⟩
  obtain ⟨a, c, hdim, htrace⟩ :=
    Moore57.LinearMap.exists_dim_trace_decomp_of_idempotent_pow_eq_one
      11 (permMatrix h.σ).toLin' h.σ_lin_pow_eleven
      (EMinus8Matrix Γ).toLin'
      (EMinus8Matrix_toLin'_isIdempotentElem'' h.isMoore)
      h.EMinus8_commute_permMatrix_σ_toLin'
  refine ⟨a, c, ?_, ?_⟩
  · have hf : Module.finrank ℚ (LinearMap.range (EMinus8Matrix Γ).toLin') = 1520 :=
      finrank_range_EMinus8Matrix_eq_1520 Γ h.isMoore
    rw [hf] at hdim
    omega
  · have h_trace_EM8_σ := htrace (k := 1) (by norm_num) (by norm_num)
    rw [pow_one] at h_trace_EM8_σ
    rw [← h.trace_E_perm_bridge (EMinus8Matrix Γ)]
    exact h_trace_EM8_σ

/-! ## (A-4) Assembly: `∃ s, n = 5 + 15 s` -/

/-- `Matrix.trace (permMatrix h.σ) = 5`. -/
theorem trace_permMatrix_σ_eq_five :
    Matrix.trace ((permMatrix h.σ : Matrix V V ℚ)) = 5 := by
  rw [Moore57.trace_permMatrix_eq_fixedVertexCount,
      h.fixedVertexCount_σ_eq_five]
  norm_num

/-- **Phase 3 出力**: ∃ a c : ℕ, 11n = 25 + 15(a - c) かつ a + 10c = 1729.

Higman trace 公式 + spectral decomposition + Q[C_11] 表現論. -/
theorem traceNumber_eq_25_plus_15_mul_dim_form :
    ∃ a c : ℕ,
      (11 * h.traceNumber : ℤ) = 25 + 15 * ((a : ℤ) - c) ∧ a + 10 * c = 1729 := by
  obtain ⟨a₇, c₇, hdim₇, htrace₇⟩ := h.exists_a7_c7_decomp
  obtain ⟨a₈, c₈, hdim₈, htrace₈⟩ := h.exists_aM8_cM8_decomp
  refine ⟨a₇, c₇, ?_, hdim₇⟩
  -- (T_1 : ℚ) = 11 * n
  have hT1 : (h.Tk 1 : ℕ) = 11 * h.traceNumber := h.Tk_one_eq_eleven_mul_traceNumber
  have hT1ℚ : ((h.Tk 1 : ℕ) : ℚ) = ((11 * h.traceNumber : ℕ) : ℚ) := by exact_mod_cast hT1
  -- (T_1 : ℚ) = Matrix.trace (A * P_σ)
  have hT1_trace : ((h.Tk 1 : ℕ) : ℚ) = Matrix.trace (Γ.adjMatrix ℚ * permMatrix h.σ) := by
    rw [Moore57.trace_adjMatrix_mul_permMatrix_eq_adjacentMovedCount Γ h.σ]
    rfl
  -- Spectral decomposition: A * P_σ = 57 E_57 P_σ + 7 E_7 P_σ - 8 E_{-8} P_σ
  have hspec :
      Matrix.trace (Γ.adjMatrix ℚ * permMatrix h.σ) =
        57 * Matrix.trace ((E57Matrix V : Matrix V V ℚ) * permMatrix h.σ) +
        7 * Matrix.trace ((E7Matrix Γ : Matrix V V ℚ) * permMatrix h.σ) -
        8 * Matrix.trace ((EMinus8Matrix Γ : Matrix V V ℚ) * permMatrix h.σ) := by
    rw [Moore57.adjMatrix_eq_spectral_decomp h.isMoore]
    simp only [Matrix.sub_mul, Matrix.add_mul, Matrix.smul_mul,
               Matrix.trace_add, Matrix.trace_sub, Matrix.trace_smul, smul_eq_mul]
  -- trace(E_57 * P_σ) = 1
  have hE57 : Matrix.trace ((E57Matrix V : Matrix V V ℚ) * permMatrix h.σ) = 1 :=
    Moore57.trace_E57Matrix_mul_permMatrix h.isMoore h.σ
  -- trace(P_σ) = 5 = trace((E_57 + E_7 + E_-8) * P_σ) = 1 + (a₇ - c₇) + (a₈ - c₈)
  have hPσ_decomp :
      Matrix.trace ((permMatrix h.σ : Matrix V V ℚ)) =
        Matrix.trace ((E57Matrix V : Matrix V V ℚ) * permMatrix h.σ) +
        Matrix.trace ((E7Matrix Γ : Matrix V V ℚ) * permMatrix h.σ) +
        Matrix.trace ((EMinus8Matrix Γ : Matrix V V ℚ) * permMatrix h.σ) := by
    conv_lhs => rw [← Matrix.one_mul (permMatrix h.σ : Matrix V V ℚ),
      show (1 : Matrix V V ℚ) = E57Matrix V + E7Matrix Γ + EMinus8Matrix Γ from
        (E57_plus_E7_plus_EMinus8_eq_one (V := V) (Γ := Γ)).symm,
      Matrix.add_mul, Matrix.add_mul, Matrix.trace_add, Matrix.trace_add]
  rw [h.trace_permMatrix_σ_eq_five, hE57, htrace₇, htrace₈] at hPσ_decomp
  -- hPσ_decomp : 5 = 1 + (a₇ - c₇) + (a₈ - c₈)
  -- Therefore (a₈ - c₈) = 4 - (a₇ - c₇)
  have h_relation : (a₈ : ℚ) - c₈ = 4 - ((a₇ : ℚ) - c₇) := by linarith
  -- T_1 = 57 + 7(a₇ - c₇) - 8(a₈ - c₈) = 25 + 15(a₇-c₇)
  rw [hT1_trace, hspec, hE57, htrace₇, htrace₈, h_relation] at hT1ℚ
  -- hT1ℚ : 57 * 1 + 7(a₇-c₇) - 8(4-(a₇-c₇)) = ↑(11 * traceNumber)
  push_cast at hT1ℚ
  -- Goal: (11 * h.traceNumber : ℤ) = 25 + 15 * ((a₇ : ℤ) - c₇)
  have h_int : (11 * (h.traceNumber : ℚ)) = 25 + 15 * ((a₇ : ℚ) - c₇) := by linarith
  have h_castℚ : ((11 * h.traceNumber : ℤ) : ℚ) =
      ((25 + 15 * ((a₇ : ℤ) - c₇) : ℤ) : ℚ) := by
    push_cast
    linarith
  exact_mod_cast h_castℚ

/-- **Phase 3 結論**: ∃ s : ℕ, traceNumber = 5 + 15 s. -/
theorem traceNumber_exists_form :
    ∃ s : ℕ, h.traceNumber = 5 + 15 * s := by
  obtain ⟨a, c, h_eq, hdim⟩ := h.traceNumber_eq_25_plus_15_mul_dim_form
  -- (a - c) % 11 = 2 from a + 10c = 1729 ≡ 2 (mod 11)
  have h_mod : ((a : ℤ) - c) % 11 = 2 := by
    -- a + 10c = 1729 ⟹ a - c = a + 10c - 11c = 1729 - 11c
    -- 1729 = 11 * 157 + 2, so 1729 % 11 = 2
    have h1 : (a : ℤ) + 10 * c = 1729 := by exact_mod_cast hdim
    have h2 : (a : ℤ) - c = 1729 - 11 * c := by linarith
    rw [h2]
    omega
  exact Moore57.Order22ActsOnMoore57.traceNumber.eq_five_plus_fifteen_mul_of_modular
    h_eq h_mod

end Order22ActsOnMoore57

end Moore57
