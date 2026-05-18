import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Algebra.Module.Submodule.Range

/-!
# Jordan partition monotonicity

For a linear endomorphism `T : V → V` of a finite-dimensional vector space,
the function `j ↦ finrank ker(T^j)` is **concave**:
`finrank ker(T^{j+1}) + finrank ker(T^{j-1}) ≤ 2 · finrank ker(T^j)` for `j ≥ 1`.

Equivalently, `μ_j := finrank ker(T^j) - finrank ker(T^{j-1})` is non-increasing in `j`.

Classical fact, proved via the injection
`ker(T^{j+1})/ker(T^j) ↪ ker(T^j)/ker(T^{j-1})` induced by `T`.

Main result: `Moore57.LinearAlgebra.finrank_ker_pow_concave`.
-/

namespace Moore57.LinearAlgebra

open LinearMap Submodule Module

variable {F V : Type*} [Field F] [AddCommGroup V] [Module F V]

/-- `ker(T^a) ⊆ ker(T^b)` for `a ≤ b`. -/
lemma ker_pow_le_of_le (T : V →ₗ[F] V) {a b : ℕ} (hab : a ≤ b) :
    LinearMap.ker (T^a) ≤ LinearMap.ker (T^b) :=
  T.iterateKer.monotone hab

/-- `ker(T^j) ⊆ ker(T^{j+1})`: 標準的 kernel filtration. -/
lemma ker_pow_le_succ (T : V →ₗ[F] V) (j : ℕ) :
    LinearMap.ker (T^j) ≤ LinearMap.ker (T^(j+1)) :=
  ker_pow_le_of_le T (Nat.le_succ j)

/-- `T^j (T v) = T^(j+1) v`. (Just `pow_succ` rephrased.) -/
lemma pow_apply_T (T : V →ₗ[F] V) (j : ℕ) (v : V) :
    (T^j) (T v) = (T^(j+1)) v := by
  rw [pow_succ, Module.End.mul_apply]

/-- 鍵となる線形写像: `φ : ker(T^{j+1}) → V ⧸ ker(T^{j-1})`, `v ↦ [T v]`. -/
noncomputable def jordanQuotMap (T : V →ₗ[F] V) (j : ℕ) :
    (LinearMap.ker (T^(j+1))) →ₗ[F] V ⧸ LinearMap.ker (T^(j-1)) :=
  (Submodule.mkQ (LinearMap.ker (T^(j-1)))) ∘ₗ T ∘ₗ
    (LinearMap.ker (T^(j+1))).subtype

/-- `ker φ = K_j` (に対応する `K_{j+1}` の部分加群). -/
lemma ker_jordanQuotMap (T : V →ₗ[F] V) {j : ℕ} (hj : 1 ≤ j) :
    LinearMap.ker (jordanQuotMap T j) =
      Submodule.comap (LinearMap.ker (T^(j+1))).subtype (LinearMap.ker (T^j)) := by
  have hj_eq : (j - 1) + 1 = j := Nat.sub_add_cancel hj
  ext ⟨v, hv_in⟩
  -- 目標を「T^(j-1) (T v) = 0 ↔ T^j v = 0」に reduce
  have hgoal_iff : (T^(j-1)) (T v) = 0 ↔ (T^j) v = 0 := by
    rw [pow_apply_T, hj_eq]
  constructor
  · intro h
    -- h : ⟨v, hv_in⟩ ∈ ker φ
    simp only [LinearMap.mem_ker, jordanQuotMap, LinearMap.coe_comp,
               Function.comp_apply, Submodule.coe_subtype,
               Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero,
               LinearMap.mem_ker] at h
    -- h : T^(j-1) (T v) = 0
    rw [Submodule.mem_comap, Submodule.coe_subtype, LinearMap.mem_ker]
    -- 目標: T^j v = 0
    exact hgoal_iff.mp h
  · intro h
    rw [Submodule.mem_comap, Submodule.coe_subtype, LinearMap.mem_ker] at h
    -- h : T^j v = 0
    simp only [LinearMap.mem_ker, jordanQuotMap, LinearMap.coe_comp,
               Function.comp_apply, Submodule.coe_subtype,
               Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero,
               LinearMap.mem_ker]
    -- 目標: T^(j-1) (T v) = 0
    exact hgoal_iff.mpr h

/-- `range φ` ⊆ `(ker(T^j) → V ⧸ ker(T^{j-1}))` の像. -/
lemma range_jordanQuotMap_le (T : V →ₗ[F] V) (j : ℕ) :
    LinearMap.range (jordanQuotMap T j) ≤
      Submodule.map (Submodule.mkQ (LinearMap.ker (T^(j-1))))
        (LinearMap.ker (T^j)) := by
  rintro _ ⟨⟨v, hv_in⟩, rfl⟩
  -- v ∈ ker(T^(j+1)), 目標: φ ⟨v, ...⟩ ∈ map mkQ (ker(T^j))
  -- T v ∈ ker(T^j) を示せばよい
  have hTv : T v ∈ LinearMap.ker (T^j) := by
    rw [LinearMap.mem_ker]
    rw [LinearMap.mem_ker] at hv_in
    rw [pow_apply_T]
    exact hv_in
  refine ⟨T v, hTv, ?_⟩
  simp [jordanQuotMap]

section FiniteDim

variable [FiniteDimensional F V]

/-- `finrank (Submodule.map mkQ K_j) = finrank K_j - finrank K_{j-1}`. -/
lemma finrank_map_mkQ_ker (T : V →ₗ[F] V) (j : ℕ) :
    finrank F (Submodule.map (Submodule.mkQ (LinearMap.ker (T^(j-1))))
        (LinearMap.ker (T^j))) =
      finrank F (LinearMap.ker (T^j)) - finrank F (LinearMap.ker (T^(j-1))) := by
  have h_le : LinearMap.ker (T^(j-1)) ≤ LinearMap.ker (T^j) :=
    ker_pow_le_of_le T (Nat.sub_le j 1)
  -- `Submodule.map (mkQ S) T` の finrank は `T ⧸ (S ∩ T)` の finrank に等しい.
  -- かつ S ⊆ T なら `T ⧸ S` の finrank は `finrank T - finrank S`.
  -- Mathlib: Submodule.finrank_quotient.
  -- map_mkQ K_j は K_j / (K_{j-1} ∩ K_j) = K_j / K_{j-1} と equiv.
  -- このための equiv は Submodule.quotientEquivOfLE などにある.
  have : LinearMap.range
      ((Submodule.mkQ (LinearMap.ker (T^(j-1)))) ∘ₗ
        (LinearMap.ker (T^j)).subtype) =
      Submodule.map (Submodule.mkQ (LinearMap.ker (T^(j-1))))
        (LinearMap.ker (T^j)) := by
    rw [LinearMap.range_comp]
    congr 1
    exact (Submodule.range_subtype _)
  rw [← this]
  -- finrank range = finrank domain - finrank ker
  rw [← LinearMap.finrank_range_add_finrank_ker
    ((Submodule.mkQ (LinearMap.ker (T^(j-1)))) ∘ₗ (LinearMap.ker (T^j)).subtype)]
  -- ker of this composition = preimage of (ker mkQ) in K_j = K_{j-1} (since K_{j-1} ⊆ K_j)
  have h_ker_eq : LinearMap.ker
      ((Submodule.mkQ (LinearMap.ker (T^(j-1)))) ∘ₗ
        (LinearMap.ker (T^j)).subtype) =
      Submodule.comap (LinearMap.ker (T^j)).subtype (LinearMap.ker (T^(j-1))) := by
    ext ⟨v, hv⟩
    simp [Submodule.Quotient.mk_eq_zero, Submodule.mem_comap]
  rw [h_ker_eq]
  have h_finrank_comap : finrank F
      (Submodule.comap (LinearMap.ker (T^j)).subtype (LinearMap.ker (T^(j-1)))) =
      finrank F (LinearMap.ker (T^(j-1))) := by
    exact (Submodule.comapSubtypeEquivOfLe h_le).finrank_eq
  rw [h_finrank_comap]
  omega

/-- 主結果: `j ↦ finrank ker(T^j)` の凹性.
`finrank ker(T^{j+1}) + finrank ker(T^{j-1}) ≤ 2 · finrank ker(T^j)`. -/
theorem finrank_ker_pow_concave (T : V →ₗ[F] V) {j : ℕ} (hj : 1 ≤ j) :
    finrank F (LinearMap.ker (T^(j+1))) + finrank F (LinearMap.ker (T^(j-1))) ≤
      2 * finrank F (LinearMap.ker (T^j)) := by
  -- φ := jordanQuotMap T j
  set φ := jordanQuotMap T j with hφ_def
  -- rank-nullity: finrank K_{j+1} = finrank (ker φ) + finrank (range φ).
  have h_rk_null :=
    LinearMap.finrank_range_add_finrank_ker (f := φ)
  -- finrank (ker φ) = finrank K_j
  have h_ker : finrank F (LinearMap.ker φ) = finrank F (LinearMap.ker (T^j)) := by
    rw [ker_jordanQuotMap T hj]
    exact (Submodule.comapSubtypeEquivOfLe (ker_pow_le_succ T j)).finrank_eq
  -- finrank (range φ) ≤ finrank K_j - finrank K_{j-1}
  have h_K_le : finrank F (LinearMap.ker (T^(j-1))) ≤ finrank F (LinearMap.ker (T^j)) :=
    Submodule.finrank_mono (ker_pow_le_of_le T (Nat.sub_le j 1))
  have h_rng : finrank F (LinearMap.range φ) ≤
      finrank F (LinearMap.ker (T^j)) - finrank F (LinearMap.ker (T^(j-1))) := by
    have h_sub := range_jordanQuotMap_le T j
    calc finrank F (LinearMap.range φ)
        ≤ finrank F (Submodule.map (Submodule.mkQ (LinearMap.ker (T^(j-1))))
            (LinearMap.ker (T^j))) :=
          Submodule.finrank_mono h_sub
      _ = finrank F (LinearMap.ker (T^j)) -
            finrank F (LinearMap.ker (T^(j-1))) :=
          finrank_map_mkQ_ker T j
  -- 組み合わせ
  omega

/-- `μ_j := finrank ker(T^j) - finrank ker(T^{j-1})` の単調性形.
`μ_{j+1} ≤ μ_j` (j ≥ 1 で). -/
theorem mu_succ_le_mu (T : V →ₗ[F] V) {j : ℕ} (hj : 1 ≤ j) :
    finrank F (LinearMap.ker (T^(j+1))) - finrank F (LinearMap.ker (T^j)) ≤
      finrank F (LinearMap.ker (T^j)) - finrank F (LinearMap.ker (T^(j-1))) := by
  have h := finrank_ker_pow_concave T hj
  have h_mono : finrank F (LinearMap.ker (T^(j-1))) ≤ finrank F (LinearMap.ker (T^j)) :=
    Submodule.finrank_mono (ker_pow_le_of_le T (Nat.sub_le j 1))
  have h_mono2 : finrank F (LinearMap.ker (T^j)) ≤ finrank F (LinearMap.ker (T^(j+1))) :=
    Submodule.finrank_mono (ker_pow_le_succ T j)
  omega

end FiniteDim

/-! ## Linearity forcing: pure ℕ formulation

LinearMap の `HPow` 合成を回避するため, pure ℕ 関数として定式化. -/

/-- **Linearity forcing (pure ℕ form)**: ℕ-valued concave function with endpoint
values + 整合性条件 ⟹ 線形.

* `f : ℕ → ℕ` concave (`f (k+1) + f (k-1) ≤ 2 * f k` for `k ≥ 1`),
* `f(0) = 0`, `f(1) = α`, `f(N-1) = β`, `f(N) = γ`,
* `β ≤ γ`, integrity: `α + (N - 1) * (γ - β) = γ`.
* 結論: `f(j) = α + (j - 1) * (γ - β)` for `j ∈ [1, N]`. -/
theorem concave_linearity_forcing
    (f : ℕ → ℕ) {N α β γ : ℕ}
    (hN : 1 ≤ N)
    (hf_concave : ∀ k, 1 ≤ k → f (k + 1) + f (k - 1) ≤ 2 * f k)
    (_hf_mono : ∀ k, f k ≤ f (k + 1))
    (hf_0 : f 0 = 0)
    (hf_1 : f 1 = α)
    (hf_Nm1 : f (N - 1) = β)
    (hf_N : f N = γ)
    (h_consistency : α + (N - 1) * (γ - β) = γ)
    (hβγ : β ≤ γ)
    {j : ℕ} (hj : 1 ≤ j) (hj_le : j ≤ N) :
    f j = α + (j - 1) * (γ - β) := by
  classical
  -- m_k := f(k+1) - f(k) (ℤ) 非増加
  have h_m_anti : ∀ a b : ℕ, a ≤ b →
      (f (b+1) : ℤ) - f b ≤ (f (a+1) : ℤ) - f a := by
    intro a b hab
    induction b, hab using Nat.le_induction with
    | base => exact le_refl _
    | succ b _ ih =>
      have h_step : (f (b+2) : ℤ) - f (b+1) ≤ (f (b+1) : ℤ) - f b := by
        have hb1 : 1 ≤ b + 1 := Nat.succ_pos b
        have h_conc := hf_concave (b+1) hb1
        have heq : b + 1 - 1 = b := by omega
        rw [heq, show b + 1 + 1 = b + 2 from rfl] at h_conc
        omega
      linarith
  -- m_{N-1} = γ - β
  have h_m_Nm1 : (f N : ℤ) - f (N-1) = (γ : ℤ) - β := by
    rw [hf_N, hf_Nm1]
  -- ∀ k ≤ N - 1, m_k ≥ γ - β
  have h_m_lb : ∀ k : ℕ, k ≤ N - 1 →
      ((γ : ℤ) - β) ≤ (f (k+1) : ℤ) - f k := by
    intro k hk
    have h_app := h_m_anti k (N-1) hk
    have hN_eq : N - 1 + 1 = N := Nat.sub_add_cancel hN
    rw [hN_eq] at h_app
    linarith [h_m_Nm1]
  -- Telescope
  have h_telescope : ∀ n : ℕ,
      (f n : ℤ) = ∑ i ∈ Finset.range n, ((f (i+1) : ℤ) - f i) := by
    intro n
    induction n with
    | zero =>
      simp only [Finset.range_zero, Finset.sum_empty]
      exact_mod_cast hf_0
    | succ n ih => rw [Finset.sum_range_succ]; linarith
  -- range j = insert 0 (Ico 1 j)
  have h_range_split : ∀ n : ℕ, 1 ≤ n →
      Finset.range n = insert 0 (Finset.Ico 1 n) := by
    intro n hn
    ext k
    simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Ico]
    omega
  -- ∑_{k ∈ Ico 1 N} m_k = γ - α
  have h_sum_Ico :
      ∑ k ∈ Finset.Ico 1 N, ((f (k+1) : ℤ) - f k) = (γ : ℤ) - α := by
    have h_tot := h_telescope N
    rw [h_range_split N hN, Finset.sum_insert (by simp)] at h_tot
    have hfN_int : (f N : ℤ) = γ := by exact_mod_cast hf_N
    have hf1_int : (f 1 : ℤ) = α := by exact_mod_cast hf_1
    have hf0_int : (f 0 : ℤ) = 0 := by exact_mod_cast hf_0
    linarith
  -- (N - 1) * (γ - β) = γ - α
  have h_consistency_int : ((N - 1 : ℕ) : ℤ) * ((γ : ℤ) - β) = (γ : ℤ) - α := by
    have h1 : ((N - 1 : ℕ) : ℤ) = (N : ℤ) - 1 := by
      have := Nat.cast_sub (R := ℤ) hN; simpa using this
    have h2 : ((γ - β : ℕ) : ℤ) = (γ : ℤ) - β := by
      have := Nat.cast_sub (R := ℤ) hβγ; simpa using this
    have h_full : ((α + (N - 1) * (γ - β) : ℕ) : ℤ) = (γ : ℤ) := by
      exact_mod_cast h_consistency
    push_cast at h_full
    rw [h1, h2] at h_full
    rw [h1]; linarith
  -- 各 m_k = γ - β for k ∈ Ico 1 N
  have h_m_eq : ∀ k ∈ Finset.Ico 1 N, (f (k+1) : ℤ) - f k = (γ : ℤ) - β := by
    have h_card_Ico : (Finset.Ico 1 N).card = N - 1 := Nat.card_Ico 1 N
    have h_each_nn : ∀ k ∈ Finset.Ico 1 N,
        (0 : ℤ) ≤ ((f (k+1) : ℤ) - f k - ((γ : ℤ) - β)) := by
      intro k hk
      rw [Finset.mem_Ico] at hk
      have := h_m_lb k (by omega)
      linarith
    have h_sum_diff :
        ∑ k ∈ Finset.Ico 1 N, ((f (k+1) : ℤ) - f k - ((γ : ℤ) - β)) = 0 := by
      rw [Finset.sum_sub_distrib, Finset.sum_const, h_card_Ico, h_sum_Ico,
          nsmul_eq_mul]
      linarith [h_consistency_int]
    have h_each_zero := (Finset.sum_eq_zero_iff_of_nonneg h_each_nn).mp h_sum_diff
    intro k hk
    have := h_each_zero k hk
    linarith
  -- 結論: f(j) = α + (j - 1) * (γ - β)
  have h_tel_j := h_telescope j
  rw [h_range_split j hj, Finset.sum_insert (by simp)] at h_tel_j
  have hf0_int : (f 0 : ℤ) = 0 := by exact_mod_cast hf_0
  have hf1_int : (f 1 : ℤ) = α := by exact_mod_cast hf_1
  have h_sum_j :
      ∑ k ∈ Finset.Ico 1 j, ((f (k+1) : ℤ) - f k) =
        ((j - 1 : ℕ) : ℤ) * ((γ : ℤ) - β) := by
    have h_each : ∀ k ∈ Finset.Ico 1 j,
        (f (k+1) : ℤ) - f k = (γ : ℤ) - β := by
      intro k hk
      have hk' : k ∈ Finset.Ico 1 N := by
        rw [Finset.mem_Ico] at hk ⊢; omega
      exact h_m_eq k hk'
    rw [Finset.sum_congr rfl h_each, Finset.sum_const, Nat.card_Ico]
    ring
  rw [h_sum_j] at h_tel_j
  have h_d_j_int : (f j : ℤ) = α + ((j - 1 : ℕ) : ℤ) * ((γ : ℤ) - β) := by
    linarith
  -- Cast back to ℕ
  have h_cast_γβ : ((γ - β : ℕ) : ℤ) = (γ : ℤ) - β := by
    have := Nat.cast_sub (R := ℤ) hβγ; simpa using this
  zify [show (j - 1 : ℕ) * (γ - β) = ((j - 1) * (γ - β) : ℕ) from rfl]
  rw [h_cast_γβ]
  linarith

end Moore57.LinearAlgebra
