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

end Moore57.LinearAlgebra
