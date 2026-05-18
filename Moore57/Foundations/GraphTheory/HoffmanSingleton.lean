import Mathlib.Combinatorics.SimpleGraph.StronglyRegular
import Mathlib.Combinatorics.SimpleGraph.AdjMatrix
import Mathlib.Combinatorics.SimpleGraph.LapMatrix
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Tactic

/-!
# Hoffman-Singleton classification of SRG(k² + 1, k, 0, 1)

Classical theorem (Hoffman-Singleton 1960): a strongly regular graph with
parameters `(k² + 1, k, 0, 1)` exists only when `k ∈ {0, 1, 2, 3, 7, 57}`.

## Status

* **S1 SRG matrix identity** `A² + A − (k − 1)·I = J`: ✅️ sorry-free.
* **S2 Regular adj-matrix lemmas** `A · J = J · A = k·J`: ✅️ sorry-free.
* **S3 Cubic annihilator** `(A − k·I)(A² + A − (k − 1)·I) = 0`: ✅️ sorry-free.
* **S3 Eigenvalue dichotomy**: ✅️ sorry-free.
* **S4 Hermitian setup + λ_± definitions + distinctness**: ✅️ sorry-free.
* **S4 3-way Finset partition** + multiplicity definitions: ✅️ sorry-free.
* **S4 Trace identity** `m_k k + m_+ λ_+ + m_- λ_- = 0`: ✅️ sorry-free.
* **S4 Discriminant equation** `(m_+ − m_-)√D = k² + 1 − m_k(2k+1)`: ✅️ sorry-free.
* **S5 Case A** (irrational discriminant): ✅️ sorry-free → `k = 2`.
* **S4f Perron multiplicity** `m_k = 1`: ⚠ sorry (requires spectral
  theorem + inner-product orthogonality argument).
* **S6 Case B** (square discriminant): ⚠ sorry (divisibility analysis,
  modular arithmetic over ℤ, depends on `m_k = 1`).
* **S7 Main theorem**: ⚠ sorry (just Case B + assembly).

## Proof outline

`A² + A − (k − 1)·I = J`. Eigenvalues `{k, λ_±}` with `λ_± := (−1 ± √D)/2`,
`D := 4k − 3`. Constraints `m_k + m_+ + m_- = k² + 1`,
`m_k k + m_+ λ_+ + m_- λ_- = 0`.

* Case A (`D` non-square): `√D` irrational ⟹ `m_+ = m_-` and
  `m_k(2k + 1) = k² + 1` ⟹ `(2k + 1) | 5` ⟹ `k ∈ {0, 2}`.
* Case B (`D = (2u+1)²`): assuming `m_k = 1`,
  `(m_+ − m_-)(2u + 1) = (u² + u − 1)k` ⟹ `(2u + 1) | 15`
  ⟹ `u ∈ {0, 1, 2, 7}` ⟹ `k ∈ {1, 3, 7, 57}`.
-/

namespace Moore57

open Matrix BigOperators Finset

variable {W : Type*} [Fintype W] [DecidableEq W]

/-! ## Stage S0: Basic setup -/

/-- Discriminant of the SRG`(k²+1, k, 0, 1)` eigenvalue equation. -/
def srgDiscriminant (k : ℕ) : ℤ := 4 * (k : ℤ) - 3

/-- For SRG`(k²+1, k, 0, 1)`, `|W| ≥ 1`. -/
theorem srg_kk_plus_one_card_pos {G : SimpleGraph W} [DecidableRel G.Adj]
    (hsrg : G.IsSRGWith (k * k + 1) k 0 1) :
    0 < Fintype.card W := by
  rw [hsrg.card]; omega

/-! ## Stage S1: SRG matrix identity -/

/-- The all-ones matrix over `α`. -/
def srgAllOnesMatrix (W : Type*) [Fintype W] (α : Type*) [Zero α] [One α] :
    Matrix W W α := Matrix.of fun _ _ => 1

@[simp] theorem srgAllOnesMatrix_apply {α : Type*} [Zero α] [One α]
    (v w : W) : (srgAllOnesMatrix W α : Matrix W W α) v w = 1 := rfl

theorem srgAllOnesMatrix_isSymm {α : Type*} [Zero α] [One α] :
    (srgAllOnesMatrix W α : Matrix W W α).IsSymm := by
  ext i j; rfl

/-- Complement adjacency matrix equals `J - 1 - A`. -/
theorem compl_adjMatrix_eq_allOnes_sub
    {α : Type*} [DecidableEq α] [AddGroup α] [One α]
    {G : SimpleGraph W} [DecidableRel G.Adj] :
    (Gᶜ).adjMatrix α = srgAllOnesMatrix W α - 1 - G.adjMatrix α := by
  ext v w
  classical
  by_cases hvw : v = w
  · subst hvw
    simp [SimpleGraph.adjMatrix_apply, srgAllOnesMatrix, Matrix.one_apply,
      SimpleGraph.compl_adj]
  · simp only [SimpleGraph.adjMatrix_apply, srgAllOnesMatrix_apply,
      Matrix.sub_apply, Matrix.one_apply_ne hvw, SimpleGraph.compl_adj]
    by_cases hAdj : G.Adj v w
    · simp [hAdj, hvw, hAdj.ne]
    · simp [hAdj, hvw]

/-- **Stage S1**: SRG`(k²+1, k, 0, 1)` matrix identity:
`A² + A − (k − 1)·I = J`. -/
theorem srg_kk_plus_one_matrix_identity
    {α : Type*} [DecidableEq α] [CommRing α]
    {G : SimpleGraph W} [DecidableRel G.Adj] {k : ℕ}
    (hsrg : G.IsSRGWith (k * k + 1) k 0 1) :
    (G.adjMatrix α) ^ 2 + G.adjMatrix α - ((k : α) - 1) • 1 = srgAllOnesMatrix W α := by
  have hmat := hsrg.matrix_eq (α := α)
  rw [compl_adjMatrix_eq_allOnes_sub] at hmat
  -- hmat : A^2 = k • 1 + 0 • A + 1 • (J - 1 - A)  (k • 1 is ℕ-smul)
  simp only [zero_smul, one_smul, add_zero] at hmat
  -- Convert ℕ-smul to α-smul on (k • 1) using Nat.cast_smul_eq_nsmul.
  rw [← Nat.cast_smul_eq_nsmul α k (1 : Matrix W W α)] at hmat
  -- hmat : A^2 = (k : α) • 1 + (J - 1 - A)
  rw [hmat, sub_smul, one_smul]
  -- Goal: (k : α) • 1 + (J - 1 - A) + A - ((k : α) • 1 - 1) = J
  abel

/-! ## Stage S2: Regular-graph identities -/

theorem adjMatrix_mul_srgAllOnesMatrix_of_regular
    {α : Type*} [DecidableEq α] [CommSemiring α]
    {G : SimpleGraph W} [DecidableRel G.Adj]
    {k : ℕ} (hreg : ∀ v, G.degree v = k) :
    G.adjMatrix α * srgAllOnesMatrix W α = (k : α) • srgAllOnesMatrix W α := by
  ext v w
  simp [srgAllOnesMatrix, hreg v]

theorem srgAllOnesMatrix_mul_adjMatrix_of_regular
    {α : Type*} [DecidableEq α] [CommSemiring α]
    {G : SimpleGraph W} [DecidableRel G.Adj]
    {k : ℕ} (hreg : ∀ v, G.degree v = k) :
    srgAllOnesMatrix W α * G.adjMatrix α = (k : α) • srgAllOnesMatrix W α := by
  ext v w
  simp [srgAllOnesMatrix, hreg w]

theorem srgAllOnesMatrix_mul_srgAllOnesMatrix
    {α : Type*} [CommSemiring α] :
    (srgAllOnesMatrix W α) * (srgAllOnesMatrix W α) =
      (Fintype.card W : α) • srgAllOnesMatrix W α := by
  ext v w
  simp [srgAllOnesMatrix, Matrix.mul_apply, Finset.sum_const]

/-! ## Stage S3: Eigenvalue characterization

For SRG`(k²+1, k, 0, 1)`, the cubic `(X - k)(X² + X - (k - 1))` annihilates `A`,
so every (real) eigenvalue of `A` lies in `{k, λ_+, λ_-}` where
`λ_± := (-1 ± √(4k-3))/2`.
-/

/-- **Stage S3.1 — cubic annihilator**: For SRG`(k²+1, k, 0, 1)`,
the matrix `(A - k·I)(A² + A - (k-1)·I) = 0`. -/
theorem srg_kk_plus_one_cubic_eq_zero
    {α : Type*} [DecidableEq α] [CommRing α]
    {G : SimpleGraph W} [DecidableRel G.Adj] {k : ℕ}
    (hsrg : G.IsSRGWith (k * k + 1) k 0 1) :
    (G.adjMatrix α - (k : α) • 1) *
      (G.adjMatrix α ^ 2 + G.adjMatrix α - ((k : α) - 1) • 1) = 0 := by
  rw [srg_kk_plus_one_matrix_identity hsrg]
  -- Goal: (A - k • 1) * J = 0
  rw [sub_mul, smul_mul_assoc, one_mul,
    adjMatrix_mul_srgAllOnesMatrix_of_regular hsrg.regular]
  -- Goal: k • J - k • J = 0
  simp

/-- **Stage S3.2 — eigenvalue dichotomy**:
For SRG`(k²+1, k, 0, 1)`, any real eigenvalue `μ` of `A *ᵥ -` satisfies
`μ = k ∨ μ² + μ - (k - 1) = 0`. -/
theorem srg_kk_plus_one_eigenvalue_dichotomy
    {G : SimpleGraph W} [DecidableRel G.Adj] {k : ℕ}
    (hsrg : G.IsSRGWith (k * k + 1) k 0 1)
    {μ : ℝ} {v : W → ℝ} (hv : v ≠ 0)
    (hev : G.adjMatrix ℝ *ᵥ v = μ • v) :
    μ = k ∨ μ ^ 2 + μ - ((k : ℝ) - 1) = 0 := by
  by_cases hμ : μ ^ 2 + μ - ((k : ℝ) - 1) = 0
  · exact Or.inr hμ
  left
  -- The cubic `(A - k·I)(A² + A - (k-1)·I) = 0` annihilates `A`. Apply to `v`.
  have hcube := srg_kk_plus_one_cubic_eq_zero (α := ℝ) hsrg
  -- Compute action of intermediate factor on `v`.
  have hA2v : (G.adjMatrix ℝ ^ 2) *ᵥ v = μ ^ 2 • v := by
    rw [sq, ← Matrix.mulVec_mulVec, hev, Matrix.mulVec_smul, hev, smul_smul, ← sq]
  have hMid_expand : (μ ^ 2 + μ - ((k : ℝ) - 1)) • v
      = μ ^ 2 • v + μ • v - ((k : ℝ) - 1) • v := by
    rw [sub_smul, add_smul]
  have hMid : (G.adjMatrix ℝ ^ 2 + G.adjMatrix ℝ - ((k : ℝ) - 1) • 1) *ᵥ v
      = (μ ^ 2 + μ - ((k : ℝ) - 1)) • v := by
    rw [Matrix.sub_mulVec, Matrix.add_mulVec, hA2v, hev,
        Matrix.smul_mulVec, Matrix.one_mulVec, hMid_expand]
  -- Now: (A - k • 1) *ᵥ (hMid_value) = 0.
  have hOuter : (G.adjMatrix ℝ - (k : ℝ) • 1) *ᵥ
      ((μ ^ 2 + μ - ((k : ℝ) - 1)) • v) = 0 := by
    rw [← hMid, Matrix.mulVec_mulVec, hcube, Matrix.zero_mulVec]
  rw [Matrix.mulVec_smul] at hOuter
  -- hOuter : (μ² + μ - (k-1)) • ((A - k • 1) *ᵥ v) = 0
  have hAv_sub_expand : (μ - (k : ℝ)) • v = μ • v - (k : ℝ) • v := sub_smul μ k v
  have hAv_sub : (G.adjMatrix ℝ - (k : ℝ) • 1) *ᵥ v = (μ - (k : ℝ)) • v := by
    rw [Matrix.sub_mulVec, hev, Matrix.smul_mulVec, Matrix.one_mulVec, hAv_sub_expand]
  rw [hAv_sub, smul_smul] at hOuter
  -- hOuter : ((μ² + μ - (k-1)) * (μ - k)) • v = 0
  have hcoeff : (μ ^ 2 + μ - ((k : ℝ) - 1)) * (μ - (k : ℝ)) = 0 := by
    rcases smul_eq_zero.mp hOuter with h | h
    · exact h
    · exact absurd h hv
  have : μ - (k : ℝ) = 0 := by
    rcases mul_eq_zero.mp hcoeff with h | h
    · exact absurd h hμ
    · exact h
  linarith

/-! ## Stage S4: Multiplicities and trace identity

For Hermitian `A`, eigenvalues come from `IsHermitian.eigenvalues : W → ℝ`.
Each eigenvalue is in `{k, λ_+, λ_-}`. Define multiplicities by counting.
-/

/-- The Perron eigenvalue's eigenspace is 1-dimensional. Concretely:
if `A v = k v` then `v = c · 𝟙` for some `c : ℝ` (where `𝟙 = const 1`). -/
theorem srg_kk_plus_one_perron_collinear
    {G : SimpleGraph W} [DecidableRel G.Adj] {k : ℕ}
    (hsrg : G.IsSRGWith (k * k + 1) k 0 1)
    {v : W → ℝ} (hev : G.adjMatrix ℝ *ᵥ v = (k : ℝ) • v) :
    ∃ c : ℝ, v = fun _ => c := by
  -- Apply SRG identity to v: (A² + A - (k - 1) • I) v = J v.
  have hid := srg_kk_plus_one_matrix_identity (α := ℝ) hsrg
  have happ : (G.adjMatrix ℝ ^ 2 + G.adjMatrix ℝ - ((k : ℝ) - 1) • 1) *ᵥ v =
      srgAllOnesMatrix W ℝ *ᵥ v := by
    rw [hid]
  -- LHS = (k² + k - (k - 1)) • v = (k² + 1) • v
  have hA2v : (G.adjMatrix ℝ ^ 2) *ᵥ v = (k : ℝ) ^ 2 • v := by
    rw [sq, ← Matrix.mulVec_mulVec, hev, Matrix.mulVec_smul, hev, smul_smul, ← sq]
  have hLHS_expand : ((k : ℝ) ^ 2 + (k : ℝ) - ((k : ℝ) - 1)) • v
      = (k : ℝ) ^ 2 • v + (k : ℝ) • v - ((k : ℝ) - 1) • v := by
    rw [sub_smul, add_smul]
  have hLHS : (G.adjMatrix ℝ ^ 2 + G.adjMatrix ℝ - ((k : ℝ) - 1) • 1) *ᵥ v
      = ((k : ℝ) ^ 2 + 1) • v := by
    rw [Matrix.sub_mulVec, Matrix.add_mulVec, hA2v, hev,
        Matrix.smul_mulVec, Matrix.one_mulVec]
    -- goal: k² • v + k • v - (k - 1) • v = (k² + 1) • v
    have hk1_eq : (k : ℝ) ^ 2 + 1 = (k : ℝ) ^ 2 + (k : ℝ) - ((k : ℝ) - 1) := by ring
    rw [hk1_eq, hLHS_expand]
  -- RHS = srgAllOnesMatrix v = (sum v) • 𝟙
  have hRHS : srgAllOnesMatrix W ℝ *ᵥ v = fun _ => ∑ w, v w := by
    ext i
    simp [srgAllOnesMatrix, Matrix.mulVec, dotProduct]
  rw [hLHS, hRHS] at happ
  -- ((k² + 1) • v) = const (sum v)
  -- ⟹ v = const (sum v / (k² + 1))
  refine ⟨(∑ w, v w) / ((k : ℝ) ^ 2 + 1), funext fun i => ?_⟩
  have hk1 : ((k : ℝ) ^ 2 + 1) ≠ 0 := by positivity
  have hAppI := congrFun happ i
  simp only [Pi.smul_apply, smul_eq_mul] at hAppI
  -- hAppI : (k² + 1) * v i = ∑ w, v w
  field_simp
  linear_combination hAppI

/-- `(k : ℝ) ^ 2 + 1 ≠ 0`. -/
private theorem k_sq_plus_one_ne_zero (k : ℕ) : ((k : ℝ) ^ 2 + 1) ≠ 0 := by positivity

/-! ### S4 Hermitian setup -/

/-- The adjacency matrix of a simple graph over `ℝ` is Hermitian. -/
theorem adjMatrix_real_isHermitian {G : SimpleGraph W} [DecidableRel G.Adj] :
    (G.adjMatrix ℝ).IsHermitian :=
  SimpleGraph.isHermitian_adjMatrix (R := ℝ) (G := G)

/-- Every eigenvalue of `A` (from `IsHermitian.eigenvalues`) satisfies the
dichotomy: equals `k` or is a root of `X² + X - (k - 1)`. -/
theorem srg_kk_plus_one_eigenvalue_classification
    {G : SimpleGraph W} [DecidableRel G.Adj] {k : ℕ}
    (hsrg : G.IsSRGWith (k * k + 1) k 0 1)
    (hHerm : (G.adjMatrix ℝ).IsHermitian) (i : W) :
    hHerm.eigenvalues i = (k : ℝ) ∨
      (hHerm.eigenvalues i) ^ 2 + hHerm.eigenvalues i - ((k : ℝ) - 1) = 0 := by
  have hmv := hHerm.mulVec_eigenvectorBasis i
  have hne_basis : hHerm.eigenvectorBasis i ≠ 0 :=
    hHerm.eigenvectorBasis.orthonormal.ne_zero i
  have hne : ⇑(hHerm.eigenvectorBasis i) ≠ 0 := by
    intro h
    apply hne_basis
    exact (WithLp.ofLp_eq_zero (p := 2)).mp h
  exact srg_kk_plus_one_eigenvalue_dichotomy hsrg hne hmv

/-! ### S4b: Eigenvalue λ_± definitions and m_k = 1 -/

/-- Plus eigenvalue: `λ_+ = (-1 + √(4k-3))/2`. -/
noncomputable def srgLambdaPlus (k : ℕ) : ℝ := (-1 + Real.sqrt (4 * (k : ℝ) - 3)) / 2

/-- Minus eigenvalue: `λ_- = (-1 - √(4k-3))/2`. -/
noncomputable def srgLambdaMinus (k : ℕ) : ℝ := (-1 - Real.sqrt (4 * (k : ℝ) - 3)) / 2

/-- For `k ≥ 1`, `4k - 3 ≥ 1 ≥ 0`, so `√(4k - 3)` is well-defined. -/
private theorem sqrt_disc_sq (k : ℕ) (hk : 1 ≤ k) :
    Real.sqrt (4 * (k : ℝ) - 3) ^ 2 = 4 * (k : ℝ) - 3 := by
  apply Real.sq_sqrt
  have : (1 : ℝ) ≤ k := by exact_mod_cast hk
  linarith

/-- `λ_+` is a root of `X² + X - (k - 1)`. -/
theorem srgLambdaPlus_root (k : ℕ) (hk : 1 ≤ k) :
    (srgLambdaPlus k) ^ 2 + srgLambdaPlus k - ((k : ℝ) - 1) = 0 := by
  unfold srgLambdaPlus
  have hsq := sqrt_disc_sq k hk
  set s := Real.sqrt (4 * (k : ℝ) - 3) with hs_def
  have hrw : ((-1 + s) / 2) ^ 2 + (-1 + s) / 2 - ((k : ℝ) - 1)
      = (s ^ 2 - (4 * (k : ℝ) - 3)) / 4 := by ring
  rw [hrw, hsq]; ring

/-- `λ_-` is a root of `X² + X - (k - 1)`. -/
theorem srgLambdaMinus_root (k : ℕ) (hk : 1 ≤ k) :
    (srgLambdaMinus k) ^ 2 + srgLambdaMinus k - ((k : ℝ) - 1) = 0 := by
  unfold srgLambdaMinus
  have hsq := sqrt_disc_sq k hk
  set s := Real.sqrt (4 * (k : ℝ) - 3) with hs_def
  have hrw : ((-1 - s) / 2) ^ 2 + (-1 - s) / 2 - ((k : ℝ) - 1)
      = (s ^ 2 - (4 * (k : ℝ) - 3)) / 4 := by ring
  rw [hrw, hsq]; ring

/-- The two roots of `X² + X - (k - 1)`. Used in case analysis. -/
theorem quadratic_root_classification (k : ℕ) (hk : 1 ≤ k) (μ : ℝ)
    (h : μ ^ 2 + μ - ((k : ℝ) - 1) = 0) :
    μ = srgLambdaPlus k ∨ μ = srgLambdaMinus k := by
  unfold srgLambdaPlus srgLambdaMinus
  -- μ² + μ - (k - 1) = 0 ⟺ (2μ + 1)² = 4k - 3.
  have hdisc : Real.sqrt (4 * (k : ℝ) - 3) ^ 2 = 4 * (k : ℝ) - 3 := sqrt_disc_sq k hk
  have hsq : (2 * μ + 1) ^ 2 = 4 * (k : ℝ) - 3 := by nlinarith [h]
  have habs : |2 * μ + 1| = Real.sqrt (4 * (k : ℝ) - 3) := by
    rw [← Real.sqrt_sq_eq_abs, hsq]
  rcases abs_eq (Real.sqrt_nonneg _) |>.mp habs with h | h
  · left; linarith
  · right; linarith

/-! ### S4c: Distinctness of {k, λ_+, λ_-} and partition of W -/

/-- `k ≠ λ_+`. Proof: `λ_+ < k` strictly for `k ≥ 1`. -/
theorem k_ne_srgLambdaPlus (k : ℕ) (hk : 1 ≤ k) :
    (k : ℝ) ≠ srgLambdaPlus k := by
  unfold srgLambdaPlus
  intro h
  -- k = (-1 + √(4k-3))/2 ⟹ 2k + 1 = √(4k-3) ⟹ 4k² + 4k + 1 = 4k - 3 ⟹ 4k² = -4.
  have hsqr : (2 * (k : ℝ) + 1) = Real.sqrt (4 * (k : ℝ) - 3) := by linarith
  have hsq : Real.sqrt (4 * (k : ℝ) - 3) ^ 2 = 4 * (k : ℝ) - 3 := sqrt_disc_sq k hk
  have : (2 * (k : ℝ) + 1) ^ 2 = 4 * (k : ℝ) - 3 := by rw [hsqr]; exact hsq
  nlinarith [sq_nonneg ((k : ℝ))]

/-- `k ≠ λ_-`. -/
theorem k_ne_srgLambdaMinus (k : ℕ) (hk : 1 ≤ k) :
    (k : ℝ) ≠ srgLambdaMinus k := by
  unfold srgLambdaMinus
  intro h
  -- k = (-1 - √(4k-3))/2 ⟹ 2k + 1 = -√(4k-3) ≤ 0. But 2k + 1 ≥ 3.
  have hsqr : (2 * (k : ℝ) + 1) = -Real.sqrt (4 * (k : ℝ) - 3) := by linarith
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hnn : (0 : ℝ) ≤ Real.sqrt (4 * (k : ℝ) - 3) := Real.sqrt_nonneg _
  linarith

/-- `λ_+ ≠ λ_-` for `k ≥ 1`. -/
theorem srgLambdaPlus_ne_srgLambdaMinus (k : ℕ) (hk : 1 ≤ k) :
    srgLambdaPlus k ≠ srgLambdaMinus k := by
  unfold srgLambdaPlus srgLambdaMinus
  intro h
  -- (-1 + √D)/2 = (-1 - √D)/2 ⟹ √D = 0 ⟹ D = 0. But D ≥ 1.
  have hsqrt : Real.sqrt (4 * (k : ℝ) - 3) = 0 := by linarith
  have hD : (4 * (k : ℝ) - 3) = 0 := by
    have hsq : Real.sqrt (4 * (k : ℝ) - 3) ^ 2 = 4 * (k : ℝ) - 3 := sqrt_disc_sq k hk
    rw [hsqrt] at hsq
    linarith [hsq]
  have : (1 : ℝ) ≤ k := by exact_mod_cast hk
  linarith

/-! ### S4d: Multiplicities and partition -/

/-- Number of eigenvectors with eigenvalue `k`. -/
noncomputable def srgM_k {G : SimpleGraph W} [DecidableRel G.Adj]
    (hHerm : (G.adjMatrix ℝ).IsHermitian) (k : ℕ) : ℕ :=
  (Finset.univ.filter fun i : W => hHerm.eigenvalues i = (k : ℝ)).card

/-- Number of eigenvectors with eigenvalue `λ_+`. -/
noncomputable def srgM_plus {G : SimpleGraph W} [DecidableRel G.Adj]
    (hHerm : (G.adjMatrix ℝ).IsHermitian) (k : ℕ) : ℕ :=
  (Finset.univ.filter fun i : W => hHerm.eigenvalues i = srgLambdaPlus k).card

/-- Number of eigenvectors with eigenvalue `λ_-`. -/
noncomputable def srgM_minus {G : SimpleGraph W} [DecidableRel G.Adj]
    (hHerm : (G.adjMatrix ℝ).IsHermitian) (k : ℕ) : ℕ :=
  (Finset.univ.filter fun i : W => hHerm.eigenvalues i = srgLambdaMinus k).card

/-! ### S4e: Sum partition by eigenvalue class -/

/-- For `k ≥ 1`, the three filter sets partition `univ`. -/
theorem srgM_sum_eq_card
    {G : SimpleGraph W} [DecidableRel G.Adj] {k : ℕ}
    (hsrg : G.IsSRGWith (k * k + 1) k 0 1) (hk : 1 ≤ k)
    (hHerm : (G.adjMatrix ℝ).IsHermitian) :
    srgM_k hHerm k + srgM_plus hHerm k + srgM_minus hHerm k = Fintype.card W := by
  classical
  have hcover : ∀ i : W, hHerm.eigenvalues i = (k : ℝ) ∨
      hHerm.eigenvalues i = srgLambdaPlus k ∨ hHerm.eigenvalues i = srgLambdaMinus k := by
    intro i
    rcases srg_kk_plus_one_eigenvalue_classification hsrg hHerm i with h | h
    · exact Or.inl h
    · rcases quadratic_root_classification k hk _ h with h | h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)
  have hne_k_p := k_ne_srgLambdaPlus k hk
  have hne_k_m := k_ne_srgLambdaMinus k hk
  have hne_p_m := srgLambdaPlus_ne_srgLambdaMinus k hk
  -- Build a 3-way partition.
  set Sk := (Finset.univ : Finset W).filter (fun i => hHerm.eigenvalues i = (k : ℝ))
  set Sp := (Finset.univ : Finset W).filter (fun i => hHerm.eigenvalues i = srgLambdaPlus k)
  set Sm := (Finset.univ : Finset W).filter (fun i => hHerm.eigenvalues i = srgLambdaMinus k)
  have hSpm_disj : Disjoint Sp Sm := by
    rw [Finset.disjoint_filter]; intros i _ heqp heqm
    exact hne_p_m (heqp.symm.trans heqm)
  have hSk_disj : Disjoint Sk (Sp ∪ Sm) := by
    rw [Finset.disjoint_union_right]
    refine ⟨?_, ?_⟩
    · rw [Finset.disjoint_filter]; intros i _ heqk heqp
      exact hne_k_p (heqk.symm.trans heqp)
    · rw [Finset.disjoint_filter]; intros i _ heqk heqm
      exact hne_k_m (heqk.symm.trans heqm)
  have hUnion : Sk ∪ Sp ∪ Sm = Finset.univ := by
    ext i
    constructor
    · intro _; exact Finset.mem_univ _
    · intro _
      rcases hcover i with h | h | h
      · exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inl
          (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩))))
      · exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inr
          (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩))))
      · exact Finset.mem_union.mpr (Or.inr
          (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩))
  have hSk_Sp_disj : Disjoint Sk Sp := by
    rw [Finset.disjoint_filter]; intros i _ heqk heqp
    exact hne_k_p (heqk.symm.trans heqp)
  have hSk_Sp_Sm_disj : Disjoint (Sk ∪ Sp) Sm := by
    rw [Finset.disjoint_union_left]
    refine ⟨?_, hSpm_disj⟩
    rw [Finset.disjoint_filter]; intros i _ heqk heqm
    exact hne_k_m (heqk.symm.trans heqm)
  have hcard : (Sk ∪ Sp ∪ Sm).card = Sk.card + Sp.card + Sm.card := by
    rw [Finset.card_union_of_disjoint hSk_Sp_Sm_disj,
        Finset.card_union_of_disjoint hSk_Sp_disj]
  rw [show Fintype.card W = (Finset.univ : Finset W).card from rfl, ← hUnion, hcard]
  rfl

/-- Sum of eigenvalues equals trace of A, which is 0. -/
theorem srg_eigenvalues_sum_eq_zero
    {G : SimpleGraph W} [DecidableRel G.Adj]
    (hHerm : (G.adjMatrix ℝ).IsHermitian) :
    ∑ i : W, hHerm.eigenvalues i = 0 := by
  have htr := hHerm.trace_eq_sum_eigenvalues (𝕜 := ℝ)
  rw [SimpleGraph.trace_adjMatrix ℝ G] at htr
  exact_mod_cast htr.symm

/-! ### S4f': Sum of squared eigenvalues via spectral theorem

`trace(A · A) = ∑ (eigenvalues i)²` for any Hermitian `A`. We derive this
from `IsHermitian.spectral_theorem` by computing
`A * A = U · D² · U⁻¹` and taking trace via cyclic permutation.
-/

/-- For a Hermitian real matrix, `trace(A²) = ∑ (eigenvalues i)²`. -/
private theorem trace_sq_eq_sum_eigenvalues_sq
    {A : Matrix W W ℝ} (hHerm : A.IsHermitian) :
    (A * A).trace = ∑ i, (hHerm.eigenvalues i)^2 := by
  have hsp : A = Unitary.conjStarAlgAut ℝ (Matrix W W ℝ) hHerm.eigenvectorUnitary
              (diagonal ((RCLike.ofReal : ℝ → ℝ) ∘ hHerm.eigenvalues)) :=
    hHerm.spectral_theorem
  have hAA : A * A = Unitary.conjStarAlgAut ℝ (Matrix W W ℝ) hHerm.eigenvectorUnitary
              ((diagonal ((RCLike.ofReal : ℝ → ℝ) ∘ hHerm.eigenvalues)) *
               (diagonal ((RCLike.ofReal : ℝ → ℝ) ∘ hHerm.eigenvalues))) := by
    conv_lhs => rw [hsp]
    exact (_root_.map_mul _ _ _).symm
  rw [hAA, Unitary.conjStarAlgAut_apply, Matrix.trace_mul_cycle]
  have hsUU : (star (hHerm.eigenvectorUnitary : Matrix W W ℝ) : Matrix W W ℝ) *
                (hHerm.eigenvectorUnitary : Matrix W W ℝ) = 1 :=
    Unitary.coe_star_mul_self _
  rw [hsUU, Matrix.one_mul, Matrix.diagonal_mul_diagonal, Matrix.trace_diagonal]
  apply Finset.sum_congr rfl
  intros i _
  change ((RCLike.ofReal : ℝ → ℝ) ∘ hHerm.eigenvalues) i *
       ((RCLike.ofReal : ℝ → ℝ) ∘ hHerm.eigenvalues) i =
       (hHerm.eigenvalues i)^2
  simp [Function.comp_apply, pow_two]

/-- Trace of the all-ones matrix over ℝ equals the cardinality. -/
private theorem trace_srgAllOnesMatrix_real :
    (srgAllOnesMatrix W ℝ).trace = (Fintype.card W : ℝ) := by
  unfold Matrix.trace srgAllOnesMatrix
  simp [Finset.card_univ]

/-- For an SRG`(k²+1, k, 0, 1)`, `trace(A²) = (k² + 1) · k` via the SRG
matrix identity `A² + A − (k − 1)·I = J`. -/
private theorem srg_trace_A_sq_eq_nk
    {G : SimpleGraph W} [DecidableRel G.Adj] {k : ℕ}
    (hsrg : G.IsSRGWith (k * k + 1) k 0 1) :
    ((G.adjMatrix ℝ) * (G.adjMatrix ℝ)).trace =
      ((k : ℝ) * (k : ℝ) + 1) * (k : ℝ) := by
  have hid := srg_kk_plus_one_matrix_identity (α := ℝ) hsrg
  -- hid : (G.adjMatrix ℝ)^2 + G.adjMatrix ℝ - (k - 1) • 1 = srgAllOnesMatrix W ℝ
  have hid' : (G.adjMatrix ℝ) * (G.adjMatrix ℝ) + (G.adjMatrix ℝ) -
              ((k : ℝ) - 1) • (1 : Matrix W W ℝ) = srgAllOnesMatrix W ℝ := by
    have h := hid; rw [sq] at h; exact h
  -- A * A = J - A + (k - 1) • 1
  have hA_sq : (G.adjMatrix ℝ) * (G.adjMatrix ℝ) =
                srgAllOnesMatrix W ℝ - G.adjMatrix ℝ + ((k : ℝ) - 1) • (1 : Matrix W W ℝ) := by
    rw [← hid']; abel
  rw [hA_sq]
  rw [Matrix.trace_add, Matrix.trace_sub, trace_srgAllOnesMatrix_real,
      SimpleGraph.trace_adjMatrix ℝ G, Matrix.trace_smul, Matrix.trace_one]
  -- After: card W - 0 + (k - 1) • card W = (k² + 1) * k
  have hcard : (Fintype.card W : ℝ) = (k : ℝ) * (k : ℝ) + 1 := by
    have hh := hsrg.card; rw [hh]; push_cast; ring
  rw [hcard]
  simp [smul_eq_mul]
  ring

/-! ### S4f: Trace partition via eigenvalue classes -/

/-- The trace partition: `m_k · k + m_+ · λ_+ + m_- · λ_- = 0`. -/
theorem srg_trace_partition
    {G : SimpleGraph W} [DecidableRel G.Adj] {k : ℕ}
    (hsrg : G.IsSRGWith (k * k + 1) k 0 1) (hk : 1 ≤ k)
    (hHerm : (G.adjMatrix ℝ).IsHermitian) :
    (srgM_k hHerm k : ℝ) * (k : ℝ)
      + (srgM_plus hHerm k : ℝ) * srgLambdaPlus k
      + (srgM_minus hHerm k : ℝ) * srgLambdaMinus k = 0 := by
  classical
  have hsum := srg_eigenvalues_sum_eq_zero hHerm
  have hcover : ∀ i : W, hHerm.eigenvalues i = (k : ℝ) ∨
      hHerm.eigenvalues i = srgLambdaPlus k ∨ hHerm.eigenvalues i = srgLambdaMinus k := by
    intro i
    rcases srg_kk_plus_one_eigenvalue_classification hsrg hHerm i with h | h
    · exact Or.inl h
    · rcases quadratic_root_classification k hk _ h with h | h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)
  have hne_k_p := k_ne_srgLambdaPlus k hk
  have hne_k_m := k_ne_srgLambdaMinus k hk
  have hne_p_m := srgLambdaPlus_ne_srgLambdaMinus k hk
  set Sk := (Finset.univ : Finset W).filter (fun i => hHerm.eigenvalues i = (k : ℝ))
  set Sp := (Finset.univ : Finset W).filter (fun i => hHerm.eigenvalues i = srgLambdaPlus k)
  set Sm := (Finset.univ : Finset W).filter (fun i => hHerm.eigenvalues i = srgLambdaMinus k)
  have hSpm_disj : Disjoint Sp Sm := by
    rw [Finset.disjoint_filter]; intros i _ heqp heqm
    exact hne_p_m (heqp.symm.trans heqm)
  have hSk_Sp_disj : Disjoint Sk Sp := by
    rw [Finset.disjoint_filter]; intros i _ heqk heqp
    exact hne_k_p (heqk.symm.trans heqp)
  have hSk_Sp_Sm_disj : Disjoint (Sk ∪ Sp) Sm := by
    rw [Finset.disjoint_union_left]
    refine ⟨?_, hSpm_disj⟩
    rw [Finset.disjoint_filter]; intros i _ heqk heqm
    exact hne_k_m (heqk.symm.trans heqm)
  have hUnion : Sk ∪ Sp ∪ Sm = Finset.univ := by
    ext i
    constructor
    · intro _; exact Finset.mem_univ _
    · intro _
      rcases hcover i with h | h | h
      · exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inl
          (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩))))
      · exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inr
          (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩))))
      · exact Finset.mem_union.mpr (Or.inr
          (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩))
  -- Decompose the sum over the partition.
  have hsum_split :
      ∑ i, hHerm.eigenvalues i = ∑ i ∈ Sk, hHerm.eigenvalues i +
        ∑ i ∈ Sp, hHerm.eigenvalues i + ∑ i ∈ Sm, hHerm.eigenvalues i := by
    rw [show ∑ i, hHerm.eigenvalues i =
        ∑ i ∈ Finset.univ, hHerm.eigenvalues i from rfl]
    rw [← hUnion]
    rw [Finset.sum_union hSk_Sp_Sm_disj,
        Finset.sum_union hSk_Sp_disj]
  -- Compute each subsum.
  have hSum_k : ∑ i ∈ Sk, hHerm.eigenvalues i = (Sk.card : ℝ) * (k : ℝ) := by
    rw [Finset.sum_congr rfl
      (g := fun _ => (k : ℝ)) (by intros i hi; exact (Finset.mem_filter.mp hi).2)]
    simp [mul_comm]
  have hSum_p : ∑ i ∈ Sp, hHerm.eigenvalues i = (Sp.card : ℝ) * srgLambdaPlus k := by
    rw [Finset.sum_congr rfl
      (g := fun _ => srgLambdaPlus k) (by intros i hi; exact (Finset.mem_filter.mp hi).2)]
    simp [mul_comm]
  have hSum_m : ∑ i ∈ Sm, hHerm.eigenvalues i = (Sm.card : ℝ) * srgLambdaMinus k := by
    rw [Finset.sum_congr rfl
      (g := fun _ => srgLambdaMinus k) (by intros i hi; exact (Finset.mem_filter.mp hi).2)]
    simp [mul_comm]
  rw [hSum_k, hSum_p, hSum_m] at hsum_split
  rw [hsum] at hsum_split
  -- hsum_split : 0 = m_k * k + m_+ * λ_+ + m_- * λ_-
  -- m_k = Sk.card by definition; similarly for m_+, m_-.
  unfold srgM_k srgM_plus srgM_minus
  linarith

/-! ### S4g: Trace-square partition

Sum of squared eigenvalues, partitioned over the three eigenvalue classes,
yields `m_k k² + m_+ λ_+² + m_- λ_-² = (k² + 1) · k`.
-/

/-- Sum of squared eigenvalues equals `(k² + 1) · k` for SRG`(k²+1, k, 0, 1)`. -/
theorem srg_eigenvalues_sum_sq_eq_nk
    {G : SimpleGraph W} [DecidableRel G.Adj] {k : ℕ}
    (hsrg : G.IsSRGWith (k * k + 1) k 0 1)
    (hHerm : (G.adjMatrix ℝ).IsHermitian) :
    ∑ i : W, (hHerm.eigenvalues i)^2 = ((k : ℝ) * (k : ℝ) + 1) * (k : ℝ) := by
  rw [← trace_sq_eq_sum_eigenvalues_sq hHerm]
  exact srg_trace_A_sq_eq_nk hsrg

/-- Sum-of-squared eigenvalues partition:
`m_k · k² + m_+ · λ_+² + m_- · λ_-² = (k² + 1) · k`. -/
theorem srg_trace_sq_partition
    {G : SimpleGraph W} [DecidableRel G.Adj] {k : ℕ}
    (hsrg : G.IsSRGWith (k * k + 1) k 0 1) (hk : 1 ≤ k)
    (hHerm : (G.adjMatrix ℝ).IsHermitian) :
    (srgM_k hHerm k : ℝ) * ((k : ℝ) * (k : ℝ))
      + (srgM_plus hHerm k : ℝ) * ((srgLambdaPlus k) * (srgLambdaPlus k))
      + (srgM_minus hHerm k : ℝ) * ((srgLambdaMinus k) * (srgLambdaMinus k))
      = ((k : ℝ) * (k : ℝ) + 1) * (k : ℝ) := by
  classical
  have hsum_sq := srg_eigenvalues_sum_sq_eq_nk hsrg hHerm
  have hcover : ∀ i : W, hHerm.eigenvalues i = (k : ℝ) ∨
      hHerm.eigenvalues i = srgLambdaPlus k ∨ hHerm.eigenvalues i = srgLambdaMinus k := by
    intro i
    rcases srg_kk_plus_one_eigenvalue_classification hsrg hHerm i with h | h
    · exact Or.inl h
    · rcases quadratic_root_classification k hk _ h with h | h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)
  have hne_k_p := k_ne_srgLambdaPlus k hk
  have hne_k_m := k_ne_srgLambdaMinus k hk
  have hne_p_m := srgLambdaPlus_ne_srgLambdaMinus k hk
  set Sk := (Finset.univ : Finset W).filter (fun i => hHerm.eigenvalues i = (k : ℝ))
  set Sp := (Finset.univ : Finset W).filter (fun i => hHerm.eigenvalues i = srgLambdaPlus k)
  set Sm := (Finset.univ : Finset W).filter (fun i => hHerm.eigenvalues i = srgLambdaMinus k)
  have hSpm_disj : Disjoint Sp Sm := by
    rw [Finset.disjoint_filter]; intros i _ heqp heqm
    exact hne_p_m (heqp.symm.trans heqm)
  have hSk_Sp_disj : Disjoint Sk Sp := by
    rw [Finset.disjoint_filter]; intros i _ heqk heqp
    exact hne_k_p (heqk.symm.trans heqp)
  have hSk_Sp_Sm_disj : Disjoint (Sk ∪ Sp) Sm := by
    rw [Finset.disjoint_union_left]
    refine ⟨?_, hSpm_disj⟩
    rw [Finset.disjoint_filter]; intros i _ heqk heqm
    exact hne_k_m (heqk.symm.trans heqm)
  have hUnion : Sk ∪ Sp ∪ Sm = Finset.univ := by
    ext i
    constructor
    · intro _; exact Finset.mem_univ _
    · intro _
      rcases hcover i with h | h | h
      · exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inl
          (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩))))
      · exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inr
          (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩))))
      · exact Finset.mem_union.mpr (Or.inr
          (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩))
  have hsum_split :
      ∑ i, (hHerm.eigenvalues i)^2 = ∑ i ∈ Sk, (hHerm.eigenvalues i)^2 +
        ∑ i ∈ Sp, (hHerm.eigenvalues i)^2 + ∑ i ∈ Sm, (hHerm.eigenvalues i)^2 := by
    rw [show ∑ i, (hHerm.eigenvalues i)^2 =
        ∑ i ∈ Finset.univ, (hHerm.eigenvalues i)^2 from rfl]
    rw [← hUnion]
    rw [Finset.sum_union hSk_Sp_Sm_disj,
        Finset.sum_union hSk_Sp_disj]
  have hSum_k : ∑ i ∈ Sk, (hHerm.eigenvalues i)^2 = (Sk.card : ℝ) * ((k : ℝ) * (k : ℝ)) := by
    rw [Finset.sum_congr rfl
      (g := fun _ => (k : ℝ) * (k : ℝ))
      (by intros i hi
          have := (Finset.mem_filter.mp hi).2
          rw [this]; ring)]
    simp [mul_comm]
  have hSum_p : ∑ i ∈ Sp, (hHerm.eigenvalues i)^2 =
                  (Sp.card : ℝ) * (srgLambdaPlus k * srgLambdaPlus k) := by
    rw [Finset.sum_congr rfl
      (g := fun _ => srgLambdaPlus k * srgLambdaPlus k)
      (by intros i hi
          have := (Finset.mem_filter.mp hi).2
          rw [this]; ring)]
    simp [mul_comm]
  have hSum_m : ∑ i ∈ Sm, (hHerm.eigenvalues i)^2 =
                  (Sm.card : ℝ) * (srgLambdaMinus k * srgLambdaMinus k) := by
    rw [Finset.sum_congr rfl
      (g := fun _ => srgLambdaMinus k * srgLambdaMinus k)
      (by intros i hi
          have := (Finset.mem_filter.mp hi).2
          rw [this]; ring)]
    simp [mul_comm]
  rw [hSum_k, hSum_p, hSum_m] at hsum_split
  rw [hsum_sq] at hsum_split
  -- hsum_split : (k² + 1) * k = m_k * k² + m_+ * λ_+² + m_- * λ_-²
  unfold srgM_k srgM_plus srgM_minus
  linarith

/-! ## Stage S5: Irrational case → `k ∈ {0, 2}`

If `D = 4k - 3` is not a perfect square, then `√D` is irrational. The trace
equation `r √D = k² + 1 - m_k (2k + 1)` (with `r = m_+ - m_-`) forces both
sides to be zero, so `m_k (2k + 1) = k² + 1`. Combined with the modular
identity `4(k² + 1) = (2k - 1)(2k + 1) + 5`, we get `(2k + 1) | 5`, so
`2k + 1 ∈ {1, 5}` and `k ∈ {0, 2}`.
-/

/-- Sum of `m_+ + m_- + m_k = k² + 1` as a real-number equation. -/
theorem srgM_sum_eq_card_real
    {G : SimpleGraph W} [DecidableRel G.Adj] {k : ℕ}
    (hsrg : G.IsSRGWith (k * k + 1) k 0 1) (hk : 1 ≤ k)
    (hHerm : (G.adjMatrix ℝ).IsHermitian) :
    (srgM_k hHerm k : ℝ) + (srgM_plus hHerm k : ℝ) + (srgM_minus hHerm k : ℝ)
      = (k : ℝ) * (k : ℝ) + 1 := by
  have h := srgM_sum_eq_card hsrg hk hHerm
  have hcard : (Fintype.card W : ℝ) = (k : ℝ) * (k : ℝ) + 1 := by
    have hh := hsrg.card
    rw [hh]; push_cast; ring
  have : ((srgM_k hHerm k + srgM_plus hHerm k + srgM_minus hHerm k : ℕ) : ℝ)
      = (Fintype.card W : ℝ) := by exact_mod_cast h
  push_cast at this
  rw [hcard] at this
  exact this

/-- The fundamental equation: `r √D = k² + 1 - m_k (2k + 1)` where
`r = m_+ - m_-`. -/
theorem srg_disc_equation
    {G : SimpleGraph W} [DecidableRel G.Adj] {k : ℕ}
    (hsrg : G.IsSRGWith (k * k + 1) k 0 1) (hk : 1 ≤ k)
    (hHerm : (G.adjMatrix ℝ).IsHermitian) :
    ((srgM_plus hHerm k : ℝ) - (srgM_minus hHerm k : ℝ)) *
        Real.sqrt (4 * (k : ℝ) - 3) =
      (k : ℝ) * (k : ℝ) + 1 - (srgM_k hHerm k : ℝ) * (2 * (k : ℝ) + 1) := by
  have htr := srg_trace_partition hsrg hk hHerm
  have hsum := srgM_sum_eq_card_real hsrg hk hHerm
  -- lam_+ = (-1 + sqrt D)/2, lam_- = (-1 - sqrt D)/2.
  have hlp : srgLambdaPlus k = (-1 + Real.sqrt (4 * (k : ℝ) - 3)) / 2 := rfl
  have hlm : srgLambdaMinus k = (-1 - Real.sqrt (4 * (k : ℝ) - 3)) / 2 := rfl
  rw [hlp, hlm] at htr
  linarith [htr, hsum]

/-- If `4k - 3` is not a perfect square (in ℤ), then `√(4k - 3)` is irrational. -/
theorem sqrt_disc_irrational (k : ℕ) (hk : 1 ≤ k)
    (hsq : ¬ IsSquare (4 * (k : ℤ) - 3)) :
    Irrational (Real.sqrt (4 * (k : ℝ) - 3)) := by
  have hnn : (0 : ℤ) ≤ 4 * (k : ℤ) - 3 := by
    have : (1 : ℤ) ≤ k := by exact_mod_cast hk
    linarith
  have heq : Real.sqrt (4 * (k : ℝ) - 3) = Real.sqrt ((4 * (k : ℤ) - 3 : ℤ) : ℝ) := by
    congr 1; push_cast; ring
  rw [heq]
  exact (irrational_sqrt_intCast_iff_of_nonneg hnn).mpr hsq

/-! ## Stage S5: Case A — irrational discriminant -/

/-- If `4k - 3` is not a perfect square, then `m_+ = m_-` and
`m_k (2k + 1) = k² + 1`. -/
theorem srg_case_A_equations
    {G : SimpleGraph W} [DecidableRel G.Adj] {k : ℕ}
    (hsrg : G.IsSRGWith (k * k + 1) k 0 1) (hk : 1 ≤ k)
    (hsq : ¬ IsSquare (4 * (k : ℤ) - 3))
    (hHerm : (G.adjMatrix ℝ).IsHermitian) :
    srgM_plus hHerm k = srgM_minus hHerm k ∧
      (srgM_k hHerm k : ℤ) * (2 * (k : ℤ) + 1) = (k : ℤ) * (k : ℤ) + 1 := by
  have hd := srg_disc_equation hsrg hk hHerm
  have hirr := sqrt_disc_irrational k hk hsq
  -- LHS = r * √D, RHS = integer cast.
  -- If r ≠ 0, LHS irrational; but RHS rational. So r = 0.
  set r := (srgM_plus hHerm k : ℝ) - (srgM_minus hHerm k : ℝ) with hr_def
  have hr_int : ∃ rZ : ℤ, (rZ : ℝ) = r := ⟨(srgM_plus hHerm k : ℤ) - (srgM_minus hHerm k : ℤ),
    by push_cast; rfl⟩
  set rhs := (k : ℝ) * (k : ℝ) + 1 - (srgM_k hHerm k : ℝ) * (2 * (k : ℝ) + 1) with hrhs_def
  have hrhs_int : ∃ rhsZ : ℤ, (rhsZ : ℝ) = rhs :=
    ⟨((k : ℤ) * (k : ℤ) + 1 - (srgM_k hHerm k : ℤ) * (2 * (k : ℤ) + 1)),
      by push_cast; ring⟩
  -- Case 1: r = 0.
  by_cases hr : r = 0
  · refine ⟨?_, ?_⟩
    · have : (srgM_plus hHerm k : ℝ) = (srgM_minus hHerm k : ℝ) := by linarith
      exact_mod_cast this
    · -- 0 = rhs, so k² + 1 - m_k (2k + 1) = 0 over ℝ.
      have hrhs_zero : (k : ℝ) * (k : ℝ) + 1 - (srgM_k hHerm k : ℝ) * (2 * (k : ℝ) + 1) = 0 := by
        have := hd
        rw [hr, zero_mul] at this
        linarith
      -- Cast to ℤ.
      have : (((k : ℤ) * (k : ℤ) + 1 - (srgM_k hHerm k : ℤ) * (2 * (k : ℤ) + 1)) : ℝ) = 0 := by
        push_cast; linarith
      have hZ : (k : ℤ) * (k : ℤ) + 1 - (srgM_k hHerm k : ℤ) * (2 * (k : ℤ) + 1) = 0 := by
        exact_mod_cast this
      linarith
  · -- r ≠ 0: LHS = r * √D irrational (since r is integer-valued nonzero × irrational).
    exfalso
    obtain ⟨rZ, hrZ⟩ := hr_int
    have hrZ_ne : rZ ≠ 0 := by
      intro h
      apply hr
      rw [← hrZ]; exact_mod_cast h
    have hLHS_irr : Irrational (r * Real.sqrt (4 * (k : ℝ) - 3)) := by
      rw [← hrZ]
      exact irrational_intCast_mul_iff.mpr ⟨hrZ_ne, hirr⟩
    obtain ⟨rhsZ, hrhsZ⟩ := hrhs_int
    have hRHS_rat : ¬ Irrational rhs := by
      rw [← hrhsZ]; exact Int.not_irrational rhsZ
    rw [hd] at hLHS_irr
    exact hRHS_rat hLHS_irr

/-! ### S4f: Perron multiplicity m_k = 1

Combining the three identities (sum, trace, trace-square) with the
quadratic equation for `λ_±` yields `m_k · (k² + 1) = k² + 1`, hence
`m_k = 1`. -/

/-- **Perron uniqueness**: `m_k = 1` for `k ≥ 1`.

Derivation: from
* sum identity `m_k + m_+ + m_- = k² + 1` (counting),
* trace identity `m_k · k + m_+ · λ_+ + m_- · λ_- = 0` (trace zero),
* trace-square identity `m_k · k² + m_+ · λ_+² + m_- · λ_-² = (k² + 1) · k`
  (from `trace(A²) = nk`),
* quadratic roots `λ_±² + λ_± − (k − 1) = 0`,

eliminate `m_+ λ_+²`, `m_- λ_-²` (via the quadratic), then `m_+ λ_+ + m_- λ_-`
(via trace), then `m_+ + m_-` (via sum) to obtain `m_k (k² + 1) = k² + 1`.
Dividing by `k² + 1 > 0` gives `m_k = 1`. -/
theorem srgM_k_eq_one
    {G : SimpleGraph W} [DecidableRel G.Adj] {k : ℕ}
    (hsrg : G.IsSRGWith (k * k + 1) k 0 1) (hk : 1 ≤ k)
    (hHerm : (G.adjMatrix ℝ).IsHermitian) :
    srgM_k hHerm k = 1 := by
  have hpart := srg_trace_sq_partition hsrg hk hHerm
  have htrA := srg_trace_partition hsrg hk hHerm
  have hsum := srgM_sum_eq_card_real hsrg hk hHerm
  have hlp := srgLambdaPlus_root k hk
  have hlm := srgLambdaMinus_root k hk
  -- Derive m_k (k² + 1) = k² + 1 via linear combination.
  have hkey : (srgM_k hHerm k : ℝ) * ((k : ℝ) * (k : ℝ) + 1) =
              (k : ℝ) * (k : ℝ) + 1 := by
    linear_combination
      hpart +
        (-((srgM_plus hHerm k : ℝ))) * hlp +
        (-((srgM_minus hHerm k : ℝ))) * hlm +
        htrA +
        (-((k : ℝ) - 1)) * hsum
  -- Divide by k² + 1 > 0.
  have hpos : (0 : ℝ) < (k : ℝ) * (k : ℝ) + 1 := by positivity
  have hmk_real : (srgM_k hHerm k : ℝ) = 1 := by
    have h1 : (srgM_k hHerm k : ℝ) * ((k : ℝ) * (k : ℝ) + 1) =
              1 * ((k : ℝ) * (k : ℝ) + 1) := by linarith
    exact mul_right_cancel₀ (ne_of_gt hpos) h1
  exact_mod_cast hmk_real

/-- Case A main: if `4k - 3` is not a perfect square, `k ∈ {0, 2}`. -/
theorem srg_case_A
    {G : SimpleGraph W} [DecidableRel G.Adj] {k : ℕ}
    (hsrg : G.IsSRGWith (k * k + 1) k 0 1) (hk : 1 ≤ k)
    (hsq : ¬ IsSquare (4 * (k : ℤ) - 3)) :
    k = 2 := by
  -- Apply case A equations.
  have hHerm : (G.adjMatrix ℝ).IsHermitian := adjMatrix_real_isHermitian
  obtain ⟨_, hmk_eq⟩ := srg_case_A_equations hsrg hk hsq hHerm
  -- hmk_eq : m_k * (2k + 1) = k² + 1.
  -- ⟹ (2k + 1) | (k² + 1).
  -- 4 (k² + 1) - (2k - 1)(2k + 1) = 5 ⟹ (2k + 1) | 5.
  -- 2k + 1 ∈ divisors of 5 ∩ ℕ⁺ odd = {1, 5}. k ∈ {0, 2}.
  -- Combined with k ≥ 1: k = 2.
  have hdvd : (2 * (k : ℤ) + 1) ∣ 5 := by
    have hdvd_kk1 : (2 * (k : ℤ) + 1) ∣ ((k : ℤ) * (k : ℤ) + 1) :=
      ⟨srgM_k hHerm k, by linarith⟩
    have hdvd_4 : (2 * (k : ℤ) + 1) ∣ (4 * ((k : ℤ) * (k : ℤ) + 1)) := hdvd_kk1.mul_left 4
    have hdvd_prod : (2 * (k : ℤ) + 1) ∣ ((2 * (k : ℤ) - 1) * (2 * (k : ℤ) + 1)) :=
      ⟨(2 * (k : ℤ) - 1), by ring⟩
    have hdvd_sub : (2 * (k : ℤ) + 1) ∣ (4 * ((k : ℤ) * (k : ℤ) + 1) -
        (2 * (k : ℤ) - 1) * (2 * (k : ℤ) + 1)) := hdvd_4.sub hdvd_prod
    have h_eq : 4 * ((k : ℤ) * (k : ℤ) + 1) -
        (2 * (k : ℤ) - 1) * (2 * (k : ℤ) + 1) = 5 := by ring
    rwa [h_eq] at hdvd_sub
  -- 2k + 1 ≥ 3 (k ≥ 1) and divides 5: only 5.
  have hge : (3 : ℤ) ≤ 2 * (k : ℤ) + 1 := by
    have : (1 : ℤ) ≤ k := by exact_mod_cast hk
    linarith
  have hpos : (0 : ℤ) < 2 * (k : ℤ) + 1 := by linarith
  have hle : (2 * (k : ℤ) + 1) ≤ 5 := Int.le_of_dvd (by norm_num) hdvd
  -- 2k + 1 ∈ {3, 4, 5}, must be 5 to divide 5.
  have h5 : 2 * (k : ℤ) + 1 = 5 := by
    interval_cases h : 2 * (k : ℤ) + 1
    · exact absurd hdvd (by decide)
    · exact absurd hdvd (by decide)
    · rfl
  have : (k : ℤ) = 2 := by linarith
  exact_mod_cast this

/-! ## Stage S6: Case B — square discriminant

With `m_k = 1` and `D = u²` (integer square, `u ≥ 0`), the discriminant
equation reduces to `(m_+ − m_-) · u = k(k − 2)` over `ℤ`, so
`u | k(k − 2)`. The identity `16 k(k − 2) = u⁴ − 2u² − 15` then yields
`u | 15`, so `u ∈ {1, 3, 5, 15}` and `k = (u² + 3)/4 ∈ {1, 3, 7, 57}`. -/
theorem srg_case_B
    {G : SimpleGraph W} [DecidableRel G.Adj] {k : ℕ}
    (hsrg : G.IsSRGWith (k * k + 1) k 0 1) (hk : 1 ≤ k)
    (hsq : IsSquare (4 * (k : ℤ) - 3)) :
    k = 1 ∨ k = 3 ∨ k = 7 ∨ k = 57 := by
  -- Extract integer square root u ≥ 0 with u² = 4k - 3.
  obtain ⟨u₀, hu₀⟩ := hsq
  -- hu₀ : 4 * (k : ℤ) - 3 = u₀ * u₀
  set u : ℤ := |u₀| with hu_def
  have hu_nn : (0 : ℤ) ≤ u := abs_nonneg _
  have hu_sq : u * u = 4 * (k : ℤ) - 3 := by
    change |u₀| * |u₀| = 4 * (k : ℤ) - 3
    rw [abs_mul_abs_self]; exact hu₀.symm
  -- 4k - 3 ≥ 1 for k ≥ 1, so u ≥ 1.
  have h_4k_3_pos : (1 : ℤ) ≤ 4 * (k : ℤ) - 3 := by
    have : (1 : ℤ) ≤ (k : ℤ) := by exact_mod_cast hk
    linarith
  have hu_pos : (1 : ℤ) ≤ u := by
    have h_uu_pos : (1 : ℤ) ≤ u * u := by linarith [hu_sq]
    rcases lt_or_eq_of_le hu_nn with hgt | heq
    · linarith [hgt]
    · exfalso; rw [← heq] at h_uu_pos; norm_num at h_uu_pos
  -- √(4k - 3 : ℝ) = u.
  have hsqrt : Real.sqrt (4 * (k : ℝ) - 3) = (u : ℝ) := by
    have hD_sq : 4 * (k : ℝ) - 3 = ((u : ℝ))^2 := by
      have : ((u * u : ℤ) : ℝ) = ((4 * (k : ℤ) - 3 : ℤ) : ℝ) := by exact_mod_cast hu_sq
      push_cast at this; linarith [this]
    rw [hD_sq, Real.sqrt_sq (by exact_mod_cast hu_nn)]
  -- Use disc equation + m_k = 1.
  have hHerm : (G.adjMatrix ℝ).IsHermitian := adjMatrix_real_isHermitian
  have hd := srg_disc_equation hsrg hk hHerm
  have hmk : srgM_k hHerm k = 1 := srgM_k_eq_one hsrg hk hHerm
  rw [hsqrt] at hd
  have hmk_real : (srgM_k hHerm k : ℝ) = 1 := by exact_mod_cast hmk
  rw [hmk_real] at hd
  -- hd : (m_+ - m_-) · u = k² + 1 - (2k + 1) = k(k - 2) over ℝ.
  -- Cast to ℤ: r * u = k(k - 2) where r := m_+ - m_- ∈ ℤ.
  have hd_int : ((srgM_plus hHerm k : ℤ) - (srgM_minus hHerm k : ℤ)) * u =
                (k : ℤ) * ((k : ℤ) - 2) := by
    have hd_int_real : ((((srgM_plus hHerm k : ℤ) - (srgM_minus hHerm k : ℤ)) * u : ℤ) : ℝ) =
                       (((k : ℤ) * ((k : ℤ) - 2) : ℤ) : ℝ) := by
      push_cast
      linear_combination hd
    exact_mod_cast hd_int_real
  set r : ℤ := (srgM_plus hHerm k : ℤ) - (srgM_minus hHerm k : ℤ) with hr_def
  -- u | k(k - 2).
  have hu_dvd_kk2 : u ∣ ((k : ℤ) * ((k : ℤ) - 2)) := ⟨r, by linarith [hd_int]⟩
  -- u | 16 k(k - 2).
  have hu_dvd_16kk2 : u ∣ (16 * ((k : ℤ) * ((k : ℤ) - 2))) := hu_dvd_kk2.mul_left 16
  -- 16 k(k - 2) = u⁴ - 2u² - 15 via u² = 4k - 3.
  have h16 : 16 * ((k : ℤ) * ((k : ℤ) - 2)) = u * u * (u * u) - 2 * (u * u) - 15 := by
    have h := hu_sq
    linear_combination -(u * u + 4 * (k : ℤ) - 5) * h
  -- u | u⁴ and u | 2u², so u | (u⁴ - 2u²).
  have hu_dvd_u4_sub : u ∣ (u * u * (u * u) - 2 * (u * u)) := by
    have h_u4 : u ∣ (u * u * (u * u)) := ⟨u * (u * u), by ring⟩
    have h_2u2 : u ∣ (2 * (u * u)) := ⟨2 * u, by ring⟩
    exact h_u4.sub h_2u2
  -- u | 15: from u | (u⁴ - 2u²) - 16 k(k - 2) = 15.
  have hu_dvd_15 : u ∣ (15 : ℤ) := by
    have hkey : (u * u * (u * u) - 2 * (u * u)) - 16 * ((k : ℤ) * ((k : ℤ) - 2)) = 15 := by
      linarith [h16]
    have : u ∣ ((u * u * (u * u) - 2 * (u * u)) - 16 * ((k : ℤ) * ((k : ℤ) - 2))) :=
      hu_dvd_u4_sub.sub hu_dvd_16kk2
    rwa [hkey] at this
  -- u ≤ 15.
  have hu_le_15 : u ≤ 15 := Int.le_of_dvd (by norm_num) hu_dvd_15
  -- Case analysis on u ∈ {1, 2, ..., 15}; only divisors of 15 are possible.
  interval_cases u
  · -- u = 1: 4k - 3 = 1, k = 1.
    have hk1 : (4 : ℤ) * (k : ℤ) - 3 = 1 := by linarith [hu_sq]
    have : (k : ℤ) = 1 := by linarith
    exact Or.inl (by exact_mod_cast this)
  · exact absurd hu_dvd_15 (by decide) -- u = 2
  · -- u = 3: 4k - 3 = 9, k = 3.
    have hk3 : (4 : ℤ) * (k : ℤ) - 3 = 9 := by linarith [hu_sq]
    have : (k : ℤ) = 3 := by linarith
    exact Or.inr (Or.inl (by exact_mod_cast this))
  · exact absurd hu_dvd_15 (by decide) -- u = 4
  · -- u = 5: 4k - 3 = 25, k = 7.
    have hk7 : (4 : ℤ) * (k : ℤ) - 3 = 25 := by linarith [hu_sq]
    have : (k : ℤ) = 7 := by linarith
    exact Or.inr (Or.inr (Or.inl (by exact_mod_cast this)))
  · exact absurd hu_dvd_15 (by decide) -- u = 6
  · exact absurd hu_dvd_15 (by decide) -- u = 7
  · exact absurd hu_dvd_15 (by decide) -- u = 8
  · exact absurd hu_dvd_15 (by decide) -- u = 9
  · exact absurd hu_dvd_15 (by decide) -- u = 10
  · exact absurd hu_dvd_15 (by decide) -- u = 11
  · exact absurd hu_dvd_15 (by decide) -- u = 12
  · exact absurd hu_dvd_15 (by decide) -- u = 13
  · exact absurd hu_dvd_15 (by decide) -- u = 14
  · -- u = 15: 4k - 3 = 225, k = 57.
    have hk57 : (4 : ℤ) * (k : ℤ) - 3 = 225 := by linarith [hu_sq]
    have : (k : ℤ) = 57 := by linarith
    exact Or.inr (Or.inr (Or.inr (by exact_mod_cast this)))

/-! ## Stage S7: Main theorem -/

/-- **Hoffman-Singleton classification** (local form for SRG(k²+1, k, 0, 1)).

Currently uses sorries for:
* `srgM_k_eq_one` (Perron multiplicity uniqueness — spectral theorem
  orthogonality).
* `srg_case_B` (modular arithmetic for the square-discriminant case). -/
theorem srg_k_sq_plus_one_degree_classification'
    {W : Type*} [Fintype W]
    (G : SimpleGraph W) [DecidableRel G.Adj]
    (k : ℕ)
    (hsrg : G.IsSRGWith (k * k + 1) k 0 1) :
    k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 7 ∨ k = 57 := by
  classical
  by_cases hk0 : k = 0
  · exact Or.inl hk0
  have hk : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hk0
  by_cases hsq : IsSquare (4 * (k : ℤ) - 3)
  · -- Square discriminant: Case B.
    rcases srg_case_B hsrg hk hsq with h | h | h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))
  · -- Not a square: Case A.
    have hk2 := srg_case_A hsrg hk hsq
    exact Or.inr (Or.inr (Or.inl hk2))

end Moore57
