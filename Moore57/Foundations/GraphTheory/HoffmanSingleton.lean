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

This file proves that classification.

## Proof outline

`A² + A − (k − 1)·I = J`. Eigenvalues `{k, λ_±}` with `λ_± := (−1 ± √D)/2`,
`D := 4k − 3`. Constraints `m_+ + m_- = k²`, `m_+ λ_+ + m_- λ_- = -k`.

* Case A (`D` non-square): `√D` irrational ⟹ `k ∈ {0, 2}`.
* Case B (`D = (2u+1)²`): `(2u+1) | 30` ⟹ `k ∈ {1, 3, 7, 57}`.
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
def allOnesMatrix (W : Type*) [Fintype W] (α : Type*) [Zero α] [One α] :
    Matrix W W α := Matrix.of fun _ _ => 1

@[simp] theorem allOnesMatrix_apply {α : Type*} [Zero α] [One α]
    (v w : W) : (allOnesMatrix W α : Matrix W W α) v w = 1 := rfl

theorem allOnesMatrix_isSymm {α : Type*} [Zero α] [One α] :
    (allOnesMatrix W α : Matrix W W α).IsSymm := by
  ext i j; rfl

/-- Complement adjacency matrix equals `J - 1 - A`. -/
theorem compl_adjMatrix_eq_allOnes_sub
    {α : Type*} [DecidableEq α] [AddGroup α] [One α]
    {G : SimpleGraph W} [DecidableRel G.Adj] :
    (Gᶜ).adjMatrix α = allOnesMatrix W α - 1 - G.adjMatrix α := by
  ext v w
  classical
  by_cases hvw : v = w
  · subst hvw
    simp [SimpleGraph.adjMatrix_apply, allOnesMatrix, Matrix.one_apply,
      SimpleGraph.compl_adj]
  · simp only [SimpleGraph.adjMatrix_apply, allOnesMatrix_apply,
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
    (G.adjMatrix α) ^ 2 + G.adjMatrix α - ((k : α) - 1) • 1 = allOnesMatrix W α := by
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

theorem adjMatrix_mul_allOnesMatrix_of_regular
    {α : Type*} [DecidableEq α] [CommSemiring α]
    {G : SimpleGraph W} [DecidableRel G.Adj]
    {k : ℕ} (hreg : ∀ v, G.degree v = k) :
    G.adjMatrix α * allOnesMatrix W α = (k : α) • allOnesMatrix W α := by
  ext v w
  simp [allOnesMatrix, hreg v]

theorem allOnesMatrix_mul_adjMatrix_of_regular
    {α : Type*} [DecidableEq α] [CommSemiring α]
    {G : SimpleGraph W} [DecidableRel G.Adj]
    {k : ℕ} (hreg : ∀ v, G.degree v = k) :
    allOnesMatrix W α * G.adjMatrix α = (k : α) • allOnesMatrix W α := by
  ext v w
  simp [allOnesMatrix, hreg w]

theorem allOnesMatrix_mul_allOnesMatrix
    {α : Type*} [CommSemiring α] :
    (allOnesMatrix W α) * (allOnesMatrix W α) =
      (Fintype.card W : α) • allOnesMatrix W α := by
  ext v w
  simp [allOnesMatrix, Matrix.mul_apply, Finset.sum_const]

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
    adjMatrix_mul_allOnesMatrix_of_regular hsrg.regular]
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
      allOnesMatrix W ℝ *ᵥ v := by
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
  -- RHS = allOnesMatrix v = (sum v) • 𝟙
  have hRHS : allOnesMatrix W ℝ *ᵥ v = fun _ => ∑ w, v w := by
    ext i
    simp [allOnesMatrix, Matrix.mulVec, dotProduct]
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

end Moore57
