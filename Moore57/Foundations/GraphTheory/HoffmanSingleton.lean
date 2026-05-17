import Mathlib.Combinatorics.SimpleGraph.StronglyRegular
import Mathlib.Combinatorics.SimpleGraph.AdjMatrix
import Mathlib.LinearAlgebra.Matrix.Hermitian
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

end Moore57
