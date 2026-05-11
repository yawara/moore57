import Moore57.Moore57Graph.Moore57Definition

/-!
# Permutation commutation lemmas for the Moore57 trace matrices

This file keeps the matrix-commutation facts used by the trace pipeline separate
from the trace computations themselves.
-/

namespace Moore57

section HigmanTrace

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Left multiplication by `permMatrix σ` permutes rows by `σ.symm`. -/
theorem permMatrix_mul_apply (σ : Equiv.Perm V) (M : Matrix V V ℚ) (v w : V) :
    (permMatrix σ * M) v w = M (σ.symm v) w := by
  classical
  rw [Matrix.mul_apply]
  calc
    ∑ u : V, permMatrix σ v u * M u w
        = permMatrix σ v (σ.symm v) * M (σ.symm v) w := by
          refine Finset.sum_eq_single (σ.symm v) ?_ ?_
          · intro u _ hu
            have hne : σ.symm v ≠ u := hu.symm
            simp [permMatrix, hne]
          · intro h
            exact False.elim (h (Finset.mem_univ _))
    _ = M (σ.symm v) w := by
          simp [permMatrix]

/-- A graph automorphism commutes with the adjacency matrix, in permutation-matrix form. -/
theorem adjMatrix_mul_permMatrix_eq_permMatrix_mul_adjMatrix
    (Γ : SimpleGraph V) [DecidableRel Γ.Adj] (σ : Equiv.Perm V)
    (haut : ∀ v w, Γ.Adj v w ↔ Γ.Adj (σ v) (σ w)) :
    Γ.adjMatrix ℚ * permMatrix σ = permMatrix σ * Γ.adjMatrix ℚ := by
  classical
  ext v w
  rw [mul_permMatrix_apply, permMatrix_mul_apply]
  have hAdj : Γ.Adj v (σ w) ↔ Γ.Adj (σ.symm v) w := by
    simpa using (haut (σ.symm v) w).symm
  by_cases h : Γ.Adj v (σ w)
  · have h' : Γ.Adj (σ.symm v) w := hAdj.mp h
    simp [h, h']
  · have h' : ¬ Γ.Adj (σ.symm v) w := fun hw => h (hAdj.mpr hw)
    simp [h, h']

/-- The all-ones matrix commutes with every vertex permutation matrix. -/
theorem allOnesMatrix_mul_permMatrix_eq_permMatrix_mul_allOnesMatrix
    (σ : Equiv.Perm V) :
    allOnesMatrix V * permMatrix σ = permMatrix σ * allOnesMatrix V := by
  classical
  ext v w
  rw [mul_permMatrix_apply, permMatrix_mul_apply]
  simp [allOnesMatrix]

/-- The Moore57 `E7Matrix` commutes with a graph automorphism. -/
theorem E7Matrix_mul_permMatrix_eq_permMatrix_mul_E7Matrix
    (Γ : SimpleGraph V) [DecidableRel Γ.Adj] (σ : Equiv.Perm V)
    (haut : ∀ v w, Γ.Adj v w ↔ Γ.Adj (σ v) (σ w)) :
    E7Matrix Γ * permMatrix σ = permMatrix σ * E7Matrix Γ := by
  classical
  simp [E7Matrix, Matrix.add_mul, Matrix.sub_mul, Matrix.mul_add, Matrix.mul_sub,
    adjMatrix_mul_permMatrix_eq_permMatrix_mul_adjMatrix Γ σ haut,
    allOnesMatrix_mul_permMatrix_eq_permMatrix_mul_allOnesMatrix σ]

end HigmanTrace

end Moore57
