import Mathlib.LinearAlgebra.Trace
import Mathlib.LinearAlgebra.Matrix.ToLin
import Moore57.Moore57Graph.E7Matrix.PermutationCommutation

/-!
# Bridge from local matrices to mathlib linear maps

This file records thin wrappers around mathlib's finite Pi-module matrix API,
specialized to the matrix orientation used in the Moore57 trace pipeline.
-/

namespace Moore57

section MatrixToLin

variable {R V : Type*} [CommSemiring R] [Fintype V] [DecidableEq V]

/-- Matrix multiplication is composition of the corresponding `Matrix.toLin'`
linear maps, in the same orientation as local matrix multiplication. -/
theorem matrix_toLin'_mul (A B : Matrix V V R) :
    (A * B).toLin' = A.toLin'.comp B.toLin' := by
  simp

/-- The standard-basis matrix of a composition of two `Matrix.toLin'` maps is
the product of the original matrices. -/
theorem toMatrix'_comp_toLin' (A B : Matrix V V R) :
    LinearMap.toMatrix' (A.toLin'.comp B.toLin') = A * B := by
  rw [LinearMap.toMatrix'_comp]
  simp

/-- The trace of a local matrix, read as an endomorphism of the finite
Pi-module, is its matrix trace. -/
theorem trace_toLin'_eq_matrix_trace (A : Matrix V V R) :
    LinearMap.trace R (V → R) A.toLin' = Matrix.trace A := by
  simp

/-- A matrix commutation identity induces commutation of the associated
endomorphisms of the finite Pi-module. -/
theorem toLin'_commute_of_mul_eq {A B : Matrix V V R} (h : A * B = B * A) :
    Commute A.toLin' B.toLin' := by
  rw [commute_iff_eq]
  rw [Module.End.mul_eq_comp, Module.End.mul_eq_comp]
  rw [← matrix_toLin'_mul, ← matrix_toLin'_mul, h]

/-- Conversely, commutation of the associated endomorphisms is exactly matrix
commutation. -/
theorem mul_eq_of_toLin'_commute {A B : Matrix V V R} (h : Commute A.toLin' B.toLin') :
    A * B = B * A := by
  rw [commute_iff_eq] at h
  apply Matrix.toLin'.injective
  rw [matrix_toLin'_mul, matrix_toLin'_mul]
  simpa [Module.End.mul_eq_comp] using h

end MatrixToLin

section HigmanTrace

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Local specialization of the multiplication/composition bridge for the
Moore57 projection-like matrix followed by a permutation matrix. -/
theorem E7Matrix_mul_permMatrix_toLin'
    (Γ : SimpleGraph V) [DecidableRel Γ.Adj] (σ : Equiv.Perm V) :
    (E7Matrix Γ * permMatrix σ).toLin' =
      (E7Matrix Γ).toLin'.comp (permMatrix σ).toLin' :=
  matrix_toLin'_mul (E7Matrix Γ) (permMatrix σ)

/-- The matrix trace of `E7Matrix Γ * permMatrix σ` agrees with the trace of
its associated endomorphism of `V → ℚ`. -/
theorem trace_E7Matrix_mul_permMatrix_toLin'_eq_matrix_trace
    (Γ : SimpleGraph V) [DecidableRel Γ.Adj] (σ : Equiv.Perm V) :
    LinearMap.trace ℚ (V → ℚ) (E7Matrix Γ * permMatrix σ).toLin' =
      Matrix.trace (E7Matrix Γ * permMatrix σ) :=
  trace_toLin'_eq_matrix_trace (E7Matrix Γ * permMatrix σ)

/-- The existing matrix commutation theorem gives commutation of the associated
linear endomorphisms. -/
theorem E7Matrix_toLin'_commute_permMatrix_toLin'
    (Γ : SimpleGraph V) [DecidableRel Γ.Adj] (σ : Equiv.Perm V)
    (haut : ∀ v w, Γ.Adj v w ↔ Γ.Adj (σ v) (σ w)) :
    Commute (E7Matrix Γ).toLin' (permMatrix σ).toLin' :=
  toLin'_commute_of_mul_eq
    (E7Matrix_mul_permMatrix_eq_permMatrix_mul_E7Matrix Γ σ haut)

end HigmanTrace

end Moore57
