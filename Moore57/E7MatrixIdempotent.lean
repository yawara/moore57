import Moore57.D19Contradiction

/-!
# Idempotence of the Moore57 E7 projection matrix

This file keeps the matrix-algebra bridge for the `E7Matrix` projection
separate from the trace pipeline.
-/

namespace Moore57

section HigmanTrace

variable {V : Type*} [Fintype V]

/-- The all-ones matrix squares to `|V|` times itself. -/
theorem allOnesMatrix_mul_allOnesMatrix :
    allOnesMatrix V * allOnesMatrix V =
      (Fintype.card V : ℚ) • allOnesMatrix V := by
  classical
  ext v w
  simp [allOnesMatrix, Matrix.mul_apply]

/-- In a regular graph, the adjacency matrix sends the all-ones matrix to
`degree • J` on the left. -/
theorem adjMatrix_mul_allOnesMatrix_of_regular
    (Γ : SimpleGraph V) [DecidableRel Γ.Adj] {d : ℕ}
    (hreg : Γ.IsRegularOfDegree d) :
    Γ.adjMatrix ℚ * allOnesMatrix V = (d : ℚ) • allOnesMatrix V := by
  classical
  ext v w
  simp [allOnesMatrix, hreg.degree_eq v]

/-- In a regular graph, the all-ones matrix sends the adjacency matrix to
`degree • J` on the right. -/
theorem allOnesMatrix_mul_adjMatrix_of_regular
    (Γ : SimpleGraph V) [DecidableRel Γ.Adj] {d : ℕ}
    (hreg : Γ.IsRegularOfDegree d) :
    allOnesMatrix V * Γ.adjMatrix ℚ = (d : ℚ) • allOnesMatrix V := by
  classical
  ext v w
  simp [allOnesMatrix, hreg.degree_eq w]

/-- The Moore57 specialization of `A * J = 57J`. -/
theorem adjMatrix_mul_allOnesMatrix
    {Γ : SimpleGraph V} [DecidableRel Γ.Adj] (hΓ : IsMoore57 Γ) :
    Γ.adjMatrix ℚ * allOnesMatrix V = (57 : ℚ) • allOnesMatrix V := by
  simpa using adjMatrix_mul_allOnesMatrix_of_regular Γ hΓ.regular

/-- The Moore57 specialization of `J * A = 57J`. -/
theorem allOnesMatrix_mul_adjMatrix
    {Γ : SimpleGraph V} [DecidableRel Γ.Adj] (hΓ : IsMoore57 Γ) :
    allOnesMatrix V * Γ.adjMatrix ℚ = (57 : ℚ) • allOnesMatrix V := by
  simpa using allOnesMatrix_mul_adjMatrix_of_regular Γ hΓ.regular

/-- The Moore57 specialization of `J * J = 3250J`. -/
theorem allOnesMatrix_mul_allOnesMatrix_of_moore
    {Γ : SimpleGraph V} [DecidableRel Γ.Adj] (hΓ : IsMoore57 Γ) :
    allOnesMatrix V * allOnesMatrix V = (3250 : ℚ) • allOnesMatrix V := by
  rw [allOnesMatrix_mul_allOnesMatrix, hΓ.card]
  norm_num

/-- The Moore57 `E7Matrix` is an idempotent matrix. -/
theorem E7Matrix_mul_E7Matrix_eq_E7Matrix
    [DecidableEq V]
    {Γ : SimpleGraph V} [DecidableRel Γ.Adj] (hΓ : IsMoore57 Γ) :
    E7Matrix Γ * E7Matrix Γ = E7Matrix Γ := by
  classical
  ext v w
  have hA2 :
      (Γ.adjMatrix ℚ * Γ.adjMatrix ℚ) v w =
        ((56 : ℚ) • (1 : Matrix V V ℚ) - Γ.adjMatrix ℚ + allOnesMatrix V) v w := by
    simpa [pow_two] using congrFun (congrFun (hΓ.adjMatrix_sq_eq) v) w
  have hAJ := congrFun (congrFun (adjMatrix_mul_allOnesMatrix hΓ) v) w
  have hJA := congrFun (congrFun (allOnesMatrix_mul_adjMatrix hΓ) v) w
  have hJ2 := congrFun (congrFun (allOnesMatrix_mul_allOnesMatrix_of_moore hΓ) v) w
  simp only [E7Matrix, Matrix.sub_mul, Matrix.add_mul, Matrix.mul_sub, Matrix.mul_add,
    Matrix.smul_mul, Matrix.mul_smul, Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply,
    Matrix.one_mul, Matrix.mul_one] at hA2 hAJ hJA hJ2 ⊢
  rw [hA2, hAJ, hJA, hJ2]
  by_cases hvw : v = w
  · subst w
    simp [allOnesMatrix]
    ring
  · by_cases hadj : Γ.Adj v w
    · simp [allOnesMatrix, hvw, hadj]
      ring
    · simp [allOnesMatrix, hvw, hadj]
      ring

/-- The Moore57 `E7Matrix` as an `IsIdempotentElem` witness. -/
theorem E7Matrix_isIdempotentElem
    [DecidableEq V]
    {Γ : SimpleGraph V} [DecidableRel Γ.Adj] (hΓ : IsMoore57 Γ) :
    IsIdempotentElem (E7Matrix Γ) := by
  exact E7Matrix_mul_E7Matrix_eq_E7Matrix hΓ

end HigmanTrace

end Moore57
