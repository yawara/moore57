import Moore57.D19Contradiction
import Moore57.Moore57Graph.E7Matrix.Idempotent
import Moore57.D19OnMoore57.HigmanTrace.HigmanTraceCongruence

/-!
# Phase 2 prebuilt aliases for the SRG / Higman trace pipeline

The natural-language Lemma 9.2 (Higman trace formula) and the supporting
matrix algebra (SRG identity `A² = 56·I − A + J`, idempotent `E₇` projection,
trace expressions) are already proved in the codebase.  This file exposes
them under stable Phase 2 names and adds the immediate corollary
`Tr(E₇) = 1729` (the dimension of the 7-eigenspace), needed in Phase 4 for
the representation-side constraint `α + β + 18γ = 1729`.

* `srg_adjMatrix_sq` — `A² = 56·I − A + J` (Phase 2.1)
* `E7Matrix_isIdempotent` — `E₇² = E₇` (Phase 2.3)
* `higman_trace_formula` — `Tr(E₇ P_σ) = (8 a₀(σ) + a₁(σ) − 65)/15` (Phase 2.4)
* `E7Matrix_trace_eq_1729` — `Tr(E₇) = 1729` (Phase 2.2 dimension fact)
-/

namespace Moore57

namespace IsMoore57

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- Phase 2.1: the SRG identity `A² = 56·I − A + J` for Moore57. -/
theorem srg_adjMatrix_sq (hΓ : IsMoore57 Γ) :
    Γ.adjMatrix ℚ ^ 2 =
      (56 : ℚ) • (1 : Matrix V V ℚ) - Γ.adjMatrix ℚ + allOnesMatrix V :=
  hΓ.adjMatrix_sq_eq

/-- Phase 2.3: the `E₇` projection is idempotent. -/
theorem E7Matrix_isIdempotent (hΓ : IsMoore57 Γ) :
    IsIdempotentElem (E7Matrix Γ) :=
  E7Matrix_isIdempotentElem hΓ

/-- Phase 2.2 (key special case): the trace of `E₇` equals `1729`,
the dimension of the 7-eigenspace.  Obtained by specialising the Higman
trace formula at `σ = 1` (identity permutation), using `a₀(1) = |V| = 3250`
and `a₁(1) = 0` (no vertex is adjacent to itself in a simple graph). -/
theorem E7Matrix_trace_eq_1729 (hΓ : IsMoore57 Γ) :
    Matrix.trace (E7Matrix Γ) = (1729 : ℚ) := by
  have hform := hΓ.higman_trace_formula (1 : Equiv.Perm V)
  -- permMatrix 1 = 1 (identity matrix)
  have hperm : (permMatrix (1 : Equiv.Perm V) : Matrix V V ℚ) = 1 := by
    ext v w
    by_cases hvw : v = w
    · subst w; simp [permMatrix]
    · simp [permMatrix, hvw]
  rw [hperm, Matrix.mul_one] at hform
  -- fixedVertexCount 1 = |V| = 3250
  have hfix : fixedVertexCount (1 : Equiv.Perm V) = Fintype.card V := by
    classical
    simp [fixedVertexCount]
  have hcardV : Fintype.card V = 3250 := hΓ.card
  -- adjacentMovedCount Γ 1 = 0 (no self-loops in simple graph)
  have hadj : adjacentMovedCount Γ (1 : Equiv.Perm V) = 0 := by
    classical
    simp [adjacentMovedCount, Equiv.Perm.one_apply, SimpleGraph.irrefl]
  rw [hfix, hcardV, hadj] at hform
  rw [hform]
  norm_num

end IsMoore57

end Moore57
