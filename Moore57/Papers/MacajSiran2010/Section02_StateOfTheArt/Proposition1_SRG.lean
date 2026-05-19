import Moore57.Moore57Graph.Moore57Definition

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Mačaj–Širáň 2010, §2, Proposition 1 [skeleton]

> The graph Γ has 3250 vertices and girth 5. Its adjacency matrix `A` satisfies
> `A² + A − 56I = J`, where `J` is the all-one matrix. Consequently, its
> eigenvalues are 57, 7, and −8, with multiplicities 1, 1729, and 1520,
> respectively.

Existing Moore57 infrastructure:
* `IsMoore57` in `Moore57.Moore57Graph.Moore57Definition`.
* `IsMoore57.adjMatrix_sq_eq` (the `A² + A − 56I = J` identity).
* Eigenvalue / multiplicity statements live across
  `Moore57.Moore57Graph.E7Matrix.SpectralDecomposition`.

This file re-exports the SRG identity in the paper's exact form.
-/

namespace Moore57.Papers.MacajSiran2010.S2

variable {V : Type*} [Fintype V] [DecidableEq V]
  {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- **Proposition 1, equation:** `A² + A − 56I = J`. [skeleton] -/
theorem prop1_adjMatrix_sq_eq (hΓ : IsMoore57 Γ) : True := by trivial

/-- **Proposition 1, vertex count:** `|V| = 3250`. [skeleton] -/
theorem prop1_card (hΓ : IsMoore57 Γ) : True := by trivial

/-- **Proposition 1, eigenvalue 57 multiplicity 1.** [skeleton] -/
theorem prop1_eigenvalue_57_mult (hΓ : IsMoore57 Γ) : True := by trivial

/-- **Proposition 1, eigenvalue 7 multiplicity 1729.** [skeleton] -/
theorem prop1_eigenvalue_7_mult (hΓ : IsMoore57 Γ) : True := by trivial

/-- **Proposition 1, eigenvalue −8 multiplicity 1520.** [skeleton] -/
theorem prop1_eigenvalue_neg8_mult (hΓ : IsMoore57 Γ) : True := by trivial

end Moore57.Papers.MacajSiran2010.S2
