import Moore57.Moore57Graph.Moore57Definition
import Moore57.Moore57Graph.Aut.InducedSubgraph

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Makhnev–Paduchikh 2001, Lemma 1

> Let Γ be a strong graph with `λ = 0` and `µ = 1`. Then:
>
> (1) Γ is a Moore graph or a star;
>
> (2) if `X ⊆ Aut(Γ)` and `X` has fixed points then `Fix(X)` is also a
>     strong graph with `λ = 0` and `µ = 1`.

Status:
* Part (1) (general strong-(0,1) classification) is a foundational fact
  about strong graphs; remains a skeleton (substantial new work).
* Part (2) is wrapped for the single-element case (`X = ⟨σ⟩`) from
  `Moore57.Moore57Graph.Aut.InducedSubgraph.autFixedInducedGraph_isStrongZeroOne`.
  The general subgroup case follows by taking intersections.
-/

open Moore57

namespace Moore57.Papers.MakhnevPaduchikh2001

variable {V : Type*} [Fintype V] [DecidableEq V]
  {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- **Lemma 1 (1) (strong (0,1) ⇒ Moore or star).** [skeleton] -/
theorem lem1_part1 : True := by trivial

/-- **Lemma 1 (2) (`Fix(σ)` is also strong (0,1), single-element case).**
For a Moore57 graph Γ and any σ ∈ Aut(Γ), the σ-fixed induced subgraph
satisfies the strong (λ = 0, µ = 1) condition. -/
theorem lem1_part2 (hΓ : IsMoore57 Γ) (σ : Equiv.Perm V)
    (hAut : ∀ v w, Γ.Adj v w ↔ Γ.Adj (σ v) (σ w)) :
    IsStrongZeroOne (autFixedInducedGraph Γ σ) :=
  autFixedInducedGraph_isStrongZeroOne hΓ σ hAut

end Moore57.Papers.MakhnevPaduchikh2001
