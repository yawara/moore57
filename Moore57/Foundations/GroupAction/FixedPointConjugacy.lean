import Moore57.Foundations.GroupAction.FixedPoints

/-!
# Fixed-point counts and conjugacy

Finite permutations have the same number of fixed points after conjugation.
-/

namespace Moore57

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Fixed-point count is invariant under conjugating a finite permutation. -/
theorem fixedVertexCount_conj (τ σ : Equiv.Perm V) :
    fixedVertexCount (τ * σ * τ⁻¹) = fixedVertexCount σ := by
  rw [fixedVertexCount_eq_card_fixedVertexSet,
    fixedVertexCount_eq_card_fixedVertexSet]
  refine Fintype.card_congr ?_
  exact
    { toFun := fun x =>
        ⟨τ⁻¹ x, by
          have hx : (τ * σ * τ⁻¹) x = x := x.property
          apply τ.injective
          simpa [Equiv.Perm.mul_apply] using hx⟩
      invFun := fun x =>
        ⟨τ x, by
          have hx : σ x = x := x.property
          simp [Equiv.Perm.mul_apply, hx]⟩
      left_inv := by
        intro x
        ext
        simp
      right_inv := by
        intro x
        ext
        simp }

end Moore57
