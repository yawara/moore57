import Moore57.D19LinearCharacterInput

/-!
# Dimension equation from the D19 linear-character equality

The full class-character equality
`trace (E7Matrix Γ * permMatrix (h.smulEquiv g)) =
  d19LinearCharacter α β γ g`
specialized at the identity element, combined with the Higman trace formula
applied to the identity permutation, gives the 7-eigenspace dimension equation
`α + β + 18 γ = 1729`.

The arithmetic constraint `α + β + 18 γ = 1729` is currently a hypothesis on
`TraceMultiplicityData`.  This file shows that under the full linear-character
equality on `D19`, the constraint is automatically true for any natural
multiplicities `α, β, γ`.
-/

namespace Moore57

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- The identity permutation fixes every vertex, so its `fixedVertexCount` is
the total vertex count. -/
@[simp] theorem fixedVertexCount_one :
    fixedVertexCount (1 : Equiv.Perm V) = Fintype.card V := by
  classical
  unfold fixedVertexCount
  rw [Finset.filter_true_of_mem]
  · exact Finset.card_univ
  · intro v _
    rfl

omit [DecidableEq V] in
/-- The identity permutation never sends any vertex to an adjacent one in a
simple graph, since `Γ` is irreflexive. -/
@[simp] theorem adjacentMovedCount_one :
    adjacentMovedCount Γ (1 : Equiv.Perm V) = 0 := by
  classical
  unfold adjacentMovedCount
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro v _
  simp

namespace IsMoore57

/-- Higman trace formula at the identity gives the 7-eigenspace dimension `1729`
for `Moore57`. -/
theorem trace_E7Matrix_one (hΓ : IsMoore57 Γ) :
    Matrix.trace (E7Matrix Γ * permMatrix (1 : Equiv.Perm V)) = 1729 := by
  rw [hΓ.higman_trace_formula]
  rw [fixedVertexCount_one, adjacentMovedCount_one, hΓ.card]
  norm_num

end IsMoore57

namespace D19ActsOnMoore57

variable {h : D19ActsOnMoore57 V Γ}

/-- The 7-eigenspace dimension equation `α + β + 18 γ = 1729` follows from any
linear-character equality on `D19`, without requiring it as a separate
multiplicity field. -/
theorem dimension_eq_of_linear_character
    (alpha beta gamma : ℕ)
    (hlin : ∀ g : DihedralGroup 19,
      Matrix.trace (E7Matrix Γ * permMatrix (h.smulEquiv g)) =
        (d19LinearCharacter alpha beta gamma g : ℚ)) :
    alpha + beta + 18 * gamma = 1729 := by
  have hkey := hlin 1
  rw [h.smulEquiv_one, h.isMoore.trace_E7Matrix_one,
    d19LinearCharacter_one] at hkey
  exact_mod_cast hkey.symm

/-- The reflection-character equation `α - β = 33` follows from the
linear-character equality at any reflection element together with the standard
involution counts `a₀(t) = 56` and `a₁(t) = 112`. -/
theorem reflection_eq_of_linear_character
    (alpha beta gamma : ℕ)
    (hlin : ∀ g : DihedralGroup 19,
      Matrix.trace (E7Matrix Γ * permMatrix (h.smulEquiv g)) =
        (d19LinearCharacter alpha beta gamma g : ℚ))
    {d : ZMod 19}
    (ha0 : fixedVertexCount (h.smulEquiv (DihedralGroup.sr d)) = 56)
    (ha1 : adjacentMovedCount Γ (h.smulEquiv (DihedralGroup.sr d)) = 112) :
    (alpha : ℤ) - (beta : ℤ) = 33 := by
  have hkey := hlin (DihedralGroup.sr d)
  rw [h.isMoore.higman_trace_formula, ha0, ha1,
    d19LinearCharacter_reflection] at hkey
  have hℚ : (((alpha : ℤ) - (beta : ℤ) : ℤ) : ℚ) = ((33 : ℤ) : ℚ) := by
    rw [← hkey]; push_cast; norm_num
  exact_mod_cast hℚ

namespace D19LinearCharacterInput

/-- A `D19LinearCharacterInput` automatically witnesses the dimension equation
through its full linear-character equality, in addition to the
`multiplicity.dimension` field. -/
theorem dimension (hin : D19LinearCharacterInput h) :
    hin.multiplicity.alpha + hin.multiplicity.beta +
      18 * hin.multiplicity.gamma = 1729 :=
  dimension_eq_of_linear_character _ _ _ hin.linear_character

/-- A `D19LinearCharacterInput` automatically witnesses the reflection equation
`α - β = 33` for any reflection class element, given the standard involution
counts. -/
theorem reflection_of_counts
    (hin : D19LinearCharacterInput h)
    {d : ZMod 19}
    (ha0 : fixedVertexCount (h.smulEquiv (DihedralGroup.sr d)) = 56)
    (ha1 : adjacentMovedCount Γ (h.smulEquiv (DihedralGroup.sr d)) = 112) :
    (hin.multiplicity.alpha : ℤ) - (hin.multiplicity.beta : ℤ) = 33 :=
  reflection_eq_of_linear_character _ _ _ hin.linear_character ha0 ha1

end D19LinearCharacterInput

end D19ActsOnMoore57

end Moore57
