import Moore57.D19Contradiction
import Moore57.PermutationRepresentationCharacter

/-!
# Vertex permutation representation of a D19 action

This file packages the vertex action stored in `D19ActsOnMoore57` as a
mathlib `MulAction`, then connects its permutation representation character to
the project's concrete permutation-matrix trace and fixed-count APIs.
-/

namespace Moore57

noncomputable section

namespace D19ActsOnMoore57

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- The vertex action in a `D19ActsOnMoore57` witness as a mathlib
`MulAction`. -/
@[reducible] noncomputable def vertexMulAction (h : D19ActsOnMoore57 V Γ) :
    MulAction (DihedralGroup 19) V where
  smul g v := h.smul g v
  one_smul := h.one_smul
  mul_smul := h.mul_smul

/-- The mathlib permutation representation attached to the vertex action. -/
noncomputable def vertexPermutationRepresentation
    (h : D19ActsOnMoore57 V Γ) :
    Representation ℚ (DihedralGroup 19) (V →₀ ℚ) := by
  letI : MulAction (DihedralGroup 19) V := h.vertexMulAction
  exact
    PermutationRepresentationCharacter.permutationRepresentation
      (G := DihedralGroup 19) (X := V)

/-- The vertex permutation representation character is the project
`fixedVertexCount` for the same group element. -/
theorem vertexPermutationRepresentation_character_eq_fixedVertexCount
    (h : D19ActsOnMoore57 V Γ) (g : DihedralGroup 19) :
    (h.vertexPermutationRepresentation).character g =
      (fixedVertexCount (h.smulEquiv g) : ℚ) := by
  classical
  letI : MulAction (DihedralGroup 19) V := h.vertexMulAction
  have hchar :=
    PermutationRepresentationCharacter.character_permutationRepresentation_eq_ncard_setOf
      (G := DihedralGroup 19) (X := V) g
  have hcard :
      ({x : V | g • x = x}.ncard : ℚ) =
        (fixedVertexCount (h.smulEquiv g) : ℚ) := by
    rw [Set.ncard_eq_toFinset_card']
    unfold fixedVertexCount
    have hfinset :
        ({x : V | g • x = x}.toFinset) =
          ((Finset.univ : Finset V).filter fun v => h.smulEquiv g v = v) := by
      ext x
      simp only [Set.mem_toFinset, Finset.mem_filter, Finset.mem_univ, true_and,
        Set.mem_setOf_eq]
      change h.smul g x = x ↔ h.smulEquiv g x = x
      rfl
    rw [hfinset]
  calc
    (h.vertexPermutationRepresentation).character g
        =
          (PermutationRepresentationCharacter.permutationRepresentation
            (G := DihedralGroup 19) (X := V)).character g := rfl
    _ = ({x : V | g • x = x}.ncard : ℚ) := by
          exact hchar
    _ = (fixedVertexCount (h.smulEquiv g) : ℚ) := hcard

/-- The concrete permutation-matrix trace agrees with the mathlib vertex
permutation representation character. -/
theorem trace_permMatrix_smulEquiv_eq_vertexPermutationRepresentation_character
    (h : D19ActsOnMoore57 V Γ) (g : DihedralGroup 19) :
    Matrix.trace (permMatrix (h.smulEquiv g)) =
      (h.vertexPermutationRepresentation).character g := by
  rw [trace_permMatrix_eq_fixedVertexCount,
    h.vertexPermutationRepresentation_character_eq_fixedVertexCount g]

end D19ActsOnMoore57

end

end Moore57
