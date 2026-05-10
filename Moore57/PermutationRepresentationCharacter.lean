import Mathlib.RepresentationTheory.Character
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.LinearAlgebra.Finsupp.VectorSpace
import Mathlib.LinearAlgebra.Matrix.Permutation

/-!
# Trace of a permutation representation

This file records the mathlib-facing trace formula for the permutation
representation attached to a finite group action.
-/

open scoped BigOperators

namespace Moore57

namespace PermutationRepresentationCharacter

noncomputable section

open Matrix

variable {G X : Type*} [Group G] [MulAction G X] [Fintype X] [DecidableEq X]

/-- The natural permutation representation attached to a `G`-set. -/
abbrev permutationRepresentation : Representation ℚ G (X →₀ ℚ) :=
  Representation.ofMulAction ℚ G X

abbrev finsuppBasis : Module.Basis X ℚ (X →₀ ℚ) :=
  Finsupp.basisSingleOne

lemma toMatrix_permutationRepresentation (g : G) :
    LinearMap.toMatrix (finsuppBasis (X := X)) (finsuppBasis (X := X))
        (permutationRepresentation (G := G) (X := X) g) =
      ((MulAction.toPermHom G X g)⁻¹).permMatrix ℚ := by
  ext x y
  by_cases h : g • y = x
  · subst x
    simp [LinearMap.toMatrix_apply, permutationRepresentation, finsuppBasis,
      Equiv.Perm.permMatrix]
  · have hinv : ¬g⁻¹ • x = y := by
      intro hinv
      apply h
      rw [← hinv, smul_inv_smul]
    have hx : x ≠ g • y := fun hx => h hx.symm
    simp [LinearMap.toMatrix_apply, permutationRepresentation, finsuppBasis,
      Equiv.Perm.permMatrix, hinv, hx]

/-- The trace of the linear map induced by `g` is the number of fixed points of `g`. -/
lemma trace_permutationRepresentation (g : G) :
    LinearMap.trace ℚ (X →₀ ℚ) (permutationRepresentation (G := G) (X := X) g) =
      (Function.fixedPoints (MulAction.toPermHom G X g)).ncard := by
  let σ : Equiv.Perm X := MulAction.toPermHom G X g
  have hfixed : Function.fixedPoints (σ⁻¹ : Equiv.Perm X) = Function.fixedPoints σ := by
    ext x
    change σ⁻¹ x = x ↔ σ x = x
    constructor
    · intro h
      simpa using (congrArg σ h).symm
    · intro h
      simpa using (congrArg σ.symm h).symm
  rw [LinearMap.trace_eq_matrix_trace ℚ (finsuppBasis (X := X)),
    toMatrix_permutationRepresentation (G := G) (X := X) g,
    Matrix.trace_permutation, hfixed]

/-- Character form of `trace_permutationRepresentation`. -/
lemma character_permutationRepresentation (g : G) :
    (permutationRepresentation (G := G) (X := X)).character g =
      (Function.fixedPoints (MulAction.toPermHom G X g)).ncard :=
  trace_permutationRepresentation (G := G) (X := X) g

/-- Fixed points can also be read directly from the action formula. -/
lemma character_permutationRepresentation_eq_ncard_setOf (g : G) :
    (permutationRepresentation (G := G) (X := X)).character g =
      {x : X | g • x = x}.ncard := by
  rw [character_permutationRepresentation]
  congr 1

end

end PermutationRepresentationCharacter

end Moore57
