import Moore57.Moore57Graph.E7Matrix.PermutationCommutation
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.RepresentationTheory.Submodule
import Moore57.D19OnMoore57.Action.D19Action

/-!
# The E7 range as a subrepresentation skeleton

This file isolates the representation-theoretic step that will be used once
the `E7Matrix` projection facts are available.  The invariant-range argument
does not need idempotence: if an endomorphism `p` commutes with a representation,
then `LinearMap.range p` is stable under the representation.
-/

namespace Moore57

namespace LinearMap

variable {K W : Type*} [Semiring K] [AddCommMonoid W] [Module K W]

/-- If `p` commutes with `f`, then the range of `p` is `f`-invariant. -/
theorem range_le_comap_of_commute (p f : W →ₗ[K] W) (hcomm : Commute p f) :
    _root_.LinearMap.range p ≤ (_root_.LinearMap.range p).comap f := by
  rintro _ ⟨x, rfl⟩
  refine ⟨f x, ?_⟩
  rw [← Module.End.mul_apply, hcomm.eq, Module.End.mul_apply]

/-- Set-valued form of `range_le_comap_of_commute`. -/
theorem mapsTo_range_of_commute (p f : W →ₗ[K] W) (hcomm : Commute p f) :
    Set.MapsTo f (_root_.LinearMap.range p) (_root_.LinearMap.range p) := by
  intro x hx
  exact range_le_comap_of_commute p f hcomm hx

end LinearMap

namespace Representation

variable {K G W : Type*} [Semiring K] [Monoid G] [AddCommMonoid W] [Module K W]

/-- Restrict a representation to the range of a commuting endomorphism. -/
noncomputable def onCommutingRange
    (ρ : _root_.Representation K G W) (p : W →ₗ[K] W)
    (hcomm : ∀ g, Commute p (ρ g)) :
    _root_.Representation K G (_root_.LinearMap.range p) :=
  ρ.subrepresentation (_root_.LinearMap.range p)
    fun g => LinearMap.range_le_comap_of_commute p (ρ g) (hcomm g)

@[simp]
theorem onCommutingRange_apply_coe
    (ρ : _root_.Representation K G W) (p : W →ₗ[K] W)
    (hcomm : ∀ g, Commute p (ρ g)) (g : G)
    (x : _root_.LinearMap.range p) :
    ((onCommutingRange ρ p hcomm g x : _root_.LinearMap.range p) : W) =
      ρ g x :=
  rfl

end Representation

namespace LinearEquiv

variable {K W : Type*} [Semiring K] [AddCommMonoid W] [Module K W]

/-- A linear equivalence commuting with `p` also preserves `range p`. -/
theorem mapsTo_range_of_commute
    (p : W →ₗ[K] W) (e : W ≃ₗ[K] W) (hcomm : Commute p e.toLinearMap) :
    Set.MapsTo e (_root_.LinearMap.range p) (_root_.LinearMap.range p) :=
  LinearMap.mapsTo_range_of_commute p e.toLinearMap hcomm

/-- If a linear equivalence commutes with `p`, then its inverse also commutes with `p`. -/
theorem commute_symm_toLinearMap_of_commute
    (p : W →ₗ[K] W) (e : W ≃ₗ[K] W) (hcomm : Commute p e.toLinearMap) :
    Commute p e.symm.toLinearMap := by
  rw [commute_iff_eq]
  ext x
  apply e.injective
  calc
    e ((p * e.symm.toLinearMap) x) = e (p (e.symm x)) := rfl
    _ = p x := by
      have h :=
        congrArg (fun f : Module.End K W => f (e.symm x)) hcomm.eq
      simpa [Module.End.mul_apply] using h.symm
    _ = e ((e.symm.toLinearMap * p) x) := by
      simp [Module.End.mul_apply]

/-- Restrict a commuting linear equivalence to `range p`. -/
noncomputable def restrictRangeOfCommute
    (p : W →ₗ[K] W) (e : W ≃ₗ[K] W) (hcomm : Commute p e.toLinearMap) :
    _root_.LinearMap.range p ≃ₗ[K] _root_.LinearMap.range p where
  toFun x :=
    ⟨e x, mapsTo_range_of_commute p e hcomm x.property⟩
  invFun x :=
    ⟨e.symm x,
      LinearMap.mapsTo_range_of_commute p e.symm.toLinearMap
        (commute_symm_toLinearMap_of_commute p e hcomm) x.property⟩
  left_inv x := by
    ext
    simp
  right_inv x := by
    ext
    simp
  map_add' x y := by
    ext
    simp
  map_smul' a x := by
    ext
    simp

@[simp]
theorem restrictRangeOfCommute_apply
    (p : W →ₗ[K] W) (e : W ≃ₗ[K] W) (hcomm : Commute p e.toLinearMap)
    (x : _root_.LinearMap.range p) :
    ((restrictRangeOfCommute p e hcomm x : _root_.LinearMap.range p) : W) =
      e x :=
  rfl

end LinearEquiv

section HigmanTrace

variable {V : Type*} [Fintype V] [DecidableEq V]

omit [Fintype V] in
@[simp]
theorem moore57_permMatrix_one :
    permMatrix (1 : Equiv.Perm V) = 1 := by
  change Equiv.Perm.permMatrix ℚ ((1 : Equiv.Perm V)⁻¹) = 1
  simp

/-- The project `permMatrix` convention is multiplicative in the permutation. -/
theorem moore57_permMatrix_mul (σ τ : Equiv.Perm V) :
    permMatrix (σ * τ) = permMatrix σ * permMatrix τ := by
  change Equiv.Perm.permMatrix ℚ ((σ * τ)⁻¹) =
    Equiv.Perm.permMatrix ℚ σ⁻¹ * Equiv.Perm.permMatrix ℚ τ⁻¹
  rw [mul_inv_rev, Matrix.permMatrix_mul]

/-- The permutation-matrix representation on all functions `V → ℚ`. -/
noncomputable def permutationMatrixRepresentationOnPi
    (φ : DihedralGroup 19 →* Equiv.Perm V) :
    _root_.Representation ℚ (DihedralGroup 19) (V → ℚ) where
  toFun g := (permMatrix (φ g)).toLin'
  map_one' := by
    simp
    rfl
  map_mul' g g' := by
    rw [map_mul, moore57_permMatrix_mul, Matrix.toLin'_mul]
    rfl

/-- Matrix commutation, transported through `Matrix.toLin'`. -/
theorem E7Matrix_toLin'_commute_permMatrix
    (Γ : SimpleGraph V) [DecidableRel Γ.Adj] (σ : Equiv.Perm V)
    (haut : ∀ v w, Γ.Adj v w ↔ Γ.Adj (σ v) (σ w)) :
    Commute (E7Matrix Γ).toLin' (permMatrix σ).toLin' := by
  rw [commute_iff_eq]
  rw [Module.End.mul_eq_comp, Module.End.mul_eq_comp]
  rw [← Matrix.toLin'_mul, ← Matrix.toLin'_mul]
  exact congrArg Matrix.toLin'
    (E7Matrix_mul_permMatrix_eq_permMatrix_mul_E7Matrix Γ σ haut)

end HigmanTrace

namespace D19ActsOnMoore57

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- The D19 action as a monoid homomorphism into vertex permutations. -/
noncomputable def smulPermHom (h : D19ActsOnMoore57 V Γ) :
    DihedralGroup 19 →* Equiv.Perm V where
  toFun g := h.smulEquiv g
  map_one' := h.smulEquiv_one
  map_mul' := h.smulEquiv_mul

/-- The ambient permutation-matrix representation on `V → ℚ`. -/
noncomputable def vertexPermutationMatrixRepresentationOnPi
    (h : D19ActsOnMoore57 V Γ) :
    _root_.Representation ℚ (DihedralGroup 19) (V → ℚ) :=
  permutationMatrixRepresentationOnPi h.smulPermHom

@[simp]
theorem vertexPermutationMatrixRepresentationOnPi_apply
    (h : D19ActsOnMoore57 V Γ) (g : DihedralGroup 19) :
    h.vertexPermutationMatrixRepresentationOnPi g =
      (permMatrix (h.smulEquiv g)).toLin' :=
  rfl

/-- Assumption-parameterized E7 range representation.  This is the intended
attachment point for future idempotence/projection facts; closure only uses
commutation with the ambient permutation representation. -/
noncomputable def e7ProjectionRepresentationOfCommute
    (h : D19ActsOnMoore57 V Γ)
    (hcomm :
      ∀ g : DihedralGroup 19,
        Commute (E7Matrix Γ).toLin' (h.vertexPermutationMatrixRepresentationOnPi g)) :
    _root_.Representation ℚ (DihedralGroup 19)
      (_root_.LinearMap.range (E7Matrix Γ).toLin') :=
  Representation.onCommutingRange h.vertexPermutationMatrixRepresentationOnPi
    (E7Matrix Γ).toLin' hcomm

@[simp]
theorem e7ProjectionRepresentationOfCommute_apply_coe
    (h : D19ActsOnMoore57 V Γ)
    (hcomm :
      ∀ g : DihedralGroup 19,
        Commute (E7Matrix Γ).toLin' (h.vertexPermutationMatrixRepresentationOnPi g))
    (g : DihedralGroup 19)
    (x : _root_.LinearMap.range (E7Matrix Γ).toLin') :
    (((h.e7ProjectionRepresentationOfCommute hcomm) g x :
        _root_.LinearMap.range (E7Matrix Γ).toLin') : V → ℚ) =
      (permMatrix (h.smulEquiv g)).toLin' x :=
  rfl

/-- The concrete E7 range representation for a `D19ActsOnMoore57` action, using
the existing matrix commutation theorem for graph automorphisms. -/
noncomputable def e7ProjectionRepresentation
    (h : D19ActsOnMoore57 V Γ) :
    _root_.Representation ℚ (DihedralGroup 19)
      (_root_.LinearMap.range (E7Matrix Γ).toLin') :=
  h.e7ProjectionRepresentationOfCommute fun g =>
    E7Matrix_toLin'_commute_permMatrix Γ (h.smulEquiv g) <| by
      intro v w
      simpa using h.smul_adj g v w

end D19ActsOnMoore57

end Moore57
