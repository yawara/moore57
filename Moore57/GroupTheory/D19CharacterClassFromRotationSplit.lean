import Moore57.GroupTheory.D19RotationMovingCyclotomic
import Moore57.D19CharacterBoundaryConstructors

/-!
# D19 character class data from the rotation split

For a rational finite-dimensional representation of `D19`, the average over
the rotation subgroup splits the space into the rotation-invariant summand and
the moving summand.  The invariant summand contributes the trivial/sign
multiplicities, while the moving summand contributes copies of the rational
cyclotomic `18`-dimensional block.
-/

namespace Moore57

open DirectSum

noncomputable section

variable {W : Type*} [AddCommGroup W] [Module ℚ W]

theorem d19RotationInvariantSubmodule_maps_rotation
    (ρ : Representation ℚ (DihedralGroup 19) W) (d : ZMod 19) :
    Set.MapsTo (ρ (DihedralGroup.r d))
      (d19RotationInvariantSubmodule ρ) (d19RotationInvariantSubmodule ρ) := by
  intro x hx
  change ρ (DihedralGroup.r d) x ∈ d19RotationInvariantSubmodule ρ
  change x ∈ d19RotationInvariantSubmodule ρ at hx
  rw [mem_d19RotationInvariantSubmodule] at hx ⊢
  intro e
  calc
    ρ (DihedralGroup.r e) (ρ (DihedralGroup.r d) x)
        = ρ (DihedralGroup.r (e + d)) x := by
          rw [← Module.End.mul_apply, ← map_mul, DihedralGroup.r_mul_r]
    _ = x := hx (e + d)
    _ = ρ (DihedralGroup.r d) x := (hx d).symm

theorem d19RotationMovingSubmodule_maps
    (ρ : Representation ℚ (DihedralGroup 19) W) (g : DihedralGroup 19) :
    Set.MapsTo (ρ g) (d19RotationMovingSubmodule ρ)
      (d19RotationMovingSubmodule ρ) :=
  LinearMap.ker_le_comap_of_commute (d19RotationAverageMap_commute ρ g)

theorem trace_restrict_rotationInvariant_eq_finrank
    [FiniteDimensional ℚ W]
    (ρ : Representation ℚ (DihedralGroup 19) W) (d : ZMod 19)
    (hmaps :
      Set.MapsTo (ρ (DihedralGroup.r d))
        (d19RotationInvariantSubmodule ρ)
        (d19RotationInvariantSubmodule ρ)) :
    _root_.LinearMap.trace ℚ (d19RotationInvariantSubmodule ρ)
        ((ρ (DihedralGroup.r d)).restrict hmaps) =
      (Module.finrank ℚ (d19RotationInvariantSubmodule ρ) : ℚ) := by
  have hrestrict :
      (ρ (DihedralGroup.r d)).restrict hmaps =
        (1 : d19RotationInvariantSubmodule ρ →ₗ[ℚ]
          d19RotationInvariantSubmodule ρ) := by
    ext x
    exact (mem_d19RotationInvariantSubmodule ρ (x : W)).mp x.property d
  rw [hrestrict]
  simp

theorem trace_restrict_rotationMoving_eq_movingRepresentation
    [FiniteDimensional ℚ W]
    (ρ : Representation ℚ (DihedralGroup 19) W) (g : DihedralGroup 19)
    (hmaps :
      Set.MapsTo (ρ g) (d19RotationMovingSubmodule ρ)
        (d19RotationMovingSubmodule ρ)) :
    _root_.LinearMap.trace ℚ (d19RotationMovingSubmodule ρ)
        ((ρ g).restrict hmaps) =
      _root_.LinearMap.trace ℚ (d19RotationMovingSubmodule ρ)
        (d19RotationMovingRepresentation ρ g) := by
  congr 1

/-- The character of a rotation is the sum of the trace on the invariant
summand and the trace on the moving summand. -/
theorem d19Character_rotation_eq_invariant_add_moving
    [FiniteDimensional ℚ W]
    (ρ : Representation ℚ (DihedralGroup 19) W) (d : ZMod 19) :
    ρ.character (DihedralGroup.r d) =
      (Module.finrank ℚ (d19RotationInvariantSubmodule ρ) : ℚ) +
        _root_.LinearMap.trace ℚ (d19RotationMovingSubmodule ρ)
          (d19RotationMovingRepresentation ρ (DihedralGroup.r d)) := by
  classical
  let U := d19RotationInvariantSubmodule ρ
  let M := d19RotationMovingSubmodule ρ
  let N : Bool → Submodule ℚ W := fun b => if b then M else U
  let f := ρ (DihedralGroup.r d)
  have hInternal : DirectSum.IsInternal N := by
    refine (DirectSum.isInternal_submodule_iff_isCompl
      N (i := false) (j := true)
      (by decide) (by
        ext b
        cases b <;> simp)).mpr ?_
    change IsCompl U M
    exact d19RotationInvariantSubmodule_isCompl_moving ρ
  have hmaps :
      ∀ b : Bool, Set.MapsTo f (N b) (N b) := by
    intro b
    cases b
    · exact d19RotationInvariantSubmodule_maps_rotation ρ d
    · exact d19RotationMovingSubmodule_maps ρ (DihedralGroup.r d)
  have htrace :=
    _root_.LinearMap.trace_eq_sum_trace_restrict hInternal hmaps
  have hU :
      _root_.LinearMap.trace ℚ (N false) (f.restrict (hmaps false)) =
        (Module.finrank ℚ (N false) : ℚ) := by
    dsimp [N, U, f]
    exact trace_restrict_rotationInvariant_eq_finrank ρ d (hmaps false)
  have hM :
      _root_.LinearMap.trace ℚ (N true) (f.restrict (hmaps true)) =
        _root_.LinearMap.trace ℚ M
          (d19RotationMovingRepresentation ρ (DihedralGroup.r d)) := by
    dsimp [N, M, f]
    exact
      trace_restrict_rotationMoving_eq_movingRepresentation ρ
        (DihedralGroup.r d) (hmaps true)
  change _root_.LinearMap.trace ℚ W f =
    (Module.finrank ℚ U : ℚ) +
      _root_.LinearMap.trace ℚ M
        (d19RotationMovingRepresentation ρ (DihedralGroup.r d))
  rw [htrace]
  rw [Fintype.sum_bool]
  rw [hM, hU]
  change
    _root_.LinearMap.trace ℚ M
          (d19RotationMovingRepresentation ρ (DihedralGroup.r d)) +
        (Module.finrank ℚ U : ℚ) =
      (Module.finrank ℚ U : ℚ) +
        _root_.LinearMap.trace ℚ M
          (d19RotationMovingRepresentation ρ (DihedralGroup.r d))
  ring

/-- The abstract D19 character-value package follows from the rotation-average
split: the invariant part supplies `α, β`, and the moving part supplies `γ`.

This version has no fixed ambient dimension, so it applies equally to the E7
projection representation and to the complementary `(-8)` representation. -/
theorem exists_d19CharacterValueBoundary_from_rotation_split
    [FiniteDimensional ℚ W]
    (ρ : Representation ℚ (DihedralGroup 19) W) :
    ∃ alpha beta gamma : ℕ,
      D19CharacterValueBoundary ρ alpha beta gamma := by
  rcases exists_nat_reflectionClassCharacter_from_rotationInvariants ρ with
    ⟨alpha, beta, hdim_invariant, hreflection⟩
  rcases exists_gamma_trace_d19RotationMovingSubmodule ρ with
    ⟨gamma, hdim_moving, htrace_moving⟩
  have hdim :
      Module.finrank ℚ W = alpha + beta + 18 * gamma := by
    calc
      Module.finrank ℚ W
          = Module.finrank ℚ (d19RotationInvariantSubmodule ρ) +
              Module.finrank ℚ (d19RotationMovingSubmodule ρ) :=
            (Submodule.finrank_add_eq_of_isCompl
              (d19RotationInvariantSubmodule_isCompl_moving ρ)).symm
      _ = alpha + beta + 18 * gamma := by
            rw [hdim_invariant, hdim_moving]
  refine ⟨alpha, beta, gamma, ?_⟩
  refine
    { one_value := ?_
      rotation_value := ?_
      reflection_zero := hreflection 0 }
  · calc
      ρ.character (1 : DihedralGroup 19)
          = (Module.finrank ℚ W : ℚ) :=
            representationCharacter_one_eq_finrank ρ
      _ = (alpha : ℚ) + (beta : ℚ) + 18 * (gamma : ℚ) := by
        rw [hdim]
        norm_num
  · intro d hd
    calc
      ρ.character (DihedralGroup.r d)
          = (Module.finrank ℚ (d19RotationInvariantSubmodule ρ) : ℚ) +
              _root_.LinearMap.trace ℚ (d19RotationMovingSubmodule ρ)
                (d19RotationMovingRepresentation ρ (DihedralGroup.r d)) :=
            d19Character_rotation_eq_invariant_add_moving ρ d
      _ = ((alpha + beta : ℕ) : ℚ) - (gamma : ℚ) := by
        rw [hdim_invariant, htrace_moving d hd]
        ring
      _ = (alpha : ℚ) + (beta : ℚ) - (gamma : ℚ) := by
        norm_num

/-- The fixed-dimension class-boundary form used for the E7 representation is
an immediate consequence of the value-boundary split and
`Representation.char_one`. -/
theorem exists_d19CharacterClassBoundary_from_rotation_split
    [FiniteDimensional ℚ W]
    (ρ : Representation ℚ (DihedralGroup 19) W)
    (finrank_eq : Module.finrank ℚ W = 1729) :
    ∃ alpha beta gamma : ℕ,
      D19CharacterClassBoundary ρ alpha beta gamma := by
  rcases exists_d19CharacterValueBoundary_from_rotation_split ρ with
    ⟨alpha, beta, gamma, valueBoundary⟩
  exact ⟨alpha, beta, gamma,
    D19CharacterClassBoundary.of_character_eq_d19Linear
      alpha beta gamma finrank_eq valueBoundary.character_eq_d19Linear⟩

end

end Moore57
