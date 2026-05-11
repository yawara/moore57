import Moore57.GroupTheory.D19RotationInvariantTrace
import Moore57.ZMod19Lemmas

/-!
# Reflection trace on the rotation-invariant summand

This file is a bounded bridge toward identifying the ambient `sr 0` character
with the trace of the restricted reflection on the rotation-invariant
submodule.
-/

namespace Moore57

noncomputable section

variable {W : Type*} [AddCommGroup W] [Module ℚ W]

/-- The D19 representation on the quotient by the rotation-invariant
submodule. -/
abbrev d19RotationInvariantQuotientRepresentation
    (ρ : Representation ℚ (DihedralGroup 19) W) :
    Representation ℚ (DihedralGroup 19) (W ⧸ d19RotationInvariantSubmodule ρ) :=
  ρ.quotient (d19RotationInvariantSubmodule ρ)
    (Representation.le_comap_invariants ρ d19RotationSubgroup)

/-- The moving part for the rotation subgroup: the kernel of the rotation
average projection. -/
abbrev d19RotationMovingSubmodule
    (ρ : Representation ℚ (DihedralGroup 19) W) : Submodule ℚ W :=
  _root_.LinearMap.ker
    (Representation.averageMap (ρ.comp d19RotationSubgroup.subtype))

/-- The rotation-invariant summand and the moving summand are complementary
submodules, via the standard average projection. -/
theorem d19RotationInvariantSubmodule_isCompl_moving
    (ρ : Representation ℚ (DihedralGroup 19) W) :
    IsCompl (d19RotationInvariantSubmodule ρ) (d19RotationMovingSubmodule ρ) := by
  dsimp [d19RotationInvariantSubmodule, d19RotationMovingSubmodule]
  exact (Representation.isProj_averageMap
    (ρ := ρ.comp d19RotationSubgroup.subtype)).isCompl

/-- The moving part has no nonzero vectors fixed by all rotations. -/
theorem d19RotationMovingSubmodule_no_rotation_invariants
    (ρ : Representation ℚ (DihedralGroup 19) W) :
    d19RotationMovingSubmodule ρ ⊓ d19RotationInvariantSubmodule ρ = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  rw [Submodule.mem_inf] at hx
  have hzero :
      Representation.averageMap (ρ.comp d19RotationSubgroup.subtype) x = 0 :=
    _root_.LinearMap.mem_ker.mp hx.1
  have hid :
      Representation.averageMap (ρ.comp d19RotationSubgroup.subtype) x = x :=
    Representation.averageMap_id (ρ.comp d19RotationSubgroup.subtype) x hx.2
  rw [← hid, hzero]
  exact Submodule.zero_mem ⊥

@[simp]
theorem reflectionZeroOnRotationInvariants_apply_coe
    (ρ : Representation ℚ (DihedralGroup 19) W)
    (x : d19RotationInvariantSubmodule ρ) :
    ((reflectionZeroOnRotationInvariants ρ x : d19RotationInvariantSubmodule ρ) : W) =
      ρ (DihedralGroup.sr (0 : ZMod 19)) x := by
  rfl

theorem reflectionZeroOnRotationInvariants_maps_rotation_invariants
    (ρ : Representation ℚ (DihedralGroup 19) W)
    (x : W) (hx : x ∈ d19RotationInvariantSubmodule ρ) :
    ρ (DihedralGroup.sr (0 : ZMod 19)) x ∈ d19RotationInvariantSubmodule ρ := by
  exact (reflectionZeroOnRotationInvariants ρ ⟨x, hx⟩).property

theorem representationCharacter_reflection_eq_reflection_zero_from_rotation
    [FiniteDimensional ℚ W]
    (ρ : Representation ℚ (DihedralGroup 19) W) (k : ZMod 19) :
    ρ.character (DihedralGroup.sr k) =
      ρ.character (DihedralGroup.sr (0 : ZMod 19)) := by
  let a : ZMod 19 := -((2 : ZMod 19)⁻¹ * k)
  have htwo : (2 : ZMod 19) * ((2 : ZMod 19)⁻¹ * k) = k := by
    rw [← mul_assoc, mul_inv_cancel₀ two_ne_zero_zmod19, one_mul]
  have hconj :
      DihedralGroup.r a * DihedralGroup.sr (0 : ZMod 19) *
          (DihedralGroup.r a)⁻¹ =
        DihedralGroup.sr k := by
    simp [a]
    rw [← two_mul, htwo]
  rw [← hconj]
  exact Representation.char_conj ρ (DihedralGroup.sr (0 : ZMod 19))
    (DihedralGroup.r a)

theorem representationCharacter_rotation_mul_reflection_zero
    [FiniteDimensional ℚ W]
    (ρ : Representation ℚ (DihedralGroup 19) W) (d : ZMod 19) :
    ρ.character (DihedralGroup.r d * DihedralGroup.sr (0 : ZMod 19)) =
      ρ.character (DihedralGroup.sr (0 : ZMod 19)) := by
  rw [DihedralGroup.r_mul_sr]
  exact representationCharacter_reflection_eq_reflection_zero_from_rotation ρ (-d)

theorem average_rotation_reflection_character_eq_reflection_character
    [FiniteDimensional ℚ W]
    (ρ : Representation ℚ (DihedralGroup 19) W) :
    (19 : ℚ)⁻¹ *
        ∑ d : ZMod 19,
          ρ.character (DihedralGroup.r d * DihedralGroup.sr (0 : ZMod 19)) =
      ρ.character (DihedralGroup.sr (0 : ZMod 19)) := by
  rw [Finset.sum_congr rfl (fun d _ =>
    representationCharacter_rotation_mul_reflection_zero ρ d)]
  simp

theorem d19RotationAverageMap_commute_reflectionZero
    (ρ : Representation ℚ (DihedralGroup 19) W) :
    Commute
      (Representation.averageMap (ρ.comp d19RotationSubgroup.subtype))
      (ρ (DihedralGroup.sr (0 : ZMod 19))) := by
  ext x
  change
    Representation.averageMap (ρ.comp d19RotationSubgroup.subtype)
        (ρ (DihedralGroup.sr (0 : ZMod 19)) x) =
      ρ (DihedralGroup.sr (0 : ZMod 19))
        (Representation.averageMap (ρ.comp d19RotationSubgroup.subtype) x)
  simp [Representation.averageMap, GroupAlgebra.average, map_sum]
  rw [← Equiv.sum_comp d19RotationSubgroupEquiv
    (fun c : ↥d19RotationSubgroup =>
      (ρ (c : DihedralGroup 19)) ((ρ (DihedralGroup.sr (0 : ZMod 19))) x))]
  rw [← Equiv.sum_comp d19RotationSubgroupEquiv
    (fun c : ↥d19RotationSubgroup =>
      (ρ (DihedralGroup.sr (0 : ZMod 19))) ((ρ (c : DihedralGroup 19)) x))]
  simp only [d19RotationSubgroupEquiv, Equiv.coe_fn_mk, Subtype.coe_mk]
  simp only [← Module.End.mul_apply, ← map_mul,
    DihedralGroup.r_mul_sr, DihedralGroup.sr_mul_r, zero_sub, zero_add]
  rw [← Equiv.sum_comp (Equiv.neg (ZMod 19))
    (fun i : ZMod 19 => ρ (DihedralGroup.sr i) x)]
  simp

theorem d19RotationAverageMap_commute_rotation
    (ρ : Representation ℚ (DihedralGroup 19) W) (d : ZMod 19) :
    Commute
      (Representation.averageMap (ρ.comp d19RotationSubgroup.subtype))
      (ρ (DihedralGroup.r d)) := by
  ext x
  change
    Representation.averageMap (ρ.comp d19RotationSubgroup.subtype)
        (ρ (DihedralGroup.r d) x) =
      ρ (DihedralGroup.r d)
        (Representation.averageMap (ρ.comp d19RotationSubgroup.subtype) x)
  simp [Representation.averageMap, GroupAlgebra.average, map_sum]
  rw [← Equiv.sum_comp d19RotationSubgroupEquiv
    (fun c : ↥d19RotationSubgroup =>
      (ρ (c : DihedralGroup 19)) ((ρ (DihedralGroup.r d)) x))]
  rw [← Equiv.sum_comp d19RotationSubgroupEquiv
    (fun c : ↥d19RotationSubgroup =>
      (ρ (DihedralGroup.r d)) ((ρ (c : DihedralGroup 19)) x))]
  simp only [d19RotationSubgroupEquiv, Equiv.coe_fn_mk, Subtype.coe_mk]
  simp only [← Module.End.mul_apply, ← map_mul, DihedralGroup.r_mul_r]
  simp [add_comm]

theorem d19RotationAverageMap_commute
    (ρ : Representation ℚ (DihedralGroup 19) W) (g : DihedralGroup 19) :
    Commute
      (Representation.averageMap (ρ.comp d19RotationSubgroup.subtype))
      (ρ g) := by
  cases g with
  | r d =>
      exact d19RotationAverageMap_commute_rotation ρ d
  | sr d =>
      have hrot :
          Commute
            (Representation.averageMap (ρ.comp d19RotationSubgroup.subtype))
            (ρ (DihedralGroup.r (-d))) :=
        d19RotationAverageMap_commute_rotation ρ (-d)
      have href := d19RotationAverageMap_commute_reflectionZero ρ
      rw [← show
        DihedralGroup.r (-d) * DihedralGroup.sr (0 : ZMod 19) =
            DihedralGroup.sr d by
          simp [DihedralGroup.r_mul_sr]]
      rw [map_mul]
      exact hrot.mul_right href

namespace LinearMap

theorem ker_le_comap_of_commute
    {p f : W →ₗ[ℚ] W} (hcomm : Commute p f) :
    _root_.LinearMap.ker p ≤ (_root_.LinearMap.ker p).comap f := by
  intro x hx
  change p (f x) = 0
  rw [← Module.End.mul_apply, hcomm.eq, Module.End.mul_apply,
    _root_.LinearMap.mem_ker.mp hx, map_zero]

end LinearMap

/-- The D19 representation on the kernel of the rotation-average projection. -/
abbrev d19RotationMovingRepresentation
    (ρ : Representation ℚ (DihedralGroup 19) W) :
    Representation ℚ (DihedralGroup 19) (d19RotationMovingSubmodule ρ) :=
  ρ.subrepresentation (d19RotationMovingSubmodule ρ)
    fun g => LinearMap.ker_le_comap_of_commute
      (d19RotationAverageMap_commute ρ g)

theorem d19RotationMovingRepresentation_invariants_eq_bot
    (ρ : Representation ℚ (DihedralGroup 19) W) :
    d19RotationInvariantSubmodule (d19RotationMovingRepresentation ρ) = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  rw [Representation.mem_invariants] at hx
  apply Subtype.ext
  have hboth : (x : W) ∈ d19RotationMovingSubmodule ρ ⊓
      d19RotationInvariantSubmodule ρ := by
    rw [Submodule.mem_inf]
    refine ⟨x.property, ?_⟩
    rw [Representation.mem_invariants]
    intro c
    have hc := hx c
    exact congrArg Subtype.val hc
  have hzero : (x : W) ∈ (⊥ : Submodule ℚ W) := by
    rw [← d19RotationMovingSubmodule_no_rotation_invariants ρ]
    exact hboth
  simpa using hzero

theorem trace_averageMap_mul_reflectionZero_eq_average_rotation_reflection_character
    [FiniteDimensional ℚ W]
    (ρ : Representation ℚ (DihedralGroup 19) W) :
    _root_.LinearMap.trace ℚ W
        (Representation.averageMap (ρ.comp d19RotationSubgroup.subtype) *
          ρ (DihedralGroup.sr (0 : ZMod 19))) =
      (19 : ℚ)⁻¹ *
        ∑ d : ZMod 19,
          ρ.character (DihedralGroup.r d * DihedralGroup.sr (0 : ZMod 19)) := by
  have hcard : Fintype.card ↥d19RotationSubgroup = 19 := by
    calc
      Fintype.card ↥d19RotationSubgroup = Fintype.card (ZMod 19) :=
        Fintype.card_congr d19RotationSubgroupEquiv.symm
      _ = 19 := by rw [ZMod.card]
  simp [Representation.averageMap, GroupAlgebra.average, hcard]
  rw [Finset.sum_mul]
  rw [map_sum]
  rw [← Equiv.sum_comp d19RotationSubgroupEquiv
      (fun c : ↥d19RotationSubgroup =>
        _root_.LinearMap.trace ℚ W
          (ρ ↑c * ρ (DihedralGroup.sr (0 : ZMod 19))))]
  simp [d19RotationSubgroupEquiv, Representation.character, ← map_mul,
    DihedralGroup.r_mul_sr]

theorem trace_averageMap_mul_reflectionZero_eq_reflection_character
    [FiniteDimensional ℚ W]
    (ρ : Representation ℚ (DihedralGroup 19) W) :
    _root_.LinearMap.trace ℚ W
        (Representation.averageMap (ρ.comp d19RotationSubgroup.subtype) *
          ρ (DihedralGroup.sr (0 : ZMod 19))) =
      ρ.character (DihedralGroup.sr (0 : ZMod 19)) := by
  rw [trace_averageMap_mul_reflectionZero_eq_average_rotation_reflection_character]
  exact average_rotation_reflection_character_eq_reflection_character ρ

theorem trace_restrict_rotationAverageRange_reflectionZero_eq_reflection_character
    [FiniteDimensional ℚ W]
    (ρ : Representation ℚ (DihedralGroup 19) W) :
    _root_.LinearMap.trace ℚ
        (_root_.LinearMap.range
          (Representation.averageMap (ρ.comp d19RotationSubgroup.subtype)))
        ((ρ (DihedralGroup.sr (0 : ZMod 19))).restrict (by
          intro x hx
          exact ((Module.End.mem_invtSubmodule_iff_mapsTo
            (f := ρ (DihedralGroup.sr (0 : ZMod 19)))).mp
              ((_root_.LinearMap.IsIdempotentElem.commute_iff
                ((Representation.isProj_averageMap
                  (ρ.comp d19RotationSubgroup.subtype)).isIdempotentElem)
                (T := ρ (DihedralGroup.sr (0 : ZMod 19)))).mp
                (d19RotationAverageMap_commute_reflectionZero ρ)).1) hx)) =
      ρ.character (DihedralGroup.sr (0 : ZMod 19)) := by
  have hcomm :
      Commute
        (Representation.averageMap (ρ.comp d19RotationSubgroup.subtype))
        (ρ (DihedralGroup.sr (0 : ZMod 19))) :=
    d19RotationAverageMap_commute_reflectionZero ρ
  rw [Moore57.LinearMap.trace_restrict_range_eq_trace_comp_of_isIdempotentElem
    (p := Representation.averageMap (ρ.comp d19RotationSubgroup.subtype))
    (f := ρ (DihedralGroup.sr (0 : ZMod 19)))
    ((Representation.isProj_averageMap
      (ρ.comp d19RotationSubgroup.subtype)).isIdempotentElem) hcomm]
  change
    _root_.LinearMap.trace ℚ W
        (Representation.averageMap (ρ.comp d19RotationSubgroup.subtype) *
          ρ (DihedralGroup.sr (0 : ZMod 19))) =
      ρ.character (DihedralGroup.sr (0 : ZMod 19))
  exact trace_averageMap_mul_reflectionZero_eq_reflection_character ρ

theorem trace_reflectionZeroOnRotationInvariants_eq_reflection_character
    [FiniteDimensional ℚ W]
    (ρ : Representation ℚ (DihedralGroup 19) W) :
    _root_.LinearMap.trace ℚ (d19RotationInvariantSubmodule ρ)
        (reflectionZeroOnRotationInvariants ρ) =
      ρ.character (DihedralGroup.sr (0 : ZMod 19)) := by
  let p := Representation.averageMap (ρ.comp d19RotationSubgroup.subtype)
  let f := ρ (DihedralGroup.sr (0 : ZMod 19))
  have hproj :
      _root_.LinearMap.IsProj (d19RotationInvariantSubmodule ρ) p :=
    Representation.isProj_averageMap (ρ.comp d19RotationSubgroup.subtype)
  let e : _root_.LinearMap.range p ≃ₗ[ℚ] d19RotationInvariantSubmodule ρ :=
    LinearEquiv.ofEq _ _ hproj.range
  let frange : _root_.LinearMap.range p →ₗ[ℚ] _root_.LinearMap.range p :=
    f.restrict (by
      intro x hx
      exact ((Module.End.mem_invtSubmodule_iff_mapsTo (f := f)).mp
        ((_root_.LinearMap.IsIdempotentElem.commute_iff hproj.isIdempotentElem
          (T := f)).mp (d19RotationAverageMap_commute_reflectionZero ρ)).1) hx)
  have heq : e.conj frange = reflectionZeroOnRotationInvariants ρ := by
    ext x
    rfl
  have hconj := _root_.LinearMap.trace_conj' frange e
  rw [heq] at hconj
  rw [hconj]
  dsimp [frange, p, f]
  exact trace_restrict_rotationAverageRange_reflectionZero_eq_reflection_character ρ

theorem exists_nat_reflectionCharacter_from_rotationInvariants
    [FiniteDimensional ℚ W]
    (ρ : Representation ℚ (DihedralGroup 19) W) :
    ∃ alpha beta : ℕ,
      Module.finrank ℚ (d19RotationInvariantSubmodule ρ) = alpha + beta ∧
        ρ.character (DihedralGroup.sr (0 : ZMod 19)) =
          (alpha : ℚ) - (beta : ℚ) := by
  rcases exists_nat_trace_reflectionZeroOnRotationInvariants ρ with
    ⟨alpha, beta, hdim, htrace⟩
  refine ⟨alpha, beta, hdim, ?_⟩
  rw [← trace_reflectionZeroOnRotationInvariants_eq_reflection_character ρ]
  rw [htrace]
  norm_num

theorem exists_nat_reflectionClassCharacter_from_rotationInvariants
    [FiniteDimensional ℚ W]
    (ρ : Representation ℚ (DihedralGroup 19) W) :
    ∃ alpha beta : ℕ,
      Module.finrank ℚ (d19RotationInvariantSubmodule ρ) = alpha + beta ∧
        ∀ k : ZMod 19,
          ρ.character (DihedralGroup.sr k) =
            (alpha : ℚ) - (beta : ℚ) := by
  rcases exists_nat_reflectionCharacter_from_rotationInvariants ρ with
    ⟨alpha, beta, hdim, hreflection⟩
  refine ⟨alpha, beta, hdim, ?_⟩
  intro k
  rw [representationCharacter_reflection_eq_reflection_zero_from_rotation ρ k]
  exact hreflection

end

end Moore57
