import Moore57.Foundations.LinearAlgebra.InvolutionTrace
import Moore57.Foundations.GroupTheory.D19LinearCharacter
import Mathlib.RepresentationTheory.Character
import Mathlib.RepresentationTheory.Invariants
import Mathlib.Tactic

/-!
# The reflection trace on the D19 rotation-invariant summand

This file isolates a representation-theoretic piece of the D19 character
argument.  For any rational representation of `D19`, mathlib's invariant
submodule for the normal rotation subgroup is preserved by the reflection
`sr 0`; the restricted reflection is an involution, so its trace is a
difference of two natural multiplicities.  This is the Lean-side version of
the trivial/sign split on the rotation-invariant part of the representation.
-/

namespace Moore57

noncomputable section

/-- The rotation subgroup of `D19`, written as the rotations `r d`. -/
def d19RotationSubgroup : Subgroup (DihedralGroup 19) where
  carrier := {g | ∃ d : ZMod 19, g = DihedralGroup.r d}
  one_mem' := by
    exact ⟨0, by simp⟩
  mul_mem' := by
    intro a b ha hb
    rcases ha with ⟨i, rfl⟩
    rcases hb with ⟨j, rfl⟩
    exact ⟨i + j, by simp [DihedralGroup.r_mul_r]⟩
  inv_mem' := by
    intro a ha
    rcases ha with ⟨i, rfl⟩
    exact ⟨-i, by simp [DihedralGroup.inv_r]⟩

theorem d19RotationSubgroup_r (d : ZMod 19) :
    DihedralGroup.r d ∈ d19RotationSubgroup :=
  ⟨d, rfl⟩

/-- The rotation subgroup is indexed by the rotation exponent. -/
def d19RotationSubgroupEquiv : ZMod 19 ≃ ↥d19RotationSubgroup where
  toFun d := ⟨DihedralGroup.r d, d19RotationSubgroup_r d⟩
  invFun g :=
    match (g : DihedralGroup 19) with
    | DihedralGroup.r d => d
    | DihedralGroup.sr _ => 0
  left_inv d := rfl
  right_inv g := by
    rcases g with ⟨g, hg⟩
    rcases hg with ⟨d, hd⟩
    cases g with
    | r e =>
        cases hd
        rfl
    | sr e =>
        cases hd

instance d19RotationSubgroup_fintype : Fintype ↥d19RotationSubgroup :=
  Fintype.ofEquiv (ZMod 19) d19RotationSubgroupEquiv

instance d19RotationSubgroup_normal : d19RotationSubgroup.Normal where
  conj_mem := by
    intro n hn g
    rcases hn with ⟨d, rfl⟩
    cases g with
    | r a =>
        exact ⟨d, by simp [DihedralGroup.inv_r, DihedralGroup.r_mul_r]⟩
    | sr a =>
        exact ⟨-d, by
          simp [DihedralGroup.inv_sr, DihedralGroup.sr_mul_r,
            DihedralGroup.sr_mul_sr]⟩

/-- The submodule fixed pointwise by the rotation subgroup of `D19`.

This is deliberately mathlib's invariant submodule for the restricted
representation, with a project-specific name for readability. -/
abbrev d19RotationInvariantSubmodule
    {W : Type*} [AddCommGroup W] [Module ℚ W]
    (ρ : Representation ℚ (DihedralGroup 19) W) : Submodule ℚ W :=
  Representation.invariants (ρ.comp d19RotationSubgroup.subtype)

@[simp]
theorem mem_d19RotationInvariantSubmodule
    {W : Type*} [AddCommGroup W] [Module ℚ W]
    (ρ : Representation ℚ (DihedralGroup 19) W) (x : W) :
    x ∈ d19RotationInvariantSubmodule ρ ↔
      ∀ d : ZMod 19, ρ (DihedralGroup.r d) x = x := by
  constructor
  · intro hx d
    exact hx ⟨DihedralGroup.r d, d19RotationSubgroup_r d⟩
  · intro hx g
    rcases g.property with ⟨d, hg⟩
    change ρ (g : DihedralGroup 19) x = x
    rw [hg]
    exact hx d

/-- Mathlib's character average formula, specialized to the D19 rotation
subgroup.  This identifies the dimension of the rotation-invariant summand as
the average of the character on rotations. -/
theorem finrank_d19RotationInvariantSubmodule_eq_average_rotation_character
    {W : Type*} [AddCommGroup W] [Module ℚ W] [FiniteDimensional ℚ W]
    (ρ : Representation ℚ (DihedralGroup 19) W) :
    (19 : ℚ)⁻¹ * ∑ d : ZMod 19, ρ.character (DihedralGroup.r d) =
      (Module.finrank ℚ (d19RotationInvariantSubmodule ρ) : ℚ) := by
  have hcardZ : Nat.card (ZMod 19) = 19 := by
    rw [Nat.card_eq_fintype_card, ZMod.card]
  have hcard : Nat.card ↥d19RotationSubgroup = 19 := by
    calc
      Nat.card ↥d19RotationSubgroup = Nat.card (ZMod 19) :=
        Nat.card_congr d19RotationSubgroupEquiv.symm
      _ = 19 := hcardZ
  haveI : Invertible (Nat.card ↥d19RotationSubgroup : ℚ) := by
    rw [hcard]
    infer_instance
  have havg :=
    Representation.card_inv_mul_sum_char_eq_finrank
      (ρ := ρ.comp d19RotationSubgroup.subtype)
  have hsum :
      ∑ g : ↥d19RotationSubgroup,
          Representation.character (ρ.comp d19RotationSubgroup.subtype) g =
        ∑ d : ZMod 19, ρ.character (DihedralGroup.r d) := by
    rw [← Equiv.sum_comp d19RotationSubgroupEquiv
      (fun g : ↥d19RotationSubgroup =>
        Representation.character (ρ.comp d19RotationSubgroup.subtype) g)]
    rfl
  rw [← havg, hcard, hsum]
  norm_num

/-- The reflection `sr 0`, restricted to the rotation-invariant submodule. -/
abbrev reflectionZeroOnRotationInvariants
    {W : Type*} [AddCommGroup W] [Module ℚ W]
    (ρ : Representation ℚ (DihedralGroup 19) W) :
    d19RotationInvariantSubmodule ρ →ₗ[ℚ]
      d19RotationInvariantSubmodule ρ :=
  (ρ.toInvariants d19RotationSubgroup) (DihedralGroup.sr (0 : ZMod 19))

/-- The restricted reflection is an involution. -/
theorem reflectionZeroOnRotationInvariants_sq
    {W : Type*} [AddCommGroup W] [Module ℚ W]
    (ρ : Representation ℚ (DihedralGroup 19) W) :
    reflectionZeroOnRotationInvariants ρ *
        reflectionZeroOnRotationInvariants ρ = 1 := by
  change
    (ρ.toInvariants d19RotationSubgroup) (DihedralGroup.sr (0 : ZMod 19)) *
        (ρ.toInvariants d19RotationSubgroup) (DihedralGroup.sr (0 : ZMod 19)) = 1
  rw [← map_mul]
  ext x
  simp [DihedralGroup.sr_mul_sr]

/-- The trace of `sr 0` on the rotation-invariant submodule is the difference
of the `+1` and `-1` eigenspace dimensions. -/
theorem exists_nat_trace_reflectionZeroOnRotationInvariants
    {W : Type*} [AddCommGroup W] [Module ℚ W] [FiniteDimensional ℚ W]
    (ρ : Representation ℚ (DihedralGroup 19) W) :
    ∃ alpha beta : ℕ,
      Module.finrank ℚ (d19RotationInvariantSubmodule ρ) = alpha + beta ∧
        _root_.LinearMap.trace ℚ (d19RotationInvariantSubmodule ρ)
            (reflectionZeroOnRotationInvariants ρ) =
          ((alpha : ℤ) - (beta : ℤ) : ℚ) := by
  let U := d19RotationInvariantSubmodule ρ
  let f := reflectionZeroOnRotationInvariants ρ
  let p := LinearMap.involutionProjection f
  let n := Module.finrank ℚ U
  let alpha := Module.finrank ℚ (_root_.LinearMap.range p)
  let beta := n - alpha
  have halpha_le : alpha ≤ n := by
    dsimp [alpha, n, p, U]
    exact Submodule.finrank_le _
  refine ⟨alpha, beta, ?_, ?_⟩
  · dsimp [alpha, beta, n]
    change n = alpha + (n - alpha)
    exact (Nat.add_sub_of_le halpha_le).symm
  · have hf : f * f = 1 := by
      dsimp [f]
      exact reflectionZeroOnRotationInvariants_sq ρ
    have htrace :
        _root_.LinearMap.trace ℚ U f =
          (2 * (Module.finrank ℚ (_root_.LinearMap.range
              (LinearMap.involutionProjection f)) : ℤ) -
              (Module.finrank ℚ U : ℤ) : ℤ) :=
      LinearMap.trace_eq_two_finrank_involutionProjection_sub_finrank f hf
    have hInt :
        2 * (alpha : ℤ) - (n : ℤ) = (alpha : ℤ) - (beta : ℤ) := by
      dsimp [beta]
      omega
    dsimp [alpha, beta, n, p, f, U] at htrace ⊢
    rw [htrace]
    exact_mod_cast hInt

end

end Moore57
