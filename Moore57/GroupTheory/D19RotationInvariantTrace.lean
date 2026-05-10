import Moore57.LinearAlgebra.InvolutionTrace
import Moore57.GroupTheory.Dihedral19LinearCharacter
import Mathlib.RepresentationTheory.Character
import Mathlib.Tactic

/-!
# The reflection trace on the D19 rotation-invariant summand

This file isolates a representation-theoretic piece of the D19 character
argument.  For any rational representation of `D19`, the subspace fixed by the
rotation subgroup is preserved by the reflection `sr 0`; the restricted
reflection is an involution, so its trace is a difference of two natural
multiplicities.  This is the Lean-side version of the trivial/sign split on
the rotation-invariant part of the representation.
-/

namespace Moore57

noncomputable section

/-- The submodule fixed pointwise by the rotation subgroup of `D19`. -/
def d19RotationInvariantSubmodule
    {W : Type*} [AddCommGroup W] [Module ℚ W]
    (ρ : Representation ℚ (DihedralGroup 19) W) : Submodule ℚ W where
  carrier := {x | ∀ d : ZMod 19, ρ (DihedralGroup.r d) x = x}
  zero_mem' := by
    intro d
    simp
  add_mem' := by
    intro x y hx hy d
    simp [hx d, hy d]
  smul_mem' := by
    intro c x hx d
    simp [hx d]

/-- The reflection `sr 0`, restricted to the rotation-invariant submodule. -/
def reflectionZeroOnRotationInvariants
    {W : Type*} [AddCommGroup W] [Module ℚ W]
    (ρ : Representation ℚ (DihedralGroup 19) W) :
    d19RotationInvariantSubmodule ρ →ₗ[ℚ]
      d19RotationInvariantSubmodule ρ where
  toFun x :=
    ⟨ρ (DihedralGroup.sr (0 : ZMod 19)) (x : W), by
      intro d
      have hmul :
          DihedralGroup.r d * DihedralGroup.sr (0 : ZMod 19) =
            DihedralGroup.sr (0 : ZMod 19) * DihedralGroup.r (-d) := by
        simp [DihedralGroup.r_mul_sr, DihedralGroup.sr_mul_r]
      calc
        ρ (DihedralGroup.r d)
            (ρ (DihedralGroup.sr (0 : ZMod 19)) (x : W))
            = ρ (DihedralGroup.r d * DihedralGroup.sr (0 : ZMod 19)) (x : W) := by
              rw [map_mul]
              rfl
        _ = ρ (DihedralGroup.sr (0 : ZMod 19) * DihedralGroup.r (-d)) (x : W) := by
              rw [hmul]
        _ = ρ (DihedralGroup.sr (0 : ZMod 19))
            (ρ (DihedralGroup.r (-d)) (x : W)) := by
              rw [map_mul]
              rfl
        _ = ρ (DihedralGroup.sr (0 : ZMod 19)) (x : W) := by
              rw [x.property (-d)]⟩
  map_add' := by
    intro x y
    ext
    simp
  map_smul' := by
    intro c x
    ext
    simp

/-- The restricted reflection is an involution. -/
theorem reflectionZeroOnRotationInvariants_sq
    {W : Type*} [AddCommGroup W] [Module ℚ W]
    (ρ : Representation ℚ (DihedralGroup 19) W) :
    reflectionZeroOnRotationInvariants ρ *
        reflectionZeroOnRotationInvariants ρ = 1 := by
  ext x
  change
    ρ (DihedralGroup.sr (0 : ZMod 19))
        (ρ (DihedralGroup.sr (0 : ZMod 19)) (x : W)) = (x : W)
  rw [← Module.End.mul_apply]
  rw [← map_mul]
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
