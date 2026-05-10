import Moore57.GroupAction.FixedPointConjugacy
import Moore57.GroupTheory.Dihedral19CharacterValueReduction

/-!
# Reflection conjugacy consequences

All reflections in `D19` are conjugate when the rotation order is `19`.  This
file records the corresponding fixed-count equality for a raw
`D19ActsOnMoore57` action.
-/

namespace Moore57

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

namespace D19ActsOnMoore57

variable (h : D19ActsOnMoore57 V Γ)

/-- All reflection fixed-point counts agree with the `sr 0` representative. -/
theorem fixedVertexCount_reflection_eq_reflection_zero (k : ZMod 19) :
    fixedVertexCount (h.smulEquiv (DihedralGroup.sr k)) =
      fixedVertexCount (h.smulEquiv (DihedralGroup.sr 0)) := by
  rcases dihedral19_reflection_conj_zero k with ⟨a, ha⟩
  have hconj :
      h.smulEquiv (DihedralGroup.sr k) =
        h.smulEquiv (DihedralGroup.r a) *
          h.smulEquiv (DihedralGroup.sr 0) *
            (h.smulEquiv (DihedralGroup.r a))⁻¹ := by
    have hinv :
        h.smulEquiv ((DihedralGroup.r a)⁻¹) =
          (h.smulEquiv (DihedralGroup.r a))⁻¹ := by
      ext v
      rfl
    rw [← ha, h.smulEquiv_mul, h.smulEquiv_mul, hinv]
  rw [hconj]
  exact fixedVertexCount_conj
    (h.smulEquiv (DihedralGroup.r a))
    (h.smulEquiv (DihedralGroup.sr 0))

end D19ActsOnMoore57

end

end Moore57
