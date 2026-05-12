import Moore57.D19OnMoore57.Reflection.ReflectionRawGeometrySplit
import Moore57.D19OnMoore57.Reflection.ReflectionRegularTenCharacterBoundary

/-!
# Linear-character bridge for the raw reflection geometry split

This file connects the raw reflection split to the full D19 linear-character
input: the regular-`10` branch is incompatible with the packaged reflection
character value, so the split always lands in the fixed-center leaf boundary.
-/

namespace Moore57

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

namespace D19ActsOnMoore57

variable {h : D19ActsOnMoore57 V Γ}

namespace D19LinearCharacterInput

/-- A full linear-character input excludes the regular-`10` raw reflection
branch. -/
theorem no_reflectionRegularTenAllCenterNeighborOrbitsPreserved
    (hin : D19LinearCharacterInput h) (k : ZMod 19) :
    ¬ ReflectionRegularTenAllCenterNeighborOrbitsPreserved h k := by
  intro hreg
  exact hreg.not_d19LinearCharacterInput ⟨hin⟩

/-- Under a full linear-character input, the raw reflection split yields the
fixed-center leaf boundary. -/
theorem reflectionFixedCenterLeafBoundary
    (hin : D19LinearCharacterInput h) :
    ReflectionFixedCenterLeafBoundary h := by
  rcases h.reflectionFixedCenterLeafBoundary_or_exists_regularTenAllCenterNeighborOrbitsPreserved with
    hleaf | ⟨k, hreg⟩
  · exact hleaf
  · exact False.elim
      ((hin.no_reflectionRegularTenAllCenterNeighborOrbitsPreserved k) hreg)

end D19LinearCharacterInput

end D19ActsOnMoore57

end

end Moore57
