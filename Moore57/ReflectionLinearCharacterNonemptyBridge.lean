import Moore57.ReflectionLinearRawReflectionK155Bridge
import Moore57.ReflectionLinearCharacterGeometrySplit

/-!
# Nonempty linear-character input reflection bridges

Some upstream constructors naturally produce `Nonempty (D19LinearCharacterInput h)`
rather than a named record.  This file exposes the existing raw-reflection
fixed-star, count, `K_{1,55}`, and fixed-center leaf consequences directly at
that `Nonempty` boundary.
-/

namespace Moore57

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

namespace D19ActsOnMoore57

variable {h : D19ActsOnMoore57 V Γ}

/-- A nonempty linear-character input supplies the raw-reflection
paper-shaped fixed star. -/
theorem involutionFixedSetStar56_of_nonempty_linearCharacterInput_raw_reflection
    (hin : Nonempty (D19LinearCharacterInput h)) (k : ZMod 19) :
    InvolutionFixedSetStar56 Γ (h.smulEquiv (DihedralGroup.sr k)) := by
  rcases hin with ⟨hin⟩
  exact hin.involutionFixedSetStar56_of_raw_reflection k

/-- A nonempty linear-character input supplies the raw-reflection
`K_{1,55}` witness. -/
theorem nonempty_involutionK155_of_nonempty_linearCharacterInput_raw_reflection
    (hin : Nonempty (D19LinearCharacterInput h)) (k : ZMod 19) :
    Nonempty (InvolutionK155 Γ (h.smulEquiv (DihedralGroup.sr k))) := by
  rcases hin with ⟨hin⟩
  exact hin.nonempty_involutionK155_of_raw_reflection k

/-- A nonempty linear-character input supplies the reflection fixed-count
`56`. -/
theorem fixedVertexCount_reflection_eq_56_of_nonempty_linearCharacterInput_raw_reflection
    (hin : Nonempty (D19LinearCharacterInput h)) (k : ZMod 19) :
    fixedVertexCount (h.smulEquiv (DihedralGroup.sr k)) = 56 := by
  rcases hin with ⟨hin⟩
  exact hin.fixedVertexCount_reflection_eq_56_of_raw_reflection k

/-- A nonempty linear-character input supplies the reflection adjacent-moved
count `112`. -/
theorem adjacentMovedCount_reflection_eq_112_of_nonempty_linearCharacterInput_raw_reflection
    (hin : Nonempty (D19LinearCharacterInput h)) (k : ZMod 19) :
    adjacentMovedCount Γ (h.smulEquiv (DihedralGroup.sr k)) = 112 := by
  rcases hin with ⟨hin⟩
  exact hin.adjacentMovedCount_reflection_eq_112_of_raw_reflection k

/-- A nonempty linear-character input eliminates the regular-`10` branch of
the raw split, hence gives the fixed-center leaf boundary. -/
theorem reflectionFixedCenterLeafBoundary_of_nonempty_linearCharacterInput
    (hin : Nonempty (D19LinearCharacterInput h)) :
    ReflectionFixedCenterLeafBoundary h := by
  rcases hin with ⟨hin⟩
  exact hin.reflectionFixedCenterLeafBoundary

end D19ActsOnMoore57

end

end Moore57
