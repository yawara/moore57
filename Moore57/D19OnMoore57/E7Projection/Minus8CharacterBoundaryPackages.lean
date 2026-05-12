import Moore57.D19OnMoore57.E7Projection.Minus8CountRawReflectionStarConnectors
import Moore57.D19OnMoore57.LinearCharacter.Nonempty

/-!
# Packaged E7/minus-8 character boundaries

This file bundles the concrete E7 and `(-8)` projection character boundaries
with the count-side inputs required to produce a nonempty
`D19LinearCharacterInput`.  The package is Type-valued so downstream code can
extract the multiplicities and character witnesses when needed.
-/

namespace Moore57

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

namespace D19ActsOnMoore57

/-- Concrete E7/minus-8 character boundary data together with the reflection
and rotation count inputs needed by the linear-character constructor. -/
structure E7Minus8CharacterReflectionCountBoundary
    (h : D19ActsOnMoore57 V Γ) where
  alpha : ℕ
  beta : ℕ
  gamma : ℕ
  A : ℕ
  B : ℕ
  C : ℕ
  e7Class :
    D19CharacterClassBoundary h.e7ProjectionRepresentation alpha beta gamma
  minus8Values :
    D19CharacterValueBoundary h.minus8ProjectionRepresentation A B C
  dt : ZMod 19
  reflection_fixed_count :
    fixedVertexCount (h.smulEquiv (DihedralGroup.sr dt)) = 56
  reflection_adjacent_moved :
    adjacentMovedCount Γ (h.smulEquiv (DihedralGroup.sr dt)) = 112
  rotation_fixed_count :
    ∀ d : ZMod 19, d ≠ 0 →
      fixedVertexCount (h.smulEquiv (DihedralGroup.r d)) = 1

namespace E7Minus8CharacterReflectionCountBoundary

variable {h : D19ActsOnMoore57 V Γ}

/-- Lower the packaged concrete projection character boundary to a nonempty
linear-character input. -/
theorem nonempty_d19LinearCharacterInput
    (boundary : E7Minus8CharacterReflectionCountBoundary h) :
    Nonempty (D19LinearCharacterInput h) :=
  D19LinearCharacterInput.nonempty_ofE7AndMinus8CharacterBoundaries h
    boundary.alpha boundary.beta boundary.gamma
    boundary.A boundary.B boundary.C
    boundary.e7Class boundary.minus8Values
    boundary.reflection_fixed_count
    boundary.reflection_adjacent_moved
    boundary.rotation_fixed_count

/-- The packaged boundary gives the raw-reflection paper-shaped fixed star for
any reflection. -/
theorem involutionFixedSetStar56_raw_reflection
    (boundary : E7Minus8CharacterReflectionCountBoundary h) (k : ZMod 19) :
    InvolutionFixedSetStar56 Γ (h.smulEquiv (DihedralGroup.sr k)) :=
  involutionFixedSetStar56_of_E7AndMinus8CharacterBoundariesAndReflectionCounts_raw_reflection
    h boundary.alpha boundary.beta boundary.gamma
    boundary.A boundary.B boundary.C
    boundary.e7Class boundary.minus8Values
    boundary.reflection_fixed_count
    boundary.reflection_adjacent_moved
    boundary.rotation_fixed_count k

/-- The packaged boundary gives the raw-reflection `K_{1,55}` witness for any
reflection. -/
theorem nonempty_involutionK155_raw_reflection
    (boundary : E7Minus8CharacterReflectionCountBoundary h) (k : ZMod 19) :
    Nonempty (InvolutionK155 Γ (h.smulEquiv (DihedralGroup.sr k))) :=
  nonempty_involutionK155_of_E7AndMinus8CharacterBoundariesAndReflectionCounts_raw_reflection
    h boundary.alpha boundary.beta boundary.gamma
    boundary.A boundary.B boundary.C
    boundary.e7Class boundary.minus8Values
    boundary.reflection_fixed_count
    boundary.reflection_adjacent_moved
    boundary.rotation_fixed_count k

/-- The packaged boundary gives reflection fixed count `56` for any
reflection. -/
theorem fixedVertexCount_reflection_eq_56_raw_reflection
    (boundary : E7Minus8CharacterReflectionCountBoundary h) (k : ZMod 19) :
    fixedVertexCount (h.smulEquiv (DihedralGroup.sr k)) = 56 :=
  fixedVertexCount_reflection_eq_56_of_nonempty_linearCharacterInput_raw_reflection
    boundary.nonempty_d19LinearCharacterInput k

/-- The packaged boundary gives reflection adjacent-moved count `112` for any
reflection. -/
theorem adjacentMovedCount_reflection_eq_112_raw_reflection
    (boundary : E7Minus8CharacterReflectionCountBoundary h) (k : ZMod 19) :
    adjacentMovedCount Γ (h.smulEquiv (DihedralGroup.sr k)) = 112 :=
  adjacentMovedCount_reflection_eq_112_of_nonempty_linearCharacterInput_raw_reflection
    boundary.nonempty_d19LinearCharacterInput k

/-- The packaged boundary eliminates the regular-`10` branch of the raw split,
hence gives the fixed-center leaf boundary. -/
theorem reflectionFixedCenterLeafBoundary
    (boundary : E7Minus8CharacterReflectionCountBoundary h) :
    ReflectionFixedCenterLeafBoundary h :=
  reflectionFixedCenterLeafBoundary_of_nonempty_linearCharacterInput
    boundary.nonempty_d19LinearCharacterInput

/-- The packaged boundary supplies the representation component boundary. -/
theorem representationCharacterComponentsBoundary
    (boundary : E7Minus8CharacterReflectionCountBoundary h) :
    RepresentationCharacterComponentsBoundary h :=
  representationCharacterComponentsBoundary_of_nonempty_linearCharacterInput
    boundary.nonempty_d19LinearCharacterInput

/-- The packaged boundary rules out the current final-gap frontier. -/
theorem no_currentFinalGapBoundary
    (boundary : E7Minus8CharacterReflectionCountBoundary h) :
    ¬ Nonempty (BranchOrbitABCCurrentFinalGapBoundary h) :=
  no_D19_currentFinalGapBoundary_of_nonempty_linearCharacterInput h
    boundary.nonempty_d19LinearCharacterInput

end E7Minus8CharacterReflectionCountBoundary

end D19ActsOnMoore57

end

end Moore57
