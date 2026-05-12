import Moore57.D19OnMoore57.E7Projection.Minus8InversePairTraceCountRawReflectionStarConnectors
import Moore57.D19OnMoore57.LinearCharacter.NonemptyNoGoConnectors

/-!
# Boundary packages for inverse-pair E7/minus-8 trace data

This file bundles the inverse-pair trace boundaries together with the
count-side reflection and rotation inputs used to build
`Nonempty (D19LinearCharacterInput h)`.
-/

namespace Moore57

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

namespace D19ActsOnMoore57

/-- A compact package for the inverse-pair trace boundaries and the count-side
inputs needed by the linear-character bridge. -/
structure E7Minus8InversePairTraceReflectionCountBoundary
    (h : D19ActsOnMoore57 V Γ) where
  alpha : ℕ
  beta : ℕ
  gamma : ℕ
  A : ℕ
  B : ℕ
  C : ℕ
  e7Trace : E7ProjectionInversePairTraceBoundary h alpha beta gamma
  minus8Trace : Minus8ProjectionInversePairTraceBoundary h A B C
  dt : ZMod 19
  reflection_fixed_count :
    fixedVertexCount (h.smulEquiv (DihedralGroup.sr dt)) = 56
  reflection_adjacent_moved :
    adjacentMovedCount Γ (h.smulEquiv (DihedralGroup.sr dt)) = 112
  rotation_fixed_count :
    ∀ d : ZMod 19, d ≠ 0 →
      fixedVertexCount (h.smulEquiv (DihedralGroup.r d)) = 1

namespace E7Minus8InversePairTraceReflectionCountBoundary

variable {h : D19ActsOnMoore57 V Γ}

/-- The packaged trace and count inputs produce a nonempty linear-character
input. -/
theorem nonempty_d19LinearCharacterInput
    (boundary : E7Minus8InversePairTraceReflectionCountBoundary h) :
    Nonempty (D19LinearCharacterInput h) :=
  D19LinearCharacterInput.nonempty_ofE7AndMinus8InversePairTraceBoundaries
    h boundary.alpha boundary.beta boundary.gamma boundary.A boundary.B boundary.C
    boundary.e7Trace boundary.minus8Trace
    boundary.reflection_fixed_count boundary.reflection_adjacent_moved
    boundary.rotation_fixed_count

/-- The packaged boundary gives the raw-reflection paper-shaped
`56`-fixed-set star for any reflection. -/
theorem involutionFixedSetStar56_raw_reflection
    (boundary : E7Minus8InversePairTraceReflectionCountBoundary h)
    (k : ZMod 19) :
    InvolutionFixedSetStar56 Γ (h.smulEquiv (DihedralGroup.sr k)) :=
  involutionFixedSetStar56_of_E7AndMinus8InversePairTraceBoundariesAndReflectionCounts_raw_reflection
    h boundary.alpha boundary.beta boundary.gamma boundary.A boundary.B boundary.C
    boundary.e7Trace boundary.minus8Trace
    boundary.reflection_fixed_count boundary.reflection_adjacent_moved
    boundary.rotation_fixed_count k

/-- The packaged boundary gives a nonempty explicit `K_{1,55}` witness for any
reflection. -/
theorem nonempty_involutionK155_raw_reflection
    (boundary : E7Minus8InversePairTraceReflectionCountBoundary h)
    (k : ZMod 19) :
    Nonempty (InvolutionK155 Γ (h.smulEquiv (DihedralGroup.sr k))) :=
  nonempty_involutionK155_of_E7AndMinus8InversePairTraceBoundariesAndReflectionCounts_raw_reflection
    h boundary.alpha boundary.beta boundary.gamma boundary.A boundary.B boundary.C
    boundary.e7Trace boundary.minus8Trace
    boundary.reflection_fixed_count boundary.reflection_adjacent_moved
    boundary.rotation_fixed_count k

/-- The packaged inverse-pair trace boundary gives reflection fixed count `56`
for any reflection. -/
theorem fixedVertexCount_reflection_eq_56_raw_reflection
    (boundary : E7Minus8InversePairTraceReflectionCountBoundary h)
    (k : ZMod 19) :
    fixedVertexCount (h.smulEquiv (DihedralGroup.sr k)) = 56 :=
  fixedVertexCount_reflection_eq_56_of_nonempty_linearCharacterInput_raw_reflection
    boundary.nonempty_d19LinearCharacterInput k

/-- The packaged inverse-pair trace boundary gives reflection adjacent-moved
count `112` for any reflection. -/
theorem adjacentMovedCount_reflection_eq_112_raw_reflection
    (boundary : E7Minus8InversePairTraceReflectionCountBoundary h)
    (k : ZMod 19) :
    adjacentMovedCount Γ (h.smulEquiv (DihedralGroup.sr k)) = 112 :=
  adjacentMovedCount_reflection_eq_112_of_nonempty_linearCharacterInput_raw_reflection
    boundary.nonempty_d19LinearCharacterInput k

/-- The packaged inverse-pair trace boundary eliminates the regular-`10`
branch of the raw split, hence gives the fixed-center leaf boundary. -/
theorem reflectionFixedCenterLeafBoundary
    (boundary : E7Minus8InversePairTraceReflectionCountBoundary h) :
    ReflectionFixedCenterLeafBoundary h :=
  reflectionFixedCenterLeafBoundary_of_nonempty_linearCharacterInput
    boundary.nonempty_d19LinearCharacterInput

/-- The packaged inverse-pair trace boundary supplies the representation
component boundary. -/
theorem representationCharacterComponentsBoundary
    (boundary : E7Minus8InversePairTraceReflectionCountBoundary h) :
    RepresentationCharacterComponentsBoundary h :=
  representationCharacterComponentsBoundary_of_nonempty_linearCharacterInput
    boundary.nonempty_d19LinearCharacterInput

/-- Current-final-gap no-go from the packaged nonempty linear-character input. -/
theorem no_currentFinalGapBoundary
    (boundary : E7Minus8InversePairTraceReflectionCountBoundary h) :
    ¬ Nonempty (BranchOrbitABCCurrentFinalGapBoundary h) :=
  no_D19_currentFinalGapBoundary_of_nonempty_linearCharacterInput h
    boundary.nonempty_d19LinearCharacterInput

end E7Minus8InversePairTraceReflectionCountBoundary

end D19ActsOnMoore57

end

end Moore57
