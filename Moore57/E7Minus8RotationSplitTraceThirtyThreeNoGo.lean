import Moore57.E7Minus8CharacterBoundariesFromRotationSplit
import Moore57.D19LinearCharacterNonemptyNoGoConnectors

/-!
# Rotation-split no-go from a single E7 reflection trace value

The trace value `33` for one reflection forces the paper fixed count `56`.
Together with the rotation-split construction of the concrete E7 and `(-8)`
projection characters, this is enough to recover the old
`D19LinearCharacterInput` and hence the current-final-gap no-go.
-/

namespace Moore57

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

namespace D19ActsOnMoore57

/-- Per-reflection geometry consequence of E7 trace value `33`: the reflection
has fixed count `56`, hence the rotation-fixed center is a leaf of the
reflection fixed-induced graph. -/
theorem reflectionFixedCenterLeafAt_of_E7_reflection_trace_eq_33
    (h : D19ActsOnMoore57 V Γ)
    {dt : ZMod 19}
    (htrace33 :
      Matrix.trace (E7Matrix Γ * permMatrix (h.smulEquiv (DihedralGroup.sr dt))) =
        (33 : ℚ)) :
    ReflectionFixedCenterLeafAt h dt :=
  h.reflectionFixedCenterLeafAt_of_fixedVertexCount_eq_56 dt
    (h.fixedVertexCount_reflection_eq_56_of_E7_trace_eq_33 dt htrace33)

/-- Uniform E7 reflection trace value `33` gives the fixed-center leaf
boundary for all reflections. -/
theorem reflectionFixedCenterLeafBoundary_of_E7_reflection_trace_eq_33_all
    (h : D19ActsOnMoore57 V Γ)
    (htrace33 :
      ∀ dt : ZMod 19,
        Matrix.trace (E7Matrix Γ * permMatrix (h.smulEquiv (DihedralGroup.sr dt))) =
          (33 : ℚ)) :
    ReflectionFixedCenterLeafBoundary h where
  degree_le_one := by
    intro dt
    exact
      (h.reflectionFixedCenterLeafAt_of_E7_reflection_trace_eq_33
        (htrace33 dt)).degree_le_one

/-- Rotation-split character construction plus one E7 reflection trace value
`33` rules out the current final-gap boundary. -/
theorem no_currentFinalGapBoundary_of_rotation_split_and_E7_reflection_trace_eq_33
    (h : D19ActsOnMoore57 V Γ)
    {dt : ZMod 19}
    (htrace33 :
      Matrix.trace (E7Matrix Γ * permMatrix (h.smulEquiv (DihedralGroup.sr dt))) =
        (33 : ℚ)) :
    ¬ Nonempty (BranchOrbitABCCurrentFinalGapBoundary h) :=
  no_D19_currentFinalGapBoundary_of_nonempty_linearCharacterInput h
    (h.nonempty_d19LinearCharacterInput_of_rotation_split_and_E7_reflection_trace_eq_33
      htrace33)

/-- Uniform E7 reflection trace value `33` version of the rotation-split no-go. -/
theorem no_currentFinalGapBoundary_of_rotation_split_and_E7_reflection_trace_eq_33_all
    (h : D19ActsOnMoore57 V Γ)
    (htrace33 :
      ∀ dt : ZMod 19,
        Matrix.trace (E7Matrix Γ * permMatrix (h.smulEquiv (DihedralGroup.sr dt))) =
          (33 : ℚ)) :
    ¬ Nonempty (BranchOrbitABCCurrentFinalGapBoundary h) :=
  h.no_currentFinalGapBoundary_of_rotation_split_and_E7_reflection_trace_eq_33
    (htrace33 0)

end D19ActsOnMoore57

end

end Moore57
