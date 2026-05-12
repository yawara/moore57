import Moore57.D19OnMoore57.E7Projection.Minus8D19TraceInputComplementBoundary
import Moore57.D19OnMoore57.Misc.CharacterInputPackaging

/-!
# D19 character input plus complementary minus-8 boundary

This file lifts the complementary `(-8)` route from `D19TraceInput h` to the
coarser character-input surfaces.  The proofs are thin wrappers through
`D19CharacterInput.toD19TraceInput` or the split
`D19RepresentationCharacterInput.toD19TraceInput` packaging.
-/

namespace Moore57

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

namespace D19ActsOnMoore57

namespace E7Minus8CharacterReflectionCountBoundary

variable (h : D19ActsOnMoore57 V Γ)

/-- Build the packaged E7/minus-8 boundary from the coarse character input,
using the complementary minus-8 route and the standard reflection
representative counts. -/
def ofD19CharacterInputComplement
    (characterInput : D19CharacterInput h)
    (reflection_fixed_count :
      fixedVertexCount (h.smulEquiv (DihedralGroup.sr 0)) = 56)
    (reflection_adjacent_moved :
      adjacentMovedCount Γ (h.smulEquiv (DihedralGroup.sr 0)) = 112) :
    E7Minus8CharacterReflectionCountBoundary h :=
  ofD19TraceInputComplement h characterInput.toD19TraceInput
    reflection_fixed_count reflection_adjacent_moved

/-- Fixed-star variant of `ofD19CharacterInputComplement`. -/
def ofD19CharacterInputComplementAndReflectionStar
    (characterInput : D19CharacterInput h)
    (hStar :
      InvolutionFixedSetStar56 Γ (h.smulEquiv (DihedralGroup.sr 0))) :
    E7Minus8CharacterReflectionCountBoundary h :=
  ofD19TraceInputComplementAndReflectionStar h
    characterInput.toD19TraceInput hStar

/-- Build the packaged E7/minus-8 boundary from the split representation
character input and the coarse fixed-count upper-bound input. -/
def ofD19RepresentationCharacterInputComplement
    (representation : D19RepresentationCharacterInput h)
    (fixedUpperBound : RotationFixedUpperBoundInput h)
    (reflection_fixed_count :
      fixedVertexCount (h.smulEquiv (DihedralGroup.sr 0)) = 56)
    (reflection_adjacent_moved :
      adjacentMovedCount Γ (h.smulEquiv (DihedralGroup.sr 0)) = 112) :
    E7Minus8CharacterReflectionCountBoundary h :=
  ofD19TraceInputComplement h
    (representation.toD19TraceInput fixedUpperBound)
    reflection_fixed_count reflection_adjacent_moved

end E7Minus8CharacterReflectionCountBoundary

/-- `D19CharacterInput` plus the standard reflection counts gives a nonempty
linear-character input through the complementary minus-8 route. -/
theorem nonempty_d19LinearCharacterInput_of_d19CharacterInputComplement
    (h : D19ActsOnMoore57 V Γ)
    (characterInput : D19CharacterInput h)
    (reflection_fixed_count :
      fixedVertexCount (h.smulEquiv (DihedralGroup.sr 0)) = 56)
    (reflection_adjacent_moved :
      adjacentMovedCount Γ (h.smulEquiv (DihedralGroup.sr 0)) = 112) :
    Nonempty (D19LinearCharacterInput h) :=
  nonempty_d19LinearCharacterInput_of_d19TraceInputComplement h
    characterInput.toD19TraceInput
    reflection_fixed_count reflection_adjacent_moved

/-- The complementary `D19CharacterInput` route gives the paper-shaped
fixed-star boundary for any reflection. -/
theorem involutionFixedSetStar56_of_d19CharacterInputComplement_raw_reflection
    (h : D19ActsOnMoore57 V Γ)
    (characterInput : D19CharacterInput h)
    (reflection_fixed_count :
      fixedVertexCount (h.smulEquiv (DihedralGroup.sr 0)) = 56)
    (reflection_adjacent_moved :
      adjacentMovedCount Γ (h.smulEquiv (DihedralGroup.sr 0)) = 112)
    (k : ZMod 19) :
    InvolutionFixedSetStar56 Γ (h.smulEquiv (DihedralGroup.sr k)) :=
  involutionFixedSetStar56_of_d19TraceInputComplement_raw_reflection h
    characterInput.toD19TraceInput
    reflection_fixed_count reflection_adjacent_moved k

/-- The complementary `D19CharacterInput` route gives a nonempty `K_{1,55}`
witness for any reflection. -/
theorem nonempty_involutionK155_of_d19CharacterInputComplement_raw_reflection
    (h : D19ActsOnMoore57 V Γ)
    (characterInput : D19CharacterInput h)
    (reflection_fixed_count :
      fixedVertexCount (h.smulEquiv (DihedralGroup.sr 0)) = 56)
    (reflection_adjacent_moved :
      adjacentMovedCount Γ (h.smulEquiv (DihedralGroup.sr 0)) = 112)
    (k : ZMod 19) :
    Nonempty (InvolutionK155 Γ (h.smulEquiv (DihedralGroup.sr k))) :=
  nonempty_involutionK155_of_d19TraceInputComplement_raw_reflection h
    characterInput.toD19TraceInput
    reflection_fixed_count reflection_adjacent_moved k

/-- The complementary `D19CharacterInput` route gives the fixed-center leaf
boundary. -/
theorem reflectionFixedCenterLeafBoundary_of_d19CharacterInputComplement
    (h : D19ActsOnMoore57 V Γ)
    (characterInput : D19CharacterInput h)
    (reflection_fixed_count :
      fixedVertexCount (h.smulEquiv (DihedralGroup.sr 0)) = 56)
    (reflection_adjacent_moved :
      adjacentMovedCount Γ (h.smulEquiv (DihedralGroup.sr 0)) = 112) :
    ReflectionFixedCenterLeafBoundary h :=
  reflectionFixedCenterLeafBoundary_of_d19TraceInputComplement h
    characterInput.toD19TraceInput
    reflection_fixed_count reflection_adjacent_moved

/-- The complementary `D19CharacterInput` route gives the representation
character component boundary. -/
theorem representationCharacterComponentsBoundary_of_d19CharacterInputComplement
    (h : D19ActsOnMoore57 V Γ)
    (characterInput : D19CharacterInput h)
    (reflection_fixed_count :
      fixedVertexCount (h.smulEquiv (DihedralGroup.sr 0)) = 56)
    (reflection_adjacent_moved :
      adjacentMovedCount Γ (h.smulEquiv (DihedralGroup.sr 0)) = 112) :
    RepresentationCharacterComponentsBoundary h :=
  representationCharacterComponentsBoundary_of_d19TraceInputComplement h
    characterInput.toD19TraceInput
    reflection_fixed_count reflection_adjacent_moved

/-- The complementary `D19CharacterInput` route rules out the current final-gap
boundary. -/
theorem no_currentFinalGapBoundary_of_d19CharacterInputComplement
    (h : D19ActsOnMoore57 V Γ)
    (characterInput : D19CharacterInput h)
    (reflection_fixed_count :
      fixedVertexCount (h.smulEquiv (DihedralGroup.sr 0)) = 56)
    (reflection_adjacent_moved :
      adjacentMovedCount Γ (h.smulEquiv (DihedralGroup.sr 0)) = 112) :
    ¬ Nonempty (BranchOrbitABCCurrentFinalGapBoundary h) :=
  no_currentFinalGapBoundary_of_d19TraceInputComplement h
    characterInput.toD19TraceInput
    reflection_fixed_count reflection_adjacent_moved

/-- Fixed-star input variant of
`nonempty_d19LinearCharacterInput_of_d19CharacterInputComplement`. -/
theorem nonempty_d19LinearCharacterInput_of_d19CharacterInputComplementAndReflectionStar
    (h : D19ActsOnMoore57 V Γ)
    (characterInput : D19CharacterInput h)
    (hStar :
      InvolutionFixedSetStar56 Γ (h.smulEquiv (DihedralGroup.sr 0))) :
    Nonempty (D19LinearCharacterInput h) :=
  nonempty_d19LinearCharacterInput_of_d19TraceInputComplementAndReflectionStar h
    characterInput.toD19TraceInput hStar

/-- Fixed-star input variant of
`involutionFixedSetStar56_of_d19CharacterInputComplement_raw_reflection`. -/
theorem involutionFixedSetStar56_of_d19CharacterInputComplementAndReflectionStar_raw_reflection
    (h : D19ActsOnMoore57 V Γ)
    (characterInput : D19CharacterInput h)
    (hStar :
      InvolutionFixedSetStar56 Γ (h.smulEquiv (DihedralGroup.sr 0)))
    (k : ZMod 19) :
    InvolutionFixedSetStar56 Γ (h.smulEquiv (DihedralGroup.sr k)) :=
  involutionFixedSetStar56_of_d19TraceInputComplementAndReflectionStar_raw_reflection h
    characterInput.toD19TraceInput hStar k

/-- Fixed-star input variant of
`nonempty_involutionK155_of_d19CharacterInputComplement_raw_reflection`. -/
theorem nonempty_involutionK155_of_d19CharacterInputComplementAndReflectionStar_raw_reflection
    (h : D19ActsOnMoore57 V Γ)
    (characterInput : D19CharacterInput h)
    (hStar :
      InvolutionFixedSetStar56 Γ (h.smulEquiv (DihedralGroup.sr 0)))
    (k : ZMod 19) :
    Nonempty (InvolutionK155 Γ (h.smulEquiv (DihedralGroup.sr k))) :=
  nonempty_involutionK155_of_d19TraceInputComplementAndReflectionStar_raw_reflection h
    characterInput.toD19TraceInput hStar k

/-- Fixed-star input variant of
`reflectionFixedCenterLeafBoundary_of_d19CharacterInputComplement`. -/
theorem reflectionFixedCenterLeafBoundary_of_d19CharacterInputComplementAndReflectionStar
    (h : D19ActsOnMoore57 V Γ)
    (characterInput : D19CharacterInput h)
    (hStar :
      InvolutionFixedSetStar56 Γ (h.smulEquiv (DihedralGroup.sr 0))) :
    ReflectionFixedCenterLeafBoundary h :=
  reflectionFixedCenterLeafBoundary_of_d19TraceInputComplementAndReflectionStar h
    characterInput.toD19TraceInput hStar

/-- Fixed-star input variant of
`representationCharacterComponentsBoundary_of_d19CharacterInputComplement`. -/
theorem representationCharacterComponentsBoundary_of_d19CharacterInputComplementAndReflectionStar
    (h : D19ActsOnMoore57 V Γ)
    (characterInput : D19CharacterInput h)
    (hStar :
      InvolutionFixedSetStar56 Γ (h.smulEquiv (DihedralGroup.sr 0))) :
    RepresentationCharacterComponentsBoundary h :=
  representationCharacterComponentsBoundary_of_d19TraceInputComplementAndReflectionStar h
    characterInput.toD19TraceInput hStar

/-- Fixed-star input variant of
`no_currentFinalGapBoundary_of_d19CharacterInputComplement`. -/
theorem no_currentFinalGapBoundary_of_d19CharacterInputComplementAndReflectionStar
    (h : D19ActsOnMoore57 V Γ)
    (characterInput : D19CharacterInput h)
    (hStar :
      InvolutionFixedSetStar56 Γ (h.smulEquiv (DihedralGroup.sr 0))) :
    ¬ Nonempty (BranchOrbitABCCurrentFinalGapBoundary h) :=
  no_currentFinalGapBoundary_of_d19TraceInputComplementAndReflectionStar h
    characterInput.toD19TraceInput hStar

end D19ActsOnMoore57

end

end Moore57
