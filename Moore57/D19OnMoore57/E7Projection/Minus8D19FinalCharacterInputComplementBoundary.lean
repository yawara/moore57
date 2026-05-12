import Moore57.D19OnMoore57.E7Projection.Minus8D19TraceInputComplementBoundary
import Moore57.D19OnMoore57.D19Core.ConstructiveFinalInputs

/-!
# Complementary minus-8 boundary from final character inputs

This file moves the complementary `(-8)` route one step above `D19TraceInput`.
The final character packages already split the representation-character input
from the rotation fixed-count upper-bound input; recombining those fields gives
the trace input consumed by
`E7Minus8CharacterReflectionCountBoundary.ofD19TraceInputComplement`.
-/

namespace Moore57

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

namespace D19FinalCharacterInputs

variable {h : D19ActsOnMoore57 V Γ}

/-- Recombine split final character inputs into the reduced trace input used by
the complementary `(-8)` route. -/
def toD19TraceInput (data : D19FinalCharacterInputs h) :
    D19TraceInput h :=
  data.representation.toD19TraceInput data.fixedUpperBound

end D19FinalCharacterInputs

namespace D19ActsOnMoore57

namespace E7Minus8CharacterReflectionCountBoundary

variable (h : D19ActsOnMoore57 V Γ)

/-- Build the packaged E7/minus-8 boundary from final character inputs, using
the complementary minus-8 projection formula and the standard reflection
representative counts. -/
def ofD19FinalCharacterInputsComplement
    (character : D19FinalCharacterInputs h)
    (reflection_fixed_count :
      fixedVertexCount (h.smulEquiv (DihedralGroup.sr 0)) = 56)
    (reflection_adjacent_moved :
      adjacentMovedCount Γ (h.smulEquiv (DihedralGroup.sr 0)) = 112) :
    E7Minus8CharacterReflectionCountBoundary h :=
  ofD19TraceInputComplement h character.toD19TraceInput
    reflection_fixed_count reflection_adjacent_moved

/-- Fixed-star variant of `ofD19FinalCharacterInputsComplement`. -/
def ofD19FinalCharacterInputsComplementAndReflectionStar
    (character : D19FinalCharacterInputs h)
    (hStar :
      InvolutionFixedSetStar56 Γ (h.smulEquiv (DihedralGroup.sr 0))) :
    E7Minus8CharacterReflectionCountBoundary h :=
  ofD19TraceInputComplementAndReflectionStar h character.toD19TraceInput hStar

end E7Minus8CharacterReflectionCountBoundary

/-- Final character inputs plus the standard reflection counts give a nonempty
linear-character input through the complementary minus-8 route. -/
theorem nonempty_d19LinearCharacterInput_of_d19FinalCharacterInputsComplement
    (h : D19ActsOnMoore57 V Γ)
    (character : D19FinalCharacterInputs h)
    (reflection_fixed_count :
      fixedVertexCount (h.smulEquiv (DihedralGroup.sr 0)) = 56)
    (reflection_adjacent_moved :
      adjacentMovedCount Γ (h.smulEquiv (DihedralGroup.sr 0)) = 112) :
    Nonempty (D19LinearCharacterInput h) :=
  (E7Minus8CharacterReflectionCountBoundary.ofD19FinalCharacterInputsComplement h
    character reflection_fixed_count reflection_adjacent_moved)
      |>.nonempty_d19LinearCharacterInput

/-- Final character inputs plus the standard reflection counts give the
paper-shaped fixed-star boundary for any reflection. -/
theorem involutionFixedSetStar56_of_d19FinalCharacterInputsComplement_raw_reflection
    (h : D19ActsOnMoore57 V Γ)
    (character : D19FinalCharacterInputs h)
    (reflection_fixed_count :
      fixedVertexCount (h.smulEquiv (DihedralGroup.sr 0)) = 56)
    (reflection_adjacent_moved :
      adjacentMovedCount Γ (h.smulEquiv (DihedralGroup.sr 0)) = 112)
    (k : ZMod 19) :
    InvolutionFixedSetStar56 Γ (h.smulEquiv (DihedralGroup.sr k)) :=
  (E7Minus8CharacterReflectionCountBoundary.ofD19FinalCharacterInputsComplement h
    character reflection_fixed_count reflection_adjacent_moved)
      |>.involutionFixedSetStar56_raw_reflection k

/-- Final character inputs plus the standard reflection counts give a nonempty
`K_{1,55}` witness for any reflection. -/
theorem nonempty_involutionK155_of_d19FinalCharacterInputsComplement_raw_reflection
    (h : D19ActsOnMoore57 V Γ)
    (character : D19FinalCharacterInputs h)
    (reflection_fixed_count :
      fixedVertexCount (h.smulEquiv (DihedralGroup.sr 0)) = 56)
    (reflection_adjacent_moved :
      adjacentMovedCount Γ (h.smulEquiv (DihedralGroup.sr 0)) = 112)
    (k : ZMod 19) :
    Nonempty (InvolutionK155 Γ (h.smulEquiv (DihedralGroup.sr k))) :=
  (E7Minus8CharacterReflectionCountBoundary.ofD19FinalCharacterInputsComplement h
    character reflection_fixed_count reflection_adjacent_moved)
      |>.nonempty_involutionK155_raw_reflection k

/-- Final character inputs plus the standard reflection counts give the
fixed-center leaf boundary. -/
theorem reflectionFixedCenterLeafBoundary_of_d19FinalCharacterInputsComplement
    (h : D19ActsOnMoore57 V Γ)
    (character : D19FinalCharacterInputs h)
    (reflection_fixed_count :
      fixedVertexCount (h.smulEquiv (DihedralGroup.sr 0)) = 56)
    (reflection_adjacent_moved :
      adjacentMovedCount Γ (h.smulEquiv (DihedralGroup.sr 0)) = 112) :
    ReflectionFixedCenterLeafBoundary h :=
  (E7Minus8CharacterReflectionCountBoundary.ofD19FinalCharacterInputsComplement h
    character reflection_fixed_count reflection_adjacent_moved)
      |>.reflectionFixedCenterLeafBoundary

/-- Final character inputs plus the standard reflection counts give the
representation character component boundary. -/
theorem representationCharacterComponentsBoundary_of_d19FinalCharacterInputsComplement
    (h : D19ActsOnMoore57 V Γ)
    (character : D19FinalCharacterInputs h)
    (reflection_fixed_count :
      fixedVertexCount (h.smulEquiv (DihedralGroup.sr 0)) = 56)
    (reflection_adjacent_moved :
      adjacentMovedCount Γ (h.smulEquiv (DihedralGroup.sr 0)) = 112) :
    RepresentationCharacterComponentsBoundary h :=
  (E7Minus8CharacterReflectionCountBoundary.ofD19FinalCharacterInputsComplement h
    character reflection_fixed_count reflection_adjacent_moved)
      |>.representationCharacterComponentsBoundary

/-- Final character inputs plus the standard reflection counts rule out the
current branch-orbit final-gap boundary. -/
theorem no_currentFinalGapBoundary_of_d19FinalCharacterInputsComplement
    (h : D19ActsOnMoore57 V Γ)
    (character : D19FinalCharacterInputs h)
    (reflection_fixed_count :
      fixedVertexCount (h.smulEquiv (DihedralGroup.sr 0)) = 56)
    (reflection_adjacent_moved :
      adjacentMovedCount Γ (h.smulEquiv (DihedralGroup.sr 0)) = 112) :
    ¬ Nonempty (BranchOrbitABCCurrentFinalGapBoundary h) :=
  (E7Minus8CharacterReflectionCountBoundary.ofD19FinalCharacterInputsComplement h
    character reflection_fixed_count reflection_adjacent_moved)
      |>.no_currentFinalGapBoundary

/-- Fixed-star input variant of
`nonempty_d19LinearCharacterInput_of_d19FinalCharacterInputsComplement`. -/
theorem nonempty_d19LinearCharacterInput_of_d19FinalCharacterInputsComplementAndReflectionStar
    (h : D19ActsOnMoore57 V Γ)
    (character : D19FinalCharacterInputs h)
    (hStar :
      InvolutionFixedSetStar56 Γ (h.smulEquiv (DihedralGroup.sr 0))) :
    Nonempty (D19LinearCharacterInput h) :=
  (E7Minus8CharacterReflectionCountBoundary.ofD19FinalCharacterInputsComplementAndReflectionStar
    h character hStar)
      |>.nonempty_d19LinearCharacterInput

/-- Fixed-star input variant of
`involutionFixedSetStar56_of_d19FinalCharacterInputsComplement_raw_reflection`. -/
theorem involutionFixedSetStar56_of_d19FinalCharacterInputsComplementAndReflectionStar_raw_reflection
    (h : D19ActsOnMoore57 V Γ)
    (character : D19FinalCharacterInputs h)
    (hStar :
      InvolutionFixedSetStar56 Γ (h.smulEquiv (DihedralGroup.sr 0)))
    (k : ZMod 19) :
    InvolutionFixedSetStar56 Γ (h.smulEquiv (DihedralGroup.sr k)) :=
  (E7Minus8CharacterReflectionCountBoundary.ofD19FinalCharacterInputsComplementAndReflectionStar
    h character hStar)
      |>.involutionFixedSetStar56_raw_reflection k

/-- Fixed-star input variant of
`nonempty_involutionK155_of_d19FinalCharacterInputsComplement_raw_reflection`. -/
theorem nonempty_involutionK155_of_d19FinalCharacterInputsComplementAndReflectionStar_raw_reflection
    (h : D19ActsOnMoore57 V Γ)
    (character : D19FinalCharacterInputs h)
    (hStar :
      InvolutionFixedSetStar56 Γ (h.smulEquiv (DihedralGroup.sr 0)))
    (k : ZMod 19) :
    Nonempty (InvolutionK155 Γ (h.smulEquiv (DihedralGroup.sr k))) :=
  (E7Minus8CharacterReflectionCountBoundary.ofD19FinalCharacterInputsComplementAndReflectionStar
    h character hStar)
      |>.nonempty_involutionK155_raw_reflection k

/-- Fixed-star input variant of
`reflectionFixedCenterLeafBoundary_of_d19FinalCharacterInputsComplement`. -/
theorem reflectionFixedCenterLeafBoundary_of_d19FinalCharacterInputsComplementAndReflectionStar
    (h : D19ActsOnMoore57 V Γ)
    (character : D19FinalCharacterInputs h)
    (hStar :
      InvolutionFixedSetStar56 Γ (h.smulEquiv (DihedralGroup.sr 0))) :
    ReflectionFixedCenterLeafBoundary h :=
  (E7Minus8CharacterReflectionCountBoundary.ofD19FinalCharacterInputsComplementAndReflectionStar
    h character hStar)
      |>.reflectionFixedCenterLeafBoundary

/-- Fixed-star input variant of
`representationCharacterComponentsBoundary_of_d19FinalCharacterInputsComplement`. -/
theorem representationCharacterComponentsBoundary_of_d19FinalCharacterInputsComplementAndReflectionStar
    (h : D19ActsOnMoore57 V Γ)
    (character : D19FinalCharacterInputs h)
    (hStar :
      InvolutionFixedSetStar56 Γ (h.smulEquiv (DihedralGroup.sr 0))) :
    RepresentationCharacterComponentsBoundary h :=
  (E7Minus8CharacterReflectionCountBoundary.ofD19FinalCharacterInputsComplementAndReflectionStar
    h character hStar)
      |>.representationCharacterComponentsBoundary

/-- Fixed-star input variant of
`no_currentFinalGapBoundary_of_d19FinalCharacterInputsComplement`. -/
theorem no_currentFinalGapBoundary_of_d19FinalCharacterInputsComplementAndReflectionStar
    (h : D19ActsOnMoore57 V Γ)
    (character : D19FinalCharacterInputs h)
    (hStar :
      InvolutionFixedSetStar56 Γ (h.smulEquiv (DihedralGroup.sr 0))) :
    ¬ Nonempty (BranchOrbitABCCurrentFinalGapBoundary h) :=
  (E7Minus8CharacterReflectionCountBoundary.ofD19FinalCharacterInputsComplementAndReflectionStar
    h character hStar)
      |>.no_currentFinalGapBoundary

namespace D19FinalInputs

variable {h : D19ActsOnMoore57 V Γ}

/-- Final inputs plus a fixed-star reflection input give a nonempty
linear-character input through the complementary minus-8 route. -/
theorem nonempty_d19LinearCharacterInput_of_complementAndReflectionStar
    (data : D19FinalInputs h)
    (hStar :
      InvolutionFixedSetStar56 Γ (h.smulEquiv (DihedralGroup.sr 0))) :
    Nonempty (D19LinearCharacterInput h) :=
  nonempty_d19LinearCharacterInput_of_d19FinalCharacterInputsComplementAndReflectionStar
    h data.character hStar

/-- Final inputs plus a fixed-star reflection input give fixed-star boundaries
for all reflections through the complementary minus-8 route. -/
theorem involutionFixedSetStar56_of_complementAndReflectionStar_raw_reflection
    (data : D19FinalInputs h)
    (hStar :
      InvolutionFixedSetStar56 Γ (h.smulEquiv (DihedralGroup.sr 0)))
    (k : ZMod 19) :
    InvolutionFixedSetStar56 Γ (h.smulEquiv (DihedralGroup.sr k)) :=
  involutionFixedSetStar56_of_d19FinalCharacterInputsComplementAndReflectionStar_raw_reflection
    h data.character hStar k

/-- Final inputs plus a fixed-star reflection input give `K_{1,55}` witnesses
for all reflections through the complementary minus-8 route. -/
theorem nonempty_involutionK155_of_complementAndReflectionStar_raw_reflection
    (data : D19FinalInputs h)
    (hStar :
      InvolutionFixedSetStar56 Γ (h.smulEquiv (DihedralGroup.sr 0)))
    (k : ZMod 19) :
    Nonempty (InvolutionK155 Γ (h.smulEquiv (DihedralGroup.sr k))) :=
  nonempty_involutionK155_of_d19FinalCharacterInputsComplementAndReflectionStar_raw_reflection
    h data.character hStar k

/-- Final inputs plus a fixed-star reflection input give the fixed-center leaf
boundary through the complementary minus-8 route. -/
theorem reflectionFixedCenterLeafBoundary_of_complementAndReflectionStar
    (data : D19FinalInputs h)
    (hStar :
      InvolutionFixedSetStar56 Γ (h.smulEquiv (DihedralGroup.sr 0))) :
    ReflectionFixedCenterLeafBoundary h :=
  reflectionFixedCenterLeafBoundary_of_d19FinalCharacterInputsComplementAndReflectionStar
    h data.character hStar

/-- Final inputs plus a fixed-star reflection input rule out the current
final-gap boundary through the complementary minus-8 route. -/
theorem no_currentFinalGapBoundary_of_complementAndReflectionStar
    (data : D19FinalInputs h)
    (hStar :
      InvolutionFixedSetStar56 Γ (h.smulEquiv (DihedralGroup.sr 0))) :
    ¬ Nonempty (BranchOrbitABCCurrentFinalGapBoundary h) :=
  no_currentFinalGapBoundary_of_d19FinalCharacterInputsComplementAndReflectionStar
    h data.character hStar

end D19FinalInputs

namespace D19ConstructiveFinalInputs

variable {h : D19ActsOnMoore57 V Γ}

/-- Constructive final inputs plus a fixed-star reflection input rule out the
current final-gap boundary through the complementary minus-8 route. -/
theorem no_currentFinalGapBoundary_of_complementAndReflectionStar
    (data : D19ConstructiveFinalInputs h)
    (hStar :
      InvolutionFixedSetStar56 Γ (h.smulEquiv (DihedralGroup.sr 0))) :
    ¬ Nonempty (BranchOrbitABCCurrentFinalGapBoundary h) :=
  no_currentFinalGapBoundary_of_d19FinalCharacterInputsComplementAndReflectionStar
    h data.character hStar

end D19ConstructiveFinalInputs

end D19ActsOnMoore57

end

end Moore57
