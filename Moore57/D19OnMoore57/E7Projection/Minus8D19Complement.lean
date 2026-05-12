import Moore57.D19OnMoore57.D19Core.ConstructiveFinal
import Moore57.D19OnMoore57.D19Core.GeometricInputs
import Moore57.D19OnMoore57.D19Core.OrbitContributionData
import Moore57.D19OnMoore57.E7Projection.Minus8BoundaryPackage
import Moore57.D19OnMoore57.E7Projection.Minus8D19TraceInput
import Moore57.D19OnMoore57.Misc.CharacterInputPackaging
import Moore57.D19OnMoore57.Rotation.FixedCountOneFrontier
import Moore57.D19OnMoore57.Trace.CoreRepresentationBoundary

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

/-!
# Complementary minus-8 boundary from action concrete data

This file lifts the complementary `(-8)` route from `D19TraceInput h` to the
action concrete data records that already carry `traceInput : D19TraceInput h`.
All results are thin wrappers around the trace-input boundary.
-/

namespace Moore57

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

namespace D19ActionConcreteData

variable {h : D19ActsOnMoore57 V Γ}

/-- Concrete action data plus the standard reflection counts gives a nonempty
linear-character input through the complementary minus-8 route. -/
theorem nonempty_d19LinearCharacterInput_of_complement
    (data : D19ActionConcreteData h)
    (reflection_fixed_count :
      fixedVertexCount (h.smulEquiv (DihedralGroup.sr 0)) = 56)
    (reflection_adjacent_moved :
      adjacentMovedCount Γ (h.smulEquiv (DihedralGroup.sr 0)) = 112) :
    Nonempty (D19ActsOnMoore57.D19LinearCharacterInput h) :=
  D19ActsOnMoore57.nonempty_d19LinearCharacterInput_of_d19TraceInputComplement
    h data.traceInput reflection_fixed_count reflection_adjacent_moved

/-- Concrete action data plus the standard reflection counts gives fixed-star
boundaries for all reflections through the complementary minus-8 route. -/
theorem involutionFixedSetStar56_of_complement_raw_reflection
    (data : D19ActionConcreteData h)
    (reflection_fixed_count :
      fixedVertexCount (h.smulEquiv (DihedralGroup.sr 0)) = 56)
    (reflection_adjacent_moved :
      adjacentMovedCount Γ (h.smulEquiv (DihedralGroup.sr 0)) = 112)
    (k : ZMod 19) :
    InvolutionFixedSetStar56 Γ (h.smulEquiv (DihedralGroup.sr k)) :=
  D19ActsOnMoore57.involutionFixedSetStar56_of_d19TraceInputComplement_raw_reflection
    h data.traceInput reflection_fixed_count reflection_adjacent_moved k

/-- Concrete action data plus the standard reflection counts gives `K_{1,55}`
witnesses for all reflections through the complementary minus-8 route. -/
theorem nonempty_involutionK155_of_complement_raw_reflection
    (data : D19ActionConcreteData h)
    (reflection_fixed_count :
      fixedVertexCount (h.smulEquiv (DihedralGroup.sr 0)) = 56)
    (reflection_adjacent_moved :
      adjacentMovedCount Γ (h.smulEquiv (DihedralGroup.sr 0)) = 112)
    (k : ZMod 19) :
    Nonempty (InvolutionK155 Γ (h.smulEquiv (DihedralGroup.sr k))) :=
  D19ActsOnMoore57.nonempty_involutionK155_of_d19TraceInputComplement_raw_reflection
    h data.traceInput reflection_fixed_count reflection_adjacent_moved k

/-- Concrete action data plus the standard reflection counts gives the
fixed-center leaf boundary through the complementary minus-8 route. -/
theorem reflectionFixedCenterLeafBoundary_of_complement
    (data : D19ActionConcreteData h)
    (reflection_fixed_count :
      fixedVertexCount (h.smulEquiv (DihedralGroup.sr 0)) = 56)
    (reflection_adjacent_moved :
      adjacentMovedCount Γ (h.smulEquiv (DihedralGroup.sr 0)) = 112) :
    ReflectionFixedCenterLeafBoundary h :=
  D19ActsOnMoore57.reflectionFixedCenterLeafBoundary_of_d19TraceInputComplement
    h data.traceInput reflection_fixed_count reflection_adjacent_moved

/-- Concrete action data plus the standard reflection counts gives the
representation character component boundary. -/
theorem representationCharacterComponentsBoundary_of_complement
    (data : D19ActionConcreteData h)
    (reflection_fixed_count :
      fixedVertexCount (h.smulEquiv (DihedralGroup.sr 0)) = 56)
    (reflection_adjacent_moved :
      adjacentMovedCount Γ (h.smulEquiv (DihedralGroup.sr 0)) = 112) :
    D19ActsOnMoore57.RepresentationCharacterComponentsBoundary h :=
  D19ActsOnMoore57.representationCharacterComponentsBoundary_of_d19TraceInputComplement
    h data.traceInput reflection_fixed_count reflection_adjacent_moved

/-- Concrete action data plus the standard reflection counts rules out the
current branch-orbit final-gap boundary. -/
theorem no_currentFinalGapBoundary_of_complement
    (data : D19ActionConcreteData h)
    (reflection_fixed_count :
      fixedVertexCount (h.smulEquiv (DihedralGroup.sr 0)) = 56)
    (reflection_adjacent_moved :
      adjacentMovedCount Γ (h.smulEquiv (DihedralGroup.sr 0)) = 112) :
    ¬ Nonempty (BranchOrbitABCCurrentFinalGapBoundary h) :=
  D19ActsOnMoore57.no_currentFinalGapBoundary_of_d19TraceInputComplement
    h data.traceInput reflection_fixed_count reflection_adjacent_moved

/-- Concrete action data plus a fixed-star reflection input gives a nonempty
linear-character input through the complementary minus-8 route. -/
theorem nonempty_d19LinearCharacterInput_of_complementAndReflectionStar
    (data : D19ActionConcreteData h)
    (hStar :
      InvolutionFixedSetStar56 Γ (h.smulEquiv (DihedralGroup.sr 0))) :
    Nonempty (D19ActsOnMoore57.D19LinearCharacterInput h) :=
  D19ActsOnMoore57.nonempty_d19LinearCharacterInput_of_d19TraceInputComplementAndReflectionStar
    h data.traceInput hStar

/-- Concrete action data plus a fixed-star reflection input gives fixed-star
boundaries for all reflections through the complementary minus-8 route. -/
theorem involutionFixedSetStar56_of_complementAndReflectionStar_raw_reflection
    (data : D19ActionConcreteData h)
    (hStar :
      InvolutionFixedSetStar56 Γ (h.smulEquiv (DihedralGroup.sr 0)))
    (k : ZMod 19) :
    InvolutionFixedSetStar56 Γ (h.smulEquiv (DihedralGroup.sr k)) :=
  D19ActsOnMoore57.involutionFixedSetStar56_of_d19TraceInputComplementAndReflectionStar_raw_reflection
    h data.traceInput hStar k

/-- Concrete action data plus a fixed-star reflection input gives `K_{1,55}`
witnesses for all reflections through the complementary minus-8 route. -/
theorem nonempty_involutionK155_of_complementAndReflectionStar_raw_reflection
    (data : D19ActionConcreteData h)
    (hStar :
      InvolutionFixedSetStar56 Γ (h.smulEquiv (DihedralGroup.sr 0)))
    (k : ZMod 19) :
    Nonempty (InvolutionK155 Γ (h.smulEquiv (DihedralGroup.sr k))) :=
  D19ActsOnMoore57.nonempty_involutionK155_of_d19TraceInputComplementAndReflectionStar_raw_reflection
    h data.traceInput hStar k

/-- Concrete action data plus a fixed-star reflection input gives the
fixed-center leaf boundary through the complementary minus-8 route. -/
theorem reflectionFixedCenterLeafBoundary_of_complementAndReflectionStar
    (data : D19ActionConcreteData h)
    (hStar :
      InvolutionFixedSetStar56 Γ (h.smulEquiv (DihedralGroup.sr 0))) :
    ReflectionFixedCenterLeafBoundary h :=
  D19ActsOnMoore57.reflectionFixedCenterLeafBoundary_of_d19TraceInputComplementAndReflectionStar
    h data.traceInput hStar

/-- Concrete action data plus a fixed-star reflection input gives the
representation character component boundary. -/
theorem representationCharacterComponentsBoundary_of_complementAndReflectionStar
    (data : D19ActionConcreteData h)
    (hStar :
      InvolutionFixedSetStar56 Γ (h.smulEquiv (DihedralGroup.sr 0))) :
    D19ActsOnMoore57.RepresentationCharacterComponentsBoundary h :=
  D19ActsOnMoore57.representationCharacterComponentsBoundary_of_d19TraceInputComplementAndReflectionStar
    h data.traceInput hStar

/-- Concrete action data plus a fixed-star reflection input rules out the
current branch-orbit final-gap boundary. -/
theorem no_currentFinalGapBoundary_of_complementAndReflectionStar
    (data : D19ActionConcreteData h)
    (hStar :
      InvolutionFixedSetStar56 Γ (h.smulEquiv (DihedralGroup.sr 0))) :
    ¬ Nonempty (BranchOrbitABCCurrentFinalGapBoundary h) :=
  D19ActsOnMoore57.no_currentFinalGapBoundary_of_d19TraceInputComplementAndReflectionStar
    h data.traceInput hStar

end D19ActionConcreteData

namespace D19ActionOrbitConcreteData

variable {h : D19ActsOnMoore57 V Γ}

/-- Orbit-generated concrete action data plus the standard reflection counts
gives a nonempty linear-character input through the complementary minus-8
route. -/
theorem nonempty_d19LinearCharacterInput_of_complement
    (data : D19ActionOrbitConcreteData h)
    (reflection_fixed_count :
      fixedVertexCount (h.smulEquiv (DihedralGroup.sr 0)) = 56)
    (reflection_adjacent_moved :
      adjacentMovedCount Γ (h.smulEquiv (DihedralGroup.sr 0)) = 112) :
    Nonempty (D19ActsOnMoore57.D19LinearCharacterInput h) :=
  D19ActsOnMoore57.nonempty_d19LinearCharacterInput_of_d19TraceInputComplement
    h data.traceInput reflection_fixed_count reflection_adjacent_moved

/-- Orbit-generated concrete action data plus the standard reflection counts
gives fixed-star boundaries for all reflections through the complementary
minus-8 route. -/
theorem involutionFixedSetStar56_of_complement_raw_reflection
    (data : D19ActionOrbitConcreteData h)
    (reflection_fixed_count :
      fixedVertexCount (h.smulEquiv (DihedralGroup.sr 0)) = 56)
    (reflection_adjacent_moved :
      adjacentMovedCount Γ (h.smulEquiv (DihedralGroup.sr 0)) = 112)
    (k : ZMod 19) :
    InvolutionFixedSetStar56 Γ (h.smulEquiv (DihedralGroup.sr k)) :=
  D19ActsOnMoore57.involutionFixedSetStar56_of_d19TraceInputComplement_raw_reflection
    h data.traceInput reflection_fixed_count reflection_adjacent_moved k

/-- Orbit-generated concrete action data plus the standard reflection counts
gives `K_{1,55}` witnesses for all reflections through the complementary
minus-8 route. -/
theorem nonempty_involutionK155_of_complement_raw_reflection
    (data : D19ActionOrbitConcreteData h)
    (reflection_fixed_count :
      fixedVertexCount (h.smulEquiv (DihedralGroup.sr 0)) = 56)
    (reflection_adjacent_moved :
      adjacentMovedCount Γ (h.smulEquiv (DihedralGroup.sr 0)) = 112)
    (k : ZMod 19) :
    Nonempty (InvolutionK155 Γ (h.smulEquiv (DihedralGroup.sr k))) :=
  D19ActsOnMoore57.nonempty_involutionK155_of_d19TraceInputComplement_raw_reflection
    h data.traceInput reflection_fixed_count reflection_adjacent_moved k

/-- Orbit-generated concrete action data plus the standard reflection counts
gives the fixed-center leaf boundary through the complementary minus-8 route. -/
theorem reflectionFixedCenterLeafBoundary_of_complement
    (data : D19ActionOrbitConcreteData h)
    (reflection_fixed_count :
      fixedVertexCount (h.smulEquiv (DihedralGroup.sr 0)) = 56)
    (reflection_adjacent_moved :
      adjacentMovedCount Γ (h.smulEquiv (DihedralGroup.sr 0)) = 112) :
    ReflectionFixedCenterLeafBoundary h :=
  D19ActsOnMoore57.reflectionFixedCenterLeafBoundary_of_d19TraceInputComplement
    h data.traceInput reflection_fixed_count reflection_adjacent_moved

/-- Orbit-generated concrete action data plus the standard reflection counts
gives the representation character component boundary. -/
theorem representationCharacterComponentsBoundary_of_complement
    (data : D19ActionOrbitConcreteData h)
    (reflection_fixed_count :
      fixedVertexCount (h.smulEquiv (DihedralGroup.sr 0)) = 56)
    (reflection_adjacent_moved :
      adjacentMovedCount Γ (h.smulEquiv (DihedralGroup.sr 0)) = 112) :
    D19ActsOnMoore57.RepresentationCharacterComponentsBoundary h :=
  D19ActsOnMoore57.representationCharacterComponentsBoundary_of_d19TraceInputComplement
    h data.traceInput reflection_fixed_count reflection_adjacent_moved

/-- Orbit-generated concrete action data plus the standard reflection counts
rules out the current branch-orbit final-gap boundary. -/
theorem no_currentFinalGapBoundary_of_complement
    (data : D19ActionOrbitConcreteData h)
    (reflection_fixed_count :
      fixedVertexCount (h.smulEquiv (DihedralGroup.sr 0)) = 56)
    (reflection_adjacent_moved :
      adjacentMovedCount Γ (h.smulEquiv (DihedralGroup.sr 0)) = 112) :
    ¬ Nonempty (BranchOrbitABCCurrentFinalGapBoundary h) :=
  D19ActsOnMoore57.no_currentFinalGapBoundary_of_d19TraceInputComplement
    h data.traceInput reflection_fixed_count reflection_adjacent_moved

/-- Orbit-generated concrete action data plus a fixed-star reflection input
gives a nonempty linear-character input through the complementary minus-8
route. -/
theorem nonempty_d19LinearCharacterInput_of_complementAndReflectionStar
    (data : D19ActionOrbitConcreteData h)
    (hStar :
      InvolutionFixedSetStar56 Γ (h.smulEquiv (DihedralGroup.sr 0))) :
    Nonempty (D19ActsOnMoore57.D19LinearCharacterInput h) :=
  D19ActsOnMoore57.nonempty_d19LinearCharacterInput_of_d19TraceInputComplementAndReflectionStar
    h data.traceInput hStar

/-- Orbit-generated concrete action data plus a fixed-star reflection input
gives fixed-star boundaries for all reflections through the complementary
minus-8 route. -/
theorem involutionFixedSetStar56_of_complementAndReflectionStar_raw_reflection
    (data : D19ActionOrbitConcreteData h)
    (hStar :
      InvolutionFixedSetStar56 Γ (h.smulEquiv (DihedralGroup.sr 0)))
    (k : ZMod 19) :
    InvolutionFixedSetStar56 Γ (h.smulEquiv (DihedralGroup.sr k)) :=
  D19ActsOnMoore57.involutionFixedSetStar56_of_d19TraceInputComplementAndReflectionStar_raw_reflection
    h data.traceInput hStar k

/-- Orbit-generated concrete action data plus a fixed-star reflection input
gives `K_{1,55}` witnesses for all reflections through the complementary
minus-8 route. -/
theorem nonempty_involutionK155_of_complementAndReflectionStar_raw_reflection
    (data : D19ActionOrbitConcreteData h)
    (hStar :
      InvolutionFixedSetStar56 Γ (h.smulEquiv (DihedralGroup.sr 0)))
    (k : ZMod 19) :
    Nonempty (InvolutionK155 Γ (h.smulEquiv (DihedralGroup.sr k))) :=
  D19ActsOnMoore57.nonempty_involutionK155_of_d19TraceInputComplementAndReflectionStar_raw_reflection
    h data.traceInput hStar k

/-- Orbit-generated concrete action data plus a fixed-star reflection input
gives the fixed-center leaf boundary through the complementary minus-8 route. -/
theorem reflectionFixedCenterLeafBoundary_of_complementAndReflectionStar
    (data : D19ActionOrbitConcreteData h)
    (hStar :
      InvolutionFixedSetStar56 Γ (h.smulEquiv (DihedralGroup.sr 0))) :
    ReflectionFixedCenterLeafBoundary h :=
  D19ActsOnMoore57.reflectionFixedCenterLeafBoundary_of_d19TraceInputComplementAndReflectionStar
    h data.traceInput hStar

/-- Orbit-generated concrete action data plus a fixed-star reflection input
gives the representation character component boundary. -/
theorem representationCharacterComponentsBoundary_of_complementAndReflectionStar
    (data : D19ActionOrbitConcreteData h)
    (hStar :
      InvolutionFixedSetStar56 Γ (h.smulEquiv (DihedralGroup.sr 0))) :
    D19ActsOnMoore57.RepresentationCharacterComponentsBoundary h :=
  D19ActsOnMoore57.representationCharacterComponentsBoundary_of_d19TraceInputComplementAndReflectionStar
    h data.traceInput hStar

/-- Orbit-generated concrete action data plus a fixed-star reflection input
rules out the current branch-orbit final-gap boundary. -/
theorem no_currentFinalGapBoundary_of_complementAndReflectionStar
    (data : D19ActionOrbitConcreteData h)
    (hStar :
      InvolutionFixedSetStar56 Γ (h.smulEquiv (DihedralGroup.sr 0))) :
    ¬ Nonempty (BranchOrbitABCCurrentFinalGapBoundary h) :=
  D19ActsOnMoore57.no_currentFinalGapBoundary_of_d19TraceInputComplementAndReflectionStar
    h data.traceInput hStar

end D19ActionOrbitConcreteData

namespace D19OrbitContributionData

variable {h : D19ActsOnMoore57 V Γ}

/-- Orbit contribution data plus a fixed-star reflection input gives a
nonempty linear-character input through the complementary minus-8 route. -/
theorem nonempty_d19LinearCharacterInput_of_complementAndReflectionStar
    (data : D19OrbitContributionData h)
    (hStar :
      InvolutionFixedSetStar56 Γ (h.smulEquiv (DihedralGroup.sr 0))) :
    Nonempty (D19ActsOnMoore57.D19LinearCharacterInput h) :=
  D19ActsOnMoore57.nonempty_d19LinearCharacterInput_of_d19TraceInputComplementAndReflectionStar
    h data.traceInput hStar

/-- Orbit contribution data plus a fixed-star reflection input gives fixed-star
boundaries for all reflections through the complementary minus-8 route. -/
theorem involutionFixedSetStar56_of_complementAndReflectionStar_raw_reflection
    (data : D19OrbitContributionData h)
    (hStar :
      InvolutionFixedSetStar56 Γ (h.smulEquiv (DihedralGroup.sr 0)))
    (k : ZMod 19) :
    InvolutionFixedSetStar56 Γ (h.smulEquiv (DihedralGroup.sr k)) :=
  D19ActsOnMoore57.involutionFixedSetStar56_of_d19TraceInputComplementAndReflectionStar_raw_reflection
    h data.traceInput hStar k

/-- Orbit contribution data plus a fixed-star reflection input gives
`K_{1,55}` witnesses for all reflections through the complementary minus-8
route. -/
theorem nonempty_involutionK155_of_complementAndReflectionStar_raw_reflection
    (data : D19OrbitContributionData h)
    (hStar :
      InvolutionFixedSetStar56 Γ (h.smulEquiv (DihedralGroup.sr 0)))
    (k : ZMod 19) :
    Nonempty (InvolutionK155 Γ (h.smulEquiv (DihedralGroup.sr k))) :=
  D19ActsOnMoore57.nonempty_involutionK155_of_d19TraceInputComplementAndReflectionStar_raw_reflection
    h data.traceInput hStar k

/-- Orbit contribution data plus a fixed-star reflection input gives the
fixed-center leaf boundary through the complementary minus-8 route. -/
theorem reflectionFixedCenterLeafBoundary_of_complementAndReflectionStar
    (data : D19OrbitContributionData h)
    (hStar :
      InvolutionFixedSetStar56 Γ (h.smulEquiv (DihedralGroup.sr 0))) :
    ReflectionFixedCenterLeafBoundary h :=
  D19ActsOnMoore57.reflectionFixedCenterLeafBoundary_of_d19TraceInputComplementAndReflectionStar
    h data.traceInput hStar

/-- Orbit contribution data plus a fixed-star reflection input gives the
representation character component boundary. -/
theorem representationCharacterComponentsBoundary_of_complementAndReflectionStar
    (data : D19OrbitContributionData h)
    (hStar :
      InvolutionFixedSetStar56 Γ (h.smulEquiv (DihedralGroup.sr 0))) :
    D19ActsOnMoore57.RepresentationCharacterComponentsBoundary h :=
  D19ActsOnMoore57.representationCharacterComponentsBoundary_of_d19TraceInputComplementAndReflectionStar
    h data.traceInput hStar

/-- Orbit contribution data plus a fixed-star reflection input rules out the
current branch-orbit final-gap boundary. -/
theorem no_currentFinalGapBoundary_of_complementAndReflectionStar
    (data : D19OrbitContributionData h)
    (hStar :
      InvolutionFixedSetStar56 Γ (h.smulEquiv (DihedralGroup.sr 0))) :
    ¬ Nonempty (BranchOrbitABCCurrentFinalGapBoundary h) :=
  D19ActsOnMoore57.no_currentFinalGapBoundary_of_d19TraceInputComplementAndReflectionStar
    h data.traceInput hStar

end D19OrbitContributionData

end

end Moore57

/-!
# Complementary minus-8 boundary from reduced and geometric inputs

This file lifts the complementary `(-8)` character-input route to the reduced
and geometric D19 input packages.  All proofs are thin wrappers through the
`D19CharacterInput` complement boundary theorems.
-/

namespace Moore57

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

namespace D19ReducedHypotheses

variable {h : D19ActsOnMoore57 V Γ}

/-- Reduced hypotheses plus the standard reflection counts give a nonempty
linear-character input through the complementary minus-8 route. -/
theorem nonempty_d19LinearCharacterInput_of_complement
    (data : D19ReducedHypotheses h)
    (reflection_fixed_count :
      fixedVertexCount (h.smulEquiv (DihedralGroup.sr 0)) = 56)
    (reflection_adjacent_moved :
      adjacentMovedCount Γ (h.smulEquiv (DihedralGroup.sr 0)) = 112) :
    Nonempty (D19ActsOnMoore57.D19LinearCharacterInput h) :=
  D19ActsOnMoore57.nonempty_d19LinearCharacterInput_of_d19CharacterInputComplement
    h data.characterInput reflection_fixed_count reflection_adjacent_moved

/-- Reduced hypotheses plus the standard reflection counts give fixed-star
boundaries for all reflections through the complementary minus-8 route. -/
theorem involutionFixedSetStar56_of_complement_raw_reflection
    (data : D19ReducedHypotheses h)
    (reflection_fixed_count :
      fixedVertexCount (h.smulEquiv (DihedralGroup.sr 0)) = 56)
    (reflection_adjacent_moved :
      adjacentMovedCount Γ (h.smulEquiv (DihedralGroup.sr 0)) = 112)
    (k : ZMod 19) :
    InvolutionFixedSetStar56 Γ (h.smulEquiv (DihedralGroup.sr k)) :=
  D19ActsOnMoore57.involutionFixedSetStar56_of_d19CharacterInputComplement_raw_reflection
    h data.characterInput reflection_fixed_count reflection_adjacent_moved k

/-- Reduced hypotheses plus the standard reflection counts give `K_{1,55}`
witnesses for all reflections through the complementary minus-8 route. -/
theorem nonempty_involutionK155_of_complement_raw_reflection
    (data : D19ReducedHypotheses h)
    (reflection_fixed_count :
      fixedVertexCount (h.smulEquiv (DihedralGroup.sr 0)) = 56)
    (reflection_adjacent_moved :
      adjacentMovedCount Γ (h.smulEquiv (DihedralGroup.sr 0)) = 112)
    (k : ZMod 19) :
    Nonempty (InvolutionK155 Γ (h.smulEquiv (DihedralGroup.sr k))) :=
  D19ActsOnMoore57.nonempty_involutionK155_of_d19CharacterInputComplement_raw_reflection
    h data.characterInput reflection_fixed_count reflection_adjacent_moved k

/-- Reduced hypotheses plus the standard reflection counts give the
fixed-center leaf boundary through the complementary minus-8 route. -/
theorem reflectionFixedCenterLeafBoundary_of_complement
    (data : D19ReducedHypotheses h)
    (reflection_fixed_count :
      fixedVertexCount (h.smulEquiv (DihedralGroup.sr 0)) = 56)
    (reflection_adjacent_moved :
      adjacentMovedCount Γ (h.smulEquiv (DihedralGroup.sr 0)) = 112) :
    ReflectionFixedCenterLeafBoundary h :=
  D19ActsOnMoore57.reflectionFixedCenterLeafBoundary_of_d19CharacterInputComplement
    h data.characterInput reflection_fixed_count reflection_adjacent_moved

/-- Reduced hypotheses plus the standard reflection counts give the
representation character component boundary through the complementary minus-8
route. -/
theorem representationCharacterComponentsBoundary_of_complement
    (data : D19ReducedHypotheses h)
    (reflection_fixed_count :
      fixedVertexCount (h.smulEquiv (DihedralGroup.sr 0)) = 56)
    (reflection_adjacent_moved :
      adjacentMovedCount Γ (h.smulEquiv (DihedralGroup.sr 0)) = 112) :
    D19ActsOnMoore57.RepresentationCharacterComponentsBoundary h :=
  D19ActsOnMoore57.representationCharacterComponentsBoundary_of_d19CharacterInputComplement
    h data.characterInput reflection_fixed_count reflection_adjacent_moved

/-- Reduced hypotheses plus the standard reflection counts rule out the
current final-gap boundary through the complementary minus-8 route. -/
theorem no_currentFinalGapBoundary_of_complement
    (data : D19ReducedHypotheses h)
    (reflection_fixed_count :
      fixedVertexCount (h.smulEquiv (DihedralGroup.sr 0)) = 56)
    (reflection_adjacent_moved :
      adjacentMovedCount Γ (h.smulEquiv (DihedralGroup.sr 0)) = 112) :
    ¬ Nonempty (BranchOrbitABCCurrentFinalGapBoundary h) :=
  D19ActsOnMoore57.no_currentFinalGapBoundary_of_d19CharacterInputComplement
    h data.characterInput reflection_fixed_count reflection_adjacent_moved

/-- Reduced hypotheses plus a fixed-star reflection input give a nonempty
linear-character input through the complementary minus-8 route. -/
theorem nonempty_d19LinearCharacterInput_of_complementAndReflectionStar
    (data : D19ReducedHypotheses h)
    (hStar :
      InvolutionFixedSetStar56 Γ (h.smulEquiv (DihedralGroup.sr 0))) :
    Nonempty (D19ActsOnMoore57.D19LinearCharacterInput h) :=
  D19ActsOnMoore57.nonempty_d19LinearCharacterInput_of_d19CharacterInputComplementAndReflectionStar
    h data.characterInput hStar

/-- Reduced hypotheses plus a fixed-star reflection input give fixed-star
boundaries for all reflections through the complementary minus-8 route. -/
theorem involutionFixedSetStar56_of_complementAndReflectionStar_raw_reflection
    (data : D19ReducedHypotheses h)
    (hStar :
      InvolutionFixedSetStar56 Γ (h.smulEquiv (DihedralGroup.sr 0)))
    (k : ZMod 19) :
    InvolutionFixedSetStar56 Γ (h.smulEquiv (DihedralGroup.sr k)) :=
  D19ActsOnMoore57.involutionFixedSetStar56_of_d19CharacterInputComplementAndReflectionStar_raw_reflection
    h data.characterInput hStar k

/-- Reduced hypotheses plus a fixed-star reflection input give `K_{1,55}`
witnesses for all reflections through the complementary minus-8 route. -/
theorem nonempty_involutionK155_of_complementAndReflectionStar_raw_reflection
    (data : D19ReducedHypotheses h)
    (hStar :
      InvolutionFixedSetStar56 Γ (h.smulEquiv (DihedralGroup.sr 0)))
    (k : ZMod 19) :
    Nonempty (InvolutionK155 Γ (h.smulEquiv (DihedralGroup.sr k))) :=
  D19ActsOnMoore57.nonempty_involutionK155_of_d19CharacterInputComplementAndReflectionStar_raw_reflection
    h data.characterInput hStar k

/-- Reduced hypotheses plus a fixed-star reflection input give the
fixed-center leaf boundary through the complementary minus-8 route. -/
theorem reflectionFixedCenterLeafBoundary_of_complementAndReflectionStar
    (data : D19ReducedHypotheses h)
    (hStar :
      InvolutionFixedSetStar56 Γ (h.smulEquiv (DihedralGroup.sr 0))) :
    ReflectionFixedCenterLeafBoundary h :=
  D19ActsOnMoore57.reflectionFixedCenterLeafBoundary_of_d19CharacterInputComplementAndReflectionStar
    h data.characterInput hStar

/-- Reduced hypotheses plus a fixed-star reflection input give the
representation character component boundary through the complementary minus-8
route. -/
theorem representationCharacterComponentsBoundary_of_complementAndReflectionStar
    (data : D19ReducedHypotheses h)
    (hStar :
      InvolutionFixedSetStar56 Γ (h.smulEquiv (DihedralGroup.sr 0))) :
    D19ActsOnMoore57.RepresentationCharacterComponentsBoundary h :=
  D19ActsOnMoore57.representationCharacterComponentsBoundary_of_d19CharacterInputComplementAndReflectionStar
    h data.characterInput hStar

/-- Reduced hypotheses plus a fixed-star reflection input rule out the current
final-gap boundary through the complementary minus-8 route. -/
theorem no_currentFinalGapBoundary_of_complementAndReflectionStar
    (data : D19ReducedHypotheses h)
    (hStar :
      InvolutionFixedSetStar56 Γ (h.smulEquiv (DihedralGroup.sr 0))) :
    ¬ Nonempty (BranchOrbitABCCurrentFinalGapBoundary h) :=
  D19ActsOnMoore57.no_currentFinalGapBoundary_of_d19CharacterInputComplementAndReflectionStar
    h data.characterInput hStar

end D19ReducedHypotheses

namespace D19GeometricInputs

variable {h : D19ActsOnMoore57 V Γ}

/-- Geometric inputs plus the standard reflection counts give a nonempty
linear-character input through the complementary minus-8 route. -/
theorem nonempty_d19LinearCharacterInput_of_complement
    (data : D19GeometricInputs h)
    (reflection_fixed_count :
      fixedVertexCount (h.smulEquiv (DihedralGroup.sr 0)) = 56)
    (reflection_adjacent_moved :
      adjacentMovedCount Γ (h.smulEquiv (DihedralGroup.sr 0)) = 112) :
    Nonempty (D19ActsOnMoore57.D19LinearCharacterInput h) :=
  D19ReducedHypotheses.nonempty_d19LinearCharacterInput_of_complement
    data.toD19ReducedHypotheses reflection_fixed_count reflection_adjacent_moved

/-- Geometric inputs plus the standard reflection counts give fixed-star
boundaries for all reflections through the complementary minus-8 route. -/
theorem involutionFixedSetStar56_of_complement_raw_reflection
    (data : D19GeometricInputs h)
    (reflection_fixed_count :
      fixedVertexCount (h.smulEquiv (DihedralGroup.sr 0)) = 56)
    (reflection_adjacent_moved :
      adjacentMovedCount Γ (h.smulEquiv (DihedralGroup.sr 0)) = 112)
    (k : ZMod 19) :
    InvolutionFixedSetStar56 Γ (h.smulEquiv (DihedralGroup.sr k)) :=
  D19ReducedHypotheses.involutionFixedSetStar56_of_complement_raw_reflection
    data.toD19ReducedHypotheses reflection_fixed_count reflection_adjacent_moved k

/-- Geometric inputs plus the standard reflection counts give `K_{1,55}`
witnesses for all reflections through the complementary minus-8 route. -/
theorem nonempty_involutionK155_of_complement_raw_reflection
    (data : D19GeometricInputs h)
    (reflection_fixed_count :
      fixedVertexCount (h.smulEquiv (DihedralGroup.sr 0)) = 56)
    (reflection_adjacent_moved :
      adjacentMovedCount Γ (h.smulEquiv (DihedralGroup.sr 0)) = 112)
    (k : ZMod 19) :
    Nonempty (InvolutionK155 Γ (h.smulEquiv (DihedralGroup.sr k))) :=
  D19ReducedHypotheses.nonempty_involutionK155_of_complement_raw_reflection
    data.toD19ReducedHypotheses reflection_fixed_count reflection_adjacent_moved k

/-- Geometric inputs plus the standard reflection counts give the fixed-center
leaf boundary through the complementary minus-8 route. -/
theorem reflectionFixedCenterLeafBoundary_of_complement
    (data : D19GeometricInputs h)
    (reflection_fixed_count :
      fixedVertexCount (h.smulEquiv (DihedralGroup.sr 0)) = 56)
    (reflection_adjacent_moved :
      adjacentMovedCount Γ (h.smulEquiv (DihedralGroup.sr 0)) = 112) :
    ReflectionFixedCenterLeafBoundary h :=
  D19ReducedHypotheses.reflectionFixedCenterLeafBoundary_of_complement
    data.toD19ReducedHypotheses reflection_fixed_count reflection_adjacent_moved

/-- Geometric inputs plus the standard reflection counts give the
representation character component boundary through the complementary minus-8
route. -/
theorem representationCharacterComponentsBoundary_of_complement
    (data : D19GeometricInputs h)
    (reflection_fixed_count :
      fixedVertexCount (h.smulEquiv (DihedralGroup.sr 0)) = 56)
    (reflection_adjacent_moved :
      adjacentMovedCount Γ (h.smulEquiv (DihedralGroup.sr 0)) = 112) :
    D19ActsOnMoore57.RepresentationCharacterComponentsBoundary h :=
  D19ReducedHypotheses.representationCharacterComponentsBoundary_of_complement
    data.toD19ReducedHypotheses reflection_fixed_count reflection_adjacent_moved

/-- Geometric inputs plus the standard reflection counts rule out the current
final-gap boundary through the complementary minus-8 route. -/
theorem no_currentFinalGapBoundary_of_complement
    (data : D19GeometricInputs h)
    (reflection_fixed_count :
      fixedVertexCount (h.smulEquiv (DihedralGroup.sr 0)) = 56)
    (reflection_adjacent_moved :
      adjacentMovedCount Γ (h.smulEquiv (DihedralGroup.sr 0)) = 112) :
    ¬ Nonempty (BranchOrbitABCCurrentFinalGapBoundary h) :=
  D19ReducedHypotheses.no_currentFinalGapBoundary_of_complement
    data.toD19ReducedHypotheses reflection_fixed_count reflection_adjacent_moved

/-- Geometric inputs plus a fixed-star reflection input give a nonempty
linear-character input through the complementary minus-8 route. -/
theorem nonempty_d19LinearCharacterInput_of_complementAndReflectionStar
    (data : D19GeometricInputs h)
    (hStar :
      InvolutionFixedSetStar56 Γ (h.smulEquiv (DihedralGroup.sr 0))) :
    Nonempty (D19ActsOnMoore57.D19LinearCharacterInput h) :=
  D19ReducedHypotheses.nonempty_d19LinearCharacterInput_of_complementAndReflectionStar
    data.toD19ReducedHypotheses hStar

/-- Geometric inputs plus a fixed-star reflection input give fixed-star
boundaries for all reflections through the complementary minus-8 route. -/
theorem involutionFixedSetStar56_of_complementAndReflectionStar_raw_reflection
    (data : D19GeometricInputs h)
    (hStar :
      InvolutionFixedSetStar56 Γ (h.smulEquiv (DihedralGroup.sr 0)))
    (k : ZMod 19) :
    InvolutionFixedSetStar56 Γ (h.smulEquiv (DihedralGroup.sr k)) :=
  D19ReducedHypotheses.involutionFixedSetStar56_of_complementAndReflectionStar_raw_reflection
    data.toD19ReducedHypotheses hStar k

/-- Geometric inputs plus a fixed-star reflection input give `K_{1,55}`
witnesses for all reflections through the complementary minus-8 route. -/
theorem nonempty_involutionK155_of_complementAndReflectionStar_raw_reflection
    (data : D19GeometricInputs h)
    (hStar :
      InvolutionFixedSetStar56 Γ (h.smulEquiv (DihedralGroup.sr 0)))
    (k : ZMod 19) :
    Nonempty (InvolutionK155 Γ (h.smulEquiv (DihedralGroup.sr k))) :=
  D19ReducedHypotheses.nonempty_involutionK155_of_complementAndReflectionStar_raw_reflection
    data.toD19ReducedHypotheses hStar k

/-- Geometric inputs plus a fixed-star reflection input give the fixed-center
leaf boundary through the complementary minus-8 route. -/
theorem reflectionFixedCenterLeafBoundary_of_complementAndReflectionStar
    (data : D19GeometricInputs h)
    (hStar :
      InvolutionFixedSetStar56 Γ (h.smulEquiv (DihedralGroup.sr 0))) :
    ReflectionFixedCenterLeafBoundary h :=
  D19ReducedHypotheses.reflectionFixedCenterLeafBoundary_of_complementAndReflectionStar
    data.toD19ReducedHypotheses hStar

/-- Geometric inputs plus a fixed-star reflection input give the representation
character component boundary through the complementary minus-8 route. -/
theorem representationCharacterComponentsBoundary_of_complementAndReflectionStar
    (data : D19GeometricInputs h)
    (hStar :
      InvolutionFixedSetStar56 Γ (h.smulEquiv (DihedralGroup.sr 0))) :
    D19ActsOnMoore57.RepresentationCharacterComponentsBoundary h :=
  D19ReducedHypotheses.representationCharacterComponentsBoundary_of_complementAndReflectionStar
    data.toD19ReducedHypotheses hStar

/-- Geometric inputs plus a fixed-star reflection input rule out the current
final-gap boundary through the complementary minus-8 route. -/
theorem no_currentFinalGapBoundary_of_complementAndReflectionStar
    (data : D19GeometricInputs h)
    (hStar :
      InvolutionFixedSetStar56 Γ (h.smulEquiv (DihedralGroup.sr 0))) :
    ¬ Nonempty (BranchOrbitABCCurrentFinalGapBoundary h) :=
  D19ReducedHypotheses.no_currentFinalGapBoundary_of_complementAndReflectionStar
    data.toD19ReducedHypotheses hStar

end D19GeometricInputs

end

end Moore57

/-!
# Action-level no-go connectors from complementary character inputs

This file exposes action-level no-go frontiers directly from
`D19CharacterInput` and `D19FinalCharacterInputs` after the `(-8)` character
values have been supplied by the complementary projection formula.
-/

namespace Moore57

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

namespace D19ActsOnMoore57

namespace E7Minus8CharacterReflectionCountBoundary

variable (h : D19ActsOnMoore57 V Γ)

/-- Build the complementary package from a coarse character input and a
fixed-star input at the standard reflection representative. -/
def ofD19CharacterInputComplementAndReflectionStar'
    (characterInput : D19CharacterInput h)
    (hStar :
      InvolutionFixedSetStar56 Γ (h.smulEquiv (DihedralGroup.sr 0))) :
    E7Minus8CharacterReflectionCountBoundary h :=
  ofD19CharacterInputComplementAndReflectionStar h characterInput hStar

end E7Minus8CharacterReflectionCountBoundary

/-- Complementary `D19CharacterInput` route rules out the action-level final
boundary. -/
theorem no_actionLevelFinalBoundary_of_d19CharacterInputComplement
    (h : D19ActsOnMoore57 V Γ)
    (characterInput : D19CharacterInput h)
    (reflection_fixed_count :
      fixedVertexCount (h.smulEquiv (DihedralGroup.sr 0)) = 56)
    (reflection_adjacent_moved :
      adjacentMovedCount Γ (h.smulEquiv (DihedralGroup.sr 0)) = 112) :
    ¬ Nonempty (BranchOrbitABCActionLevelFinalBoundary h) :=
  (E7Minus8CharacterReflectionCountBoundary.ofD19CharacterInputComplement h
    characterInput reflection_fixed_count reflection_adjacent_moved)
      |>.no_actionLevelFinalBoundary

/-- Complementary `D19CharacterInput` route rules out the action-level local
obstruction boundary. -/
theorem no_actionLevelLocalObstructionBoundary_of_d19CharacterInputComplement
    (h : D19ActsOnMoore57 V Γ)
    (characterInput : D19CharacterInput h)
    (reflection_fixed_count :
      fixedVertexCount (h.smulEquiv (DihedralGroup.sr 0)) = 56)
    (reflection_adjacent_moved :
      adjacentMovedCount Γ (h.smulEquiv (DihedralGroup.sr 0)) = 112) :
    ¬ Nonempty (BranchOrbitABCActionLevelLocalObstructionBoundary h) :=
  (E7Minus8CharacterReflectionCountBoundary.ofD19CharacterInputComplement h
    characterInput reflection_fixed_count reflection_adjacent_moved)
      |>.no_actionLevelLocalObstructionBoundary

/-- Complementary `D19CharacterInput` route rules out the action-level
reduced-coordinate witness boundary. -/
theorem no_actionLevelReducedCoordinateWitnessBoundary_of_d19CharacterInputComplement
    (h : D19ActsOnMoore57 V Γ)
    (characterInput : D19CharacterInput h)
    (reflection_fixed_count :
      fixedVertexCount (h.smulEquiv (DihedralGroup.sr 0)) = 56)
    (reflection_adjacent_moved :
      adjacentMovedCount Γ (h.smulEquiv (DihedralGroup.sr 0)) = 112) :
    ¬ Nonempty (BranchOrbitABCActionLevelReducedCoordinateWitnessBoundary h) :=
  (E7Minus8CharacterReflectionCountBoundary.ofD19CharacterInputComplement h
    characterInput reflection_fixed_count reflection_adjacent_moved)
      |>.no_actionLevelReducedCoordinateWitnessBoundary

/-- Complementary `D19CharacterInput` route rules out the action-level
set-invariant witness boundary. -/
theorem no_actionLevelSetInvariantWitnessBoundary_of_d19CharacterInputComplement
    (h : D19ActsOnMoore57 V Γ)
    (characterInput : D19CharacterInput h)
    (reflection_fixed_count :
      fixedVertexCount (h.smulEquiv (DihedralGroup.sr 0)) = 56)
    (reflection_adjacent_moved :
      adjacentMovedCount Γ (h.smulEquiv (DihedralGroup.sr 0)) = 112) :
    ¬ Nonempty (BranchOrbitABCActionLevelSetInvariantWitnessBoundary h) :=
  (E7Minus8CharacterReflectionCountBoundary.ofD19CharacterInputComplement h
    characterInput reflection_fixed_count reflection_adjacent_moved)
      |>.no_actionLevelSetInvariantWitnessBoundary

/-- Complementary `D19CharacterInput` route rules out the common-neighbor
reduced current-gap boundary. -/
theorem no_actionLevelCommonNeighborReducedBoundary_of_d19CharacterInputComplement
    (h : D19ActsOnMoore57 V Γ)
    (characterInput : D19CharacterInput h)
    (reflection_fixed_count :
      fixedVertexCount (h.smulEquiv (DihedralGroup.sr 0)) = 56)
    (reflection_adjacent_moved :
      adjacentMovedCount Γ (h.smulEquiv (DihedralGroup.sr 0)) = 112) :
    ¬ Nonempty (BranchOrbitABCActionLevelCommonNeighborReducedBoundary h) :=
  (E7Minus8CharacterReflectionCountBoundary.ofD19CharacterInputComplement h
    characterInput reflection_fixed_count reflection_adjacent_moved)
      |>.no_actionLevelCommonNeighborReducedBoundary

/-- Complementary `D19CharacterInput` route rules out the minimal-remaining
current-gap boundary. -/
theorem no_actionLevelMinimalRemainingBoundary_of_d19CharacterInputComplement
    (h : D19ActsOnMoore57 V Γ)
    (characterInput : D19CharacterInput h)
    (reflection_fixed_count :
      fixedVertexCount (h.smulEquiv (DihedralGroup.sr 0)) = 56)
    (reflection_adjacent_moved :
      adjacentMovedCount Γ (h.smulEquiv (DihedralGroup.sr 0)) = 112) :
    ¬ Nonempty (BranchOrbitABCActionLevelMinimalRemainingBoundary h) :=
  (E7Minus8CharacterReflectionCountBoundary.ofD19CharacterInputComplement h
    characterInput reflection_fixed_count reflection_adjacent_moved)
      |>.no_actionLevelMinimalRemainingBoundary

/-- Complementary `D19CharacterInput` route rules out the refined
minimal-remaining current-gap boundary. -/
theorem no_actionLevelMinimalRemainingRefinedBoundary_of_d19CharacterInputComplement
    (h : D19ActsOnMoore57 V Γ)
    (characterInput : D19CharacterInput h)
    (reflection_fixed_count :
      fixedVertexCount (h.smulEquiv (DihedralGroup.sr 0)) = 56)
    (reflection_adjacent_moved :
      adjacentMovedCount Γ (h.smulEquiv (DihedralGroup.sr 0)) = 112) :
    ¬ Nonempty (BranchOrbitABCActionLevelMinimalRemainingRefinedBoundary h) :=
  (E7Minus8CharacterReflectionCountBoundary.ofD19CharacterInputComplement h
    characterInput reflection_fixed_count reflection_adjacent_moved)
      |>.no_actionLevelMinimalRemainingRefinedBoundary

/-- Complementary `D19CharacterInput` route rules out the matching-equation
refined minimal-remaining current-gap boundary. -/
theorem no_actionLevelMinimalRemainingRefinedMatchingBoundary_of_d19CharacterInputComplement
    (h : D19ActsOnMoore57 V Γ)
    (characterInput : D19CharacterInput h)
    (reflection_fixed_count :
      fixedVertexCount (h.smulEquiv (DihedralGroup.sr 0)) = 56)
    (reflection_adjacent_moved :
      adjacentMovedCount Γ (h.smulEquiv (DihedralGroup.sr 0)) = 112) :
    ¬ Nonempty (BranchOrbitABCActionLevelMinimalRemainingRefinedMatchingBoundary h) :=
  (E7Minus8CharacterReflectionCountBoundary.ofD19CharacterInputComplement h
    characterInput reflection_fixed_count reflection_adjacent_moved)
      |>.no_actionLevelMinimalRemainingRefinedMatchingBoundary

/-- Fixed-star variant of
`no_actionLevelFinalBoundary_of_d19CharacterInputComplement`. -/
theorem no_actionLevelFinalBoundary_of_d19CharacterInputComplementAndReflectionStar
    (h : D19ActsOnMoore57 V Γ)
    (characterInput : D19CharacterInput h)
    (hStar :
      InvolutionFixedSetStar56 Γ (h.smulEquiv (DihedralGroup.sr 0))) :
    ¬ Nonempty (BranchOrbitABCActionLevelFinalBoundary h) :=
  (E7Minus8CharacterReflectionCountBoundary.ofD19CharacterInputComplementAndReflectionStar
    h characterInput hStar)
      |>.no_actionLevelFinalBoundary

/-- Fixed-star variant of
`no_actionLevelMinimalRemainingRefinedMatchingBoundary_of_d19CharacterInputComplement`. -/
theorem no_actionLevelMinimalRemainingRefinedMatchingBoundary_of_d19CharacterInputComplementAndReflectionStar
    (h : D19ActsOnMoore57 V Γ)
    (characterInput : D19CharacterInput h)
    (hStar :
      InvolutionFixedSetStar56 Γ (h.smulEquiv (DihedralGroup.sr 0))) :
    ¬ Nonempty (BranchOrbitABCActionLevelMinimalRemainingRefinedMatchingBoundary h) :=
  (E7Minus8CharacterReflectionCountBoundary.ofD19CharacterInputComplementAndReflectionStar
    h characterInput hStar)
      |>.no_actionLevelMinimalRemainingRefinedMatchingBoundary

/-- Final character inputs route to the action-level final no-go through the
complementary minus-8 package. -/
theorem no_actionLevelFinalBoundary_of_d19FinalCharacterInputsComplement
    (h : D19ActsOnMoore57 V Γ)
    (character : D19FinalCharacterInputs h)
    (reflection_fixed_count :
      fixedVertexCount (h.smulEquiv (DihedralGroup.sr 0)) = 56)
    (reflection_adjacent_moved :
      adjacentMovedCount Γ (h.smulEquiv (DihedralGroup.sr 0)) = 112) :
    ¬ Nonempty (BranchOrbitABCActionLevelFinalBoundary h) :=
  (E7Minus8CharacterReflectionCountBoundary.ofD19FinalCharacterInputsComplement h
    character reflection_fixed_count reflection_adjacent_moved)
      |>.no_actionLevelFinalBoundary

/-- Final character inputs route to the matching-equation refined
minimal-remaining no-go through the complementary minus-8 package. -/
theorem no_actionLevelMinimalRemainingRefinedMatchingBoundary_of_d19FinalCharacterInputsComplement
    (h : D19ActsOnMoore57 V Γ)
    (character : D19FinalCharacterInputs h)
    (reflection_fixed_count :
      fixedVertexCount (h.smulEquiv (DihedralGroup.sr 0)) = 56)
    (reflection_adjacent_moved :
      adjacentMovedCount Γ (h.smulEquiv (DihedralGroup.sr 0)) = 112) :
    ¬ Nonempty (BranchOrbitABCActionLevelMinimalRemainingRefinedMatchingBoundary h) :=
  (E7Minus8CharacterReflectionCountBoundary.ofD19FinalCharacterInputsComplement h
    character reflection_fixed_count reflection_adjacent_moved)
      |>.no_actionLevelMinimalRemainingRefinedMatchingBoundary

/-- Fixed-star final-character route to the action-level final no-go. -/
theorem no_actionLevelFinalBoundary_of_d19FinalCharacterInputsComplementAndReflectionStar
    (h : D19ActsOnMoore57 V Γ)
    (character : D19FinalCharacterInputs h)
    (hStar :
      InvolutionFixedSetStar56 Γ (h.smulEquiv (DihedralGroup.sr 0))) :
    ¬ Nonempty (BranchOrbitABCActionLevelFinalBoundary h) :=
  (E7Minus8CharacterReflectionCountBoundary.ofD19FinalCharacterInputsComplementAndReflectionStar
    h character hStar)
      |>.no_actionLevelFinalBoundary

/-- Fixed-star final-character route to the matching-equation refined
minimal-remaining no-go. -/
theorem no_actionLevelMinimalRemainingRefinedMatchingBoundary_of_d19FinalCharacterInputsComplementAndReflectionStar
    (h : D19ActsOnMoore57 V Γ)
    (character : D19FinalCharacterInputs h)
    (hStar :
      InvolutionFixedSetStar56 Γ (h.smulEquiv (DihedralGroup.sr 0))) :
    ¬ Nonempty (BranchOrbitABCActionLevelMinimalRemainingRefinedMatchingBoundary h) :=
  (E7Minus8CharacterReflectionCountBoundary.ofD19FinalCharacterInputsComplementAndReflectionStar
    h character hStar)
      |>.no_actionLevelMinimalRemainingRefinedMatchingBoundary

end D19ActsOnMoore57

end

end Moore57

/-!
# Complement route from representation input with automatic rotation bounds

The raw `D19ActsOnMoore57` action already supplies the rotation fixed-count
upper bound used by `D19FinalCharacterInputs`.  This file removes that explicit
fixed-bound input from the representation side: a representation-character
input, or equivalently a trace-core character boundary, is enough to build the
final character package consumed by the complementary `(-8)` route.
-/

namespace Moore57

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

namespace D19ActsOnMoore57

namespace D19RepresentationCharacterInput

variable {h : D19ActsOnMoore57 V Γ}

/-- A representation-character input becomes final character input using the
rotation fixed-count bound already proved from the raw action. -/
def toD19FinalCharacterInputs_autoFixedBound
    (input : D19RepresentationCharacterInput h) :
    D19FinalCharacterInputs h where
  representation := input
  fixedUpperBound := RotationFixedUpperBoundInput.of_provedRotationFixedCountOne h

end D19RepresentationCharacterInput

namespace TraceCoreCharacterBoundary

variable {h : D19ActsOnMoore57 V Γ}

/-- Trace-core character data becomes final character input using the rotation
fixed-count bound already proved from the raw action. -/
def toD19FinalCharacterInputs_autoFixedBound
    (data : TraceCoreCharacterBoundary h) :
    D19FinalCharacterInputs h :=
  data.toD19RepresentationCharacterInput.toD19FinalCharacterInputs_autoFixedBound

@[simp] theorem toD19FinalCharacterInputs_autoFixedBound_representation
    (data : TraceCoreCharacterBoundary h) :
    data.toD19FinalCharacterInputs_autoFixedBound.representation =
      data.toD19RepresentationCharacterInput :=
  rfl

end TraceCoreCharacterBoundary

/-- Representation-character input plus a fixed-star reflection input gives a
nonempty linear-character input through the complementary minus-8 route, with
the rotation fixed-bound supplied by the raw action. -/
theorem nonempty_d19LinearCharacterInput_of_representationCharacterInputComplementAndReflectionStar
    (h : D19ActsOnMoore57 V Γ)
    (representation : D19RepresentationCharacterInput h)
    (hStar :
      InvolutionFixedSetStar56 Γ (h.smulEquiv (DihedralGroup.sr 0))) :
    Nonempty (D19LinearCharacterInput h) :=
  nonempty_d19LinearCharacterInput_of_d19FinalCharacterInputsComplementAndReflectionStar
    h representation.toD19FinalCharacterInputs_autoFixedBound hStar

/-- Representation-character input plus a fixed-star reflection input gives
fixed-star boundaries for all reflections through the complementary route. -/
theorem involutionFixedSetStar56_of_representationCharacterInputComplementAndReflectionStar_raw_reflection
    (h : D19ActsOnMoore57 V Γ)
    (representation : D19RepresentationCharacterInput h)
    (hStar :
      InvolutionFixedSetStar56 Γ (h.smulEquiv (DihedralGroup.sr 0)))
    (k : ZMod 19) :
    InvolutionFixedSetStar56 Γ (h.smulEquiv (DihedralGroup.sr k)) :=
  involutionFixedSetStar56_of_d19FinalCharacterInputsComplementAndReflectionStar_raw_reflection
    h representation.toD19FinalCharacterInputs_autoFixedBound hStar k

/-- Representation-character input plus a fixed-star reflection input gives
`K_{1,55}` witnesses for all reflections through the complementary route. -/
theorem nonempty_involutionK155_of_representationCharacterInputComplementAndReflectionStar_raw_reflection
    (h : D19ActsOnMoore57 V Γ)
    (representation : D19RepresentationCharacterInput h)
    (hStar :
      InvolutionFixedSetStar56 Γ (h.smulEquiv (DihedralGroup.sr 0)))
    (k : ZMod 19) :
    Nonempty (InvolutionK155 Γ (h.smulEquiv (DihedralGroup.sr k))) :=
  nonempty_involutionK155_of_d19FinalCharacterInputsComplementAndReflectionStar_raw_reflection
    h representation.toD19FinalCharacterInputs_autoFixedBound hStar k

/-- Representation-character input plus a fixed-star reflection input gives the
fixed-center leaf boundary through the complementary route. -/
theorem reflectionFixedCenterLeafBoundary_of_representationCharacterInputComplementAndReflectionStar
    (h : D19ActsOnMoore57 V Γ)
    (representation : D19RepresentationCharacterInput h)
    (hStar :
      InvolutionFixedSetStar56 Γ (h.smulEquiv (DihedralGroup.sr 0))) :
    ReflectionFixedCenterLeafBoundary h :=
  reflectionFixedCenterLeafBoundary_of_d19FinalCharacterInputsComplementAndReflectionStar
    h representation.toD19FinalCharacterInputs_autoFixedBound hStar

/-- Representation-character input plus a fixed-star reflection input rules
out the current final-gap boundary through the complementary route. -/
theorem no_currentFinalGapBoundary_of_representationCharacterInputComplementAndReflectionStar
    (h : D19ActsOnMoore57 V Γ)
    (representation : D19RepresentationCharacterInput h)
    (hStar :
      InvolutionFixedSetStar56 Γ (h.smulEquiv (DihedralGroup.sr 0))) :
    ¬ Nonempty (BranchOrbitABCCurrentFinalGapBoundary h) :=
  no_currentFinalGapBoundary_of_d19FinalCharacterInputsComplementAndReflectionStar
    h representation.toD19FinalCharacterInputs_autoFixedBound hStar

/-- Representation-character input plus a fixed-star reflection input rules
out the action-level final boundary through the complementary route. -/
theorem no_actionLevelFinalBoundary_of_representationCharacterInputComplementAndReflectionStar
    (h : D19ActsOnMoore57 V Γ)
    (representation : D19RepresentationCharacterInput h)
    (hStar :
      InvolutionFixedSetStar56 Γ (h.smulEquiv (DihedralGroup.sr 0))) :
    ¬ Nonempty (BranchOrbitABCActionLevelFinalBoundary h) :=
  no_actionLevelFinalBoundary_of_d19FinalCharacterInputsComplementAndReflectionStar
    h representation.toD19FinalCharacterInputs_autoFixedBound hStar

/-- Trace-core character data plus a fixed-star reflection input gives a
nonempty linear-character input through the complementary route, with the
rotation fixed-bound supplied by the raw action. -/
theorem nonempty_d19LinearCharacterInput_of_traceCoreCharacterBoundaryComplementAndReflectionStar
    (h : D19ActsOnMoore57 V Γ)
    (traceCore : TraceCoreCharacterBoundary h)
    (hStar :
      InvolutionFixedSetStar56 Γ (h.smulEquiv (DihedralGroup.sr 0))) :
    Nonempty (D19LinearCharacterInput h) :=
  nonempty_d19LinearCharacterInput_of_representationCharacterInputComplementAndReflectionStar
    h traceCore.toD19RepresentationCharacterInput hStar

/-- Trace-core character data plus a fixed-star reflection input gives
fixed-star boundaries for all reflections through the complementary route. -/
theorem involutionFixedSetStar56_of_traceCoreCharacterBoundaryComplementAndReflectionStar_raw_reflection
    (h : D19ActsOnMoore57 V Γ)
    (traceCore : TraceCoreCharacterBoundary h)
    (hStar :
      InvolutionFixedSetStar56 Γ (h.smulEquiv (DihedralGroup.sr 0)))
    (k : ZMod 19) :
    InvolutionFixedSetStar56 Γ (h.smulEquiv (DihedralGroup.sr k)) :=
  involutionFixedSetStar56_of_representationCharacterInputComplementAndReflectionStar_raw_reflection
    h traceCore.toD19RepresentationCharacterInput hStar k

/-- Trace-core character data plus a fixed-star reflection input gives
`K_{1,55}` witnesses for all reflections through the complementary route. -/
theorem nonempty_involutionK155_of_traceCoreCharacterBoundaryComplementAndReflectionStar_raw_reflection
    (h : D19ActsOnMoore57 V Γ)
    (traceCore : TraceCoreCharacterBoundary h)
    (hStar :
      InvolutionFixedSetStar56 Γ (h.smulEquiv (DihedralGroup.sr 0)))
    (k : ZMod 19) :
    Nonempty (InvolutionK155 Γ (h.smulEquiv (DihedralGroup.sr k))) :=
  nonempty_involutionK155_of_representationCharacterInputComplementAndReflectionStar_raw_reflection
    h traceCore.toD19RepresentationCharacterInput hStar k

/-- Trace-core character data plus a fixed-star reflection input gives the
fixed-center leaf boundary through the complementary route. -/
theorem reflectionFixedCenterLeafBoundary_of_traceCoreCharacterBoundaryComplementAndReflectionStar
    (h : D19ActsOnMoore57 V Γ)
    (traceCore : TraceCoreCharacterBoundary h)
    (hStar :
      InvolutionFixedSetStar56 Γ (h.smulEquiv (DihedralGroup.sr 0))) :
    ReflectionFixedCenterLeafBoundary h :=
  reflectionFixedCenterLeafBoundary_of_representationCharacterInputComplementAndReflectionStar
    h traceCore.toD19RepresentationCharacterInput hStar

/-- Trace-core character data plus a fixed-star reflection input rules out the
current final-gap boundary through the complementary route. -/
theorem no_currentFinalGapBoundary_of_traceCoreCharacterBoundaryComplementAndReflectionStar
    (h : D19ActsOnMoore57 V Γ)
    (traceCore : TraceCoreCharacterBoundary h)
    (hStar :
      InvolutionFixedSetStar56 Γ (h.smulEquiv (DihedralGroup.sr 0))) :
    ¬ Nonempty (BranchOrbitABCCurrentFinalGapBoundary h) :=
  no_currentFinalGapBoundary_of_representationCharacterInputComplementAndReflectionStar
    h traceCore.toD19RepresentationCharacterInput hStar

/-- Trace-core character data plus a fixed-star reflection input rules out the
action-level final boundary through the complementary route. -/
theorem no_actionLevelFinalBoundary_of_traceCoreCharacterBoundaryComplementAndReflectionStar
    (h : D19ActsOnMoore57 V Γ)
    (traceCore : TraceCoreCharacterBoundary h)
    (hStar :
      InvolutionFixedSetStar56 Γ (h.smulEquiv (DihedralGroup.sr 0))) :
    ¬ Nonempty (BranchOrbitABCActionLevelFinalBoundary h) :=
  no_actionLevelFinalBoundary_of_representationCharacterInputComplementAndReflectionStar
    h traceCore.toD19RepresentationCharacterInput hStar

end D19ActsOnMoore57

end

end Moore57

/-!
# Fixed-count-only complement route for character inputs

This file lifts the fixed-count-only `D19TraceInput` complement route to the
coarser character packages.  The adjacent-moved count is derived from the
reflection fixed count via the paper fixed-star bridge.
-/

namespace Moore57

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

namespace D19ActsOnMoore57

namespace E7Minus8CharacterReflectionCountBoundary

variable (h : D19ActsOnMoore57 V Γ)

/-- Build the packaged E7/minus-8 boundary from `D19CharacterInput h` and only
the standard reflection fixed count `56`. -/
def ofD19CharacterInputComplementAndReflectionFixedCount
    (characterInput : D19CharacterInput h)
    (reflection_fixed_count :
      fixedVertexCount (h.smulEquiv (DihedralGroup.sr 0)) = 56) :
    E7Minus8CharacterReflectionCountBoundary h :=
  ofD19TraceInputComplementAndReflectionFixedCount h
    characterInput.toD19TraceInput reflection_fixed_count

/-- Build the packaged E7/minus-8 boundary from final character inputs and only
the standard reflection fixed count `56`. -/
def ofD19FinalCharacterInputsComplementAndReflectionFixedCount
    (character : D19FinalCharacterInputs h)
    (reflection_fixed_count :
      fixedVertexCount (h.smulEquiv (DihedralGroup.sr 0)) = 56) :
    E7Minus8CharacterReflectionCountBoundary h :=
  ofD19TraceInputComplementAndReflectionFixedCount h
    character.toD19TraceInput reflection_fixed_count

/-- Build the packaged E7/minus-8 boundary from representation-character input,
using the raw action for the rotation fixed-count bound and only the standard
reflection fixed count `56`. -/
def ofD19RepresentationCharacterInputComplementAndReflectionFixedCount
    (representation : D19RepresentationCharacterInput h)
    (reflection_fixed_count :
      fixedVertexCount (h.smulEquiv (DihedralGroup.sr 0)) = 56) :
    E7Minus8CharacterReflectionCountBoundary h :=
  ofD19FinalCharacterInputsComplementAndReflectionFixedCount h
    representation.toD19FinalCharacterInputs_autoFixedBound reflection_fixed_count

/-- Build the packaged E7/minus-8 boundary from trace-core character data,
using the raw action for the rotation fixed-count bound and only the standard
reflection fixed count `56`. -/
def ofTraceCoreCharacterBoundaryComplementAndReflectionFixedCount
    (traceCore : TraceCoreCharacterBoundary h)
    (reflection_fixed_count :
      fixedVertexCount (h.smulEquiv (DihedralGroup.sr 0)) = 56) :
    E7Minus8CharacterReflectionCountBoundary h :=
  ofD19RepresentationCharacterInputComplementAndReflectionFixedCount h
    traceCore.toD19RepresentationCharacterInput reflection_fixed_count

end E7Minus8CharacterReflectionCountBoundary

/-- `D19CharacterInput` plus the standard reflection fixed count gives a
nonempty linear-character input through the complementary route. -/
theorem nonempty_d19LinearCharacterInput_of_d19CharacterInputComplementAndReflectionFixedCount
    (h : D19ActsOnMoore57 V Γ)
    (characterInput : D19CharacterInput h)
    (reflection_fixed_count :
      fixedVertexCount (h.smulEquiv (DihedralGroup.sr 0)) = 56) :
    Nonempty (D19LinearCharacterInput h) :=
  (E7Minus8CharacterReflectionCountBoundary.ofD19CharacterInputComplementAndReflectionFixedCount h characterInput
      reflection_fixed_count)
      |>.nonempty_d19LinearCharacterInput

/-- The fixed-count-only `D19CharacterInput` route gives fixed-star boundaries
for all reflections. -/
theorem involutionFixedSetStar56_of_d19CharacterInputComplementAndReflectionFixedCount_raw_reflection
    (h : D19ActsOnMoore57 V Γ)
    (characterInput : D19CharacterInput h)
    (reflection_fixed_count :
      fixedVertexCount (h.smulEquiv (DihedralGroup.sr 0)) = 56)
    (k : ZMod 19) :
    InvolutionFixedSetStar56 Γ (h.smulEquiv (DihedralGroup.sr k)) :=
  (E7Minus8CharacterReflectionCountBoundary.ofD19CharacterInputComplementAndReflectionFixedCount h characterInput
      reflection_fixed_count)
      |>.involutionFixedSetStar56_raw_reflection k

/-- The fixed-count-only `D19CharacterInput` route gives `K_{1,55}` witnesses
for all reflections. -/
theorem nonempty_involutionK155_of_d19CharacterInputComplementAndReflectionFixedCount_raw_reflection
    (h : D19ActsOnMoore57 V Γ)
    (characterInput : D19CharacterInput h)
    (reflection_fixed_count :
      fixedVertexCount (h.smulEquiv (DihedralGroup.sr 0)) = 56)
    (k : ZMod 19) :
    Nonempty (InvolutionK155 Γ (h.smulEquiv (DihedralGroup.sr k))) :=
  (E7Minus8CharacterReflectionCountBoundary.ofD19CharacterInputComplementAndReflectionFixedCount h characterInput
      reflection_fixed_count)
      |>.nonempty_involutionK155_raw_reflection k

/-- The fixed-count-only `D19CharacterInput` route gives the fixed-center leaf
boundary. -/
theorem reflectionFixedCenterLeafBoundary_of_d19CharacterInputComplementAndReflectionFixedCount
    (h : D19ActsOnMoore57 V Γ)
    (characterInput : D19CharacterInput h)
    (reflection_fixed_count :
      fixedVertexCount (h.smulEquiv (DihedralGroup.sr 0)) = 56) :
    ReflectionFixedCenterLeafBoundary h :=
  (E7Minus8CharacterReflectionCountBoundary.ofD19CharacterInputComplementAndReflectionFixedCount h characterInput
      reflection_fixed_count)
      |>.reflectionFixedCenterLeafBoundary

/-- The fixed-count-only `D19CharacterInput` route gives the representation
component boundary. -/
theorem representationCharacterComponentsBoundary_of_d19CharacterInputComplementAndReflectionFixedCount
    (h : D19ActsOnMoore57 V Γ)
    (characterInput : D19CharacterInput h)
    (reflection_fixed_count :
      fixedVertexCount (h.smulEquiv (DihedralGroup.sr 0)) = 56) :
    RepresentationCharacterComponentsBoundary h :=
  (E7Minus8CharacterReflectionCountBoundary.ofD19CharacterInputComplementAndReflectionFixedCount h characterInput
      reflection_fixed_count)
      |>.representationCharacterComponentsBoundary

/-- The fixed-count-only `D19CharacterInput` route rules out the current
final-gap boundary. -/
theorem no_currentFinalGapBoundary_of_d19CharacterInputComplementAndReflectionFixedCount
    (h : D19ActsOnMoore57 V Γ)
    (characterInput : D19CharacterInput h)
    (reflection_fixed_count :
      fixedVertexCount (h.smulEquiv (DihedralGroup.sr 0)) = 56) :
    ¬ Nonempty (BranchOrbitABCCurrentFinalGapBoundary h) :=
  (E7Minus8CharacterReflectionCountBoundary.ofD19CharacterInputComplementAndReflectionFixedCount h characterInput
      reflection_fixed_count)
      |>.no_currentFinalGapBoundary

/-- The fixed-count-only `D19CharacterInput` route rules out the action-level
final boundary. -/
theorem no_actionLevelFinalBoundary_of_d19CharacterInputComplementAndReflectionFixedCount
    (h : D19ActsOnMoore57 V Γ)
    (characterInput : D19CharacterInput h)
    (reflection_fixed_count :
      fixedVertexCount (h.smulEquiv (DihedralGroup.sr 0)) = 56) :
    ¬ Nonempty (BranchOrbitABCActionLevelFinalBoundary h) :=
  (E7Minus8CharacterReflectionCountBoundary.ofD19CharacterInputComplementAndReflectionFixedCount h characterInput
      reflection_fixed_count)
      |>.no_actionLevelFinalBoundary

/-- Final character inputs plus the standard reflection fixed count give a
nonempty linear-character input through the complementary route. -/
theorem nonempty_d19LinearCharacterInput_of_d19FinalCharacterInputsComplementAndReflectionFixedCount
    (h : D19ActsOnMoore57 V Γ)
    (character : D19FinalCharacterInputs h)
    (reflection_fixed_count :
      fixedVertexCount (h.smulEquiv (DihedralGroup.sr 0)) = 56) :
    Nonempty (D19LinearCharacterInput h) :=
  (E7Minus8CharacterReflectionCountBoundary.ofD19FinalCharacterInputsComplementAndReflectionFixedCount h character
      reflection_fixed_count)
      |>.nonempty_d19LinearCharacterInput

/-- Final character inputs plus the standard reflection fixed count rule out
the current final-gap boundary through the complementary route. -/
theorem no_currentFinalGapBoundary_of_d19FinalCharacterInputsComplementAndReflectionFixedCount
    (h : D19ActsOnMoore57 V Γ)
    (character : D19FinalCharacterInputs h)
    (reflection_fixed_count :
      fixedVertexCount (h.smulEquiv (DihedralGroup.sr 0)) = 56) :
    ¬ Nonempty (BranchOrbitABCCurrentFinalGapBoundary h) :=
  (E7Minus8CharacterReflectionCountBoundary.ofD19FinalCharacterInputsComplementAndReflectionFixedCount h character
      reflection_fixed_count)
      |>.no_currentFinalGapBoundary

/-- Final character inputs plus the standard reflection fixed count rule out
the action-level final boundary through the complementary route. -/
theorem no_actionLevelFinalBoundary_of_d19FinalCharacterInputsComplementAndReflectionFixedCount
    (h : D19ActsOnMoore57 V Γ)
    (character : D19FinalCharacterInputs h)
    (reflection_fixed_count :
      fixedVertexCount (h.smulEquiv (DihedralGroup.sr 0)) = 56) :
    ¬ Nonempty (BranchOrbitABCActionLevelFinalBoundary h) :=
  (E7Minus8CharacterReflectionCountBoundary.ofD19FinalCharacterInputsComplementAndReflectionFixedCount h character
      reflection_fixed_count)
      |>.no_actionLevelFinalBoundary

/-- Representation-character input plus the standard reflection fixed count
gives a nonempty linear-character input through the complementary route, with
the rotation fixed-bound supplied by the raw action. -/
theorem nonempty_d19LinearCharacterInput_of_representationCharacterInputComplementAndReflectionFixedCount
    (h : D19ActsOnMoore57 V Γ)
    (representation : D19RepresentationCharacterInput h)
    (reflection_fixed_count :
      fixedVertexCount (h.smulEquiv (DihedralGroup.sr 0)) = 56) :
    Nonempty (D19LinearCharacterInput h) :=
  (E7Minus8CharacterReflectionCountBoundary.ofD19RepresentationCharacterInputComplementAndReflectionFixedCount h
      representation reflection_fixed_count)
      |>.nonempty_d19LinearCharacterInput

/-- Representation-character input plus the standard reflection fixed count
rules out the current final-gap boundary through the complementary route. -/
theorem no_currentFinalGapBoundary_of_representationCharacterInputComplementAndReflectionFixedCount
    (h : D19ActsOnMoore57 V Γ)
    (representation : D19RepresentationCharacterInput h)
    (reflection_fixed_count :
      fixedVertexCount (h.smulEquiv (DihedralGroup.sr 0)) = 56) :
    ¬ Nonempty (BranchOrbitABCCurrentFinalGapBoundary h) :=
  (E7Minus8CharacterReflectionCountBoundary.ofD19RepresentationCharacterInputComplementAndReflectionFixedCount h
      representation reflection_fixed_count)
      |>.no_currentFinalGapBoundary

/-- Representation-character input plus the standard reflection fixed count
rules out the action-level final boundary through the complementary route. -/
theorem no_actionLevelFinalBoundary_of_representationCharacterInputComplementAndReflectionFixedCount
    (h : D19ActsOnMoore57 V Γ)
    (representation : D19RepresentationCharacterInput h)
    (reflection_fixed_count :
      fixedVertexCount (h.smulEquiv (DihedralGroup.sr 0)) = 56) :
    ¬ Nonempty (BranchOrbitABCActionLevelFinalBoundary h) :=
  (E7Minus8CharacterReflectionCountBoundary.ofD19RepresentationCharacterInputComplementAndReflectionFixedCount h
      representation reflection_fixed_count)
      |>.no_actionLevelFinalBoundary

/-- Trace-core character data plus the standard reflection fixed count gives a
nonempty linear-character input through the complementary route, with the
rotation fixed-bound supplied by the raw action. -/
theorem nonempty_d19LinearCharacterInput_of_traceCoreCharacterBoundaryComplementAndReflectionFixedCount
    (h : D19ActsOnMoore57 V Γ)
    (traceCore : TraceCoreCharacterBoundary h)
    (reflection_fixed_count :
      fixedVertexCount (h.smulEquiv (DihedralGroup.sr 0)) = 56) :
    Nonempty (D19LinearCharacterInput h) :=
  (E7Minus8CharacterReflectionCountBoundary.ofTraceCoreCharacterBoundaryComplementAndReflectionFixedCount h
      traceCore reflection_fixed_count)
      |>.nonempty_d19LinearCharacterInput

/-- Trace-core character data plus the standard reflection fixed count rules
out the current final-gap boundary through the complementary route. -/
theorem no_currentFinalGapBoundary_of_traceCoreCharacterBoundaryComplementAndReflectionFixedCount
    (h : D19ActsOnMoore57 V Γ)
    (traceCore : TraceCoreCharacterBoundary h)
    (reflection_fixed_count :
      fixedVertexCount (h.smulEquiv (DihedralGroup.sr 0)) = 56) :
    ¬ Nonempty (BranchOrbitABCCurrentFinalGapBoundary h) :=
  (E7Minus8CharacterReflectionCountBoundary.ofTraceCoreCharacterBoundaryComplementAndReflectionFixedCount h
      traceCore reflection_fixed_count)
      |>.no_currentFinalGapBoundary

/-- Trace-core character data plus the standard reflection fixed count rules
out the action-level final boundary through the complementary route. -/
theorem no_actionLevelFinalBoundary_of_traceCoreCharacterBoundaryComplementAndReflectionFixedCount
    (h : D19ActsOnMoore57 V Γ)
    (traceCore : TraceCoreCharacterBoundary h)
    (reflection_fixed_count :
      fixedVertexCount (h.smulEquiv (DihedralGroup.sr 0)) = 56) :
    ¬ Nonempty (BranchOrbitABCActionLevelFinalBoundary h) :=
  (E7Minus8CharacterReflectionCountBoundary.ofTraceCoreCharacterBoundaryComplementAndReflectionFixedCount h
      traceCore reflection_fixed_count)
      |>.no_actionLevelFinalBoundary

end D19ActsOnMoore57

end

end Moore57

/-!
# Fixed-count-only complementary minus-8 route from data packages

This file lifts the fixed-count-only `D19TraceInput` complementary route to the
action, orbit, reduced, and geometric data records.  All proofs are thin
wrappers through `data.traceInput` or `data.characterInput.toD19TraceInput`.
-/

namespace Moore57

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

namespace D19ActionConcreteData

variable {h : D19ActsOnMoore57 V Γ}

/-- Concrete action data plus the standard reflection fixed count gives a
nonempty linear-character input through the fixed-count-only complementary
minus-8 route. -/
theorem nonempty_d19LinearCharacterInput_of_complementAndReflectionFixedCount
    (data : D19ActionConcreteData h)
    (reflection_fixed_count :
      fixedVertexCount (h.smulEquiv (DihedralGroup.sr 0)) = 56) :
    Nonempty (D19ActsOnMoore57.D19LinearCharacterInput h) :=
  D19ActsOnMoore57.nonempty_d19LinearCharacterInput_of_d19TraceInputComplementAndReflectionFixedCount
    h data.traceInput reflection_fixed_count

/-- Concrete action data plus the standard reflection fixed count gives
fixed-star boundaries for all reflections through the fixed-count-only
complementary minus-8 route. -/
theorem involutionFixedSetStar56_of_complementAndReflectionFixedCount_raw_reflection
    (data : D19ActionConcreteData h)
    (reflection_fixed_count :
      fixedVertexCount (h.smulEquiv (DihedralGroup.sr 0)) = 56)
    (k : ZMod 19) :
    InvolutionFixedSetStar56 Γ (h.smulEquiv (DihedralGroup.sr k)) :=
  D19ActsOnMoore57.involutionFixedSetStar56_of_d19TraceInputComplementAndReflectionFixedCount_raw_reflection
    h data.traceInput reflection_fixed_count k

/-- Concrete action data plus the standard reflection fixed count gives
`K_{1,55}` witnesses for all reflections through the fixed-count-only
complementary minus-8 route. -/
theorem nonempty_involutionK155_of_complementAndReflectionFixedCount_raw_reflection
    (data : D19ActionConcreteData h)
    (reflection_fixed_count :
      fixedVertexCount (h.smulEquiv (DihedralGroup.sr 0)) = 56)
    (k : ZMod 19) :
    Nonempty (InvolutionK155 Γ (h.smulEquiv (DihedralGroup.sr k))) :=
  D19ActsOnMoore57.nonempty_involutionK155_of_d19TraceInputComplementAndReflectionFixedCount_raw_reflection
    h data.traceInput reflection_fixed_count k

/-- Concrete action data plus the standard reflection fixed count gives the
fixed-center leaf boundary through the fixed-count-only complementary minus-8
route. -/
theorem reflectionFixedCenterLeafBoundary_of_complementAndReflectionFixedCount
    (data : D19ActionConcreteData h)
    (reflection_fixed_count :
      fixedVertexCount (h.smulEquiv (DihedralGroup.sr 0)) = 56) :
    ReflectionFixedCenterLeafBoundary h :=
  D19ActsOnMoore57.reflectionFixedCenterLeafBoundary_of_d19TraceInputComplementAndReflectionFixedCount
    h data.traceInput reflection_fixed_count

/-- Concrete action data plus the standard reflection fixed count gives the
representation character component boundary. -/
theorem representationCharacterComponentsBoundary_of_complementAndReflectionFixedCount
    (data : D19ActionConcreteData h)
    (reflection_fixed_count :
      fixedVertexCount (h.smulEquiv (DihedralGroup.sr 0)) = 56) :
    D19ActsOnMoore57.RepresentationCharacterComponentsBoundary h :=
  D19ActsOnMoore57.representationCharacterComponentsBoundary_of_d19TraceInputComplementAndReflectionFixedCount
    h data.traceInput reflection_fixed_count

/-- Concrete action data plus the standard reflection fixed count rules out
the current branch-orbit final-gap boundary. -/
theorem no_currentFinalGapBoundary_of_complementAndReflectionFixedCount
    (data : D19ActionConcreteData h)
    (reflection_fixed_count :
      fixedVertexCount (h.smulEquiv (DihedralGroup.sr 0)) = 56) :
    ¬ Nonempty (BranchOrbitABCCurrentFinalGapBoundary h) :=
  D19ActsOnMoore57.no_currentFinalGapBoundary_of_d19TraceInputComplementAndReflectionFixedCount
    h data.traceInput reflection_fixed_count

end D19ActionConcreteData

namespace D19ActionOrbitConcreteData

variable {h : D19ActsOnMoore57 V Γ}

/-- Orbit-generated concrete action data plus the standard reflection fixed
count gives a nonempty linear-character input through the fixed-count-only
complementary minus-8 route. -/
theorem nonempty_d19LinearCharacterInput_of_complementAndReflectionFixedCount
    (data : D19ActionOrbitConcreteData h)
    (reflection_fixed_count :
      fixedVertexCount (h.smulEquiv (DihedralGroup.sr 0)) = 56) :
    Nonempty (D19ActsOnMoore57.D19LinearCharacterInput h) :=
  D19ActsOnMoore57.nonempty_d19LinearCharacterInput_of_d19TraceInputComplementAndReflectionFixedCount
    h data.traceInput reflection_fixed_count

/-- Orbit-generated concrete action data plus the standard reflection fixed
count gives fixed-star boundaries for all reflections through the
fixed-count-only complementary minus-8 route. -/
theorem involutionFixedSetStar56_of_complementAndReflectionFixedCount_raw_reflection
    (data : D19ActionOrbitConcreteData h)
    (reflection_fixed_count :
      fixedVertexCount (h.smulEquiv (DihedralGroup.sr 0)) = 56)
    (k : ZMod 19) :
    InvolutionFixedSetStar56 Γ (h.smulEquiv (DihedralGroup.sr k)) :=
  D19ActsOnMoore57.involutionFixedSetStar56_of_d19TraceInputComplementAndReflectionFixedCount_raw_reflection
    h data.traceInput reflection_fixed_count k

/-- Orbit-generated concrete action data plus the standard reflection fixed
count gives `K_{1,55}` witnesses for all reflections through the
fixed-count-only complementary minus-8 route. -/
theorem nonempty_involutionK155_of_complementAndReflectionFixedCount_raw_reflection
    (data : D19ActionOrbitConcreteData h)
    (reflection_fixed_count :
      fixedVertexCount (h.smulEquiv (DihedralGroup.sr 0)) = 56)
    (k : ZMod 19) :
    Nonempty (InvolutionK155 Γ (h.smulEquiv (DihedralGroup.sr k))) :=
  D19ActsOnMoore57.nonempty_involutionK155_of_d19TraceInputComplementAndReflectionFixedCount_raw_reflection
    h data.traceInput reflection_fixed_count k

/-- Orbit-generated concrete action data plus the standard reflection fixed
count gives the fixed-center leaf boundary through the fixed-count-only
complementary minus-8 route. -/
theorem reflectionFixedCenterLeafBoundary_of_complementAndReflectionFixedCount
    (data : D19ActionOrbitConcreteData h)
    (reflection_fixed_count :
      fixedVertexCount (h.smulEquiv (DihedralGroup.sr 0)) = 56) :
    ReflectionFixedCenterLeafBoundary h :=
  D19ActsOnMoore57.reflectionFixedCenterLeafBoundary_of_d19TraceInputComplementAndReflectionFixedCount
    h data.traceInput reflection_fixed_count

/-- Orbit-generated concrete action data plus the standard reflection fixed
count gives the representation character component boundary. -/
theorem representationCharacterComponentsBoundary_of_complementAndReflectionFixedCount
    (data : D19ActionOrbitConcreteData h)
    (reflection_fixed_count :
      fixedVertexCount (h.smulEquiv (DihedralGroup.sr 0)) = 56) :
    D19ActsOnMoore57.RepresentationCharacterComponentsBoundary h :=
  D19ActsOnMoore57.representationCharacterComponentsBoundary_of_d19TraceInputComplementAndReflectionFixedCount
    h data.traceInput reflection_fixed_count

/-- Orbit-generated concrete action data plus the standard reflection fixed
count rules out the current branch-orbit final-gap boundary. -/
theorem no_currentFinalGapBoundary_of_complementAndReflectionFixedCount
    (data : D19ActionOrbitConcreteData h)
    (reflection_fixed_count :
      fixedVertexCount (h.smulEquiv (DihedralGroup.sr 0)) = 56) :
    ¬ Nonempty (BranchOrbitABCCurrentFinalGapBoundary h) :=
  D19ActsOnMoore57.no_currentFinalGapBoundary_of_d19TraceInputComplementAndReflectionFixedCount
    h data.traceInput reflection_fixed_count

end D19ActionOrbitConcreteData

namespace D19OrbitContributionData

variable {h : D19ActsOnMoore57 V Γ}

/-- Orbit contribution data plus the standard reflection fixed count gives a
nonempty linear-character input through the fixed-count-only complementary
minus-8 route. -/
theorem nonempty_d19LinearCharacterInput_of_complementAndReflectionFixedCount
    (data : D19OrbitContributionData h)
    (reflection_fixed_count :
      fixedVertexCount (h.smulEquiv (DihedralGroup.sr 0)) = 56) :
    Nonempty (D19ActsOnMoore57.D19LinearCharacterInput h) :=
  D19ActsOnMoore57.nonempty_d19LinearCharacterInput_of_d19TraceInputComplementAndReflectionFixedCount
    h data.traceInput reflection_fixed_count

/-- Orbit contribution data plus the standard reflection fixed count gives
fixed-star boundaries for all reflections through the fixed-count-only
complementary minus-8 route. -/
theorem involutionFixedSetStar56_of_complementAndReflectionFixedCount_raw_reflection
    (data : D19OrbitContributionData h)
    (reflection_fixed_count :
      fixedVertexCount (h.smulEquiv (DihedralGroup.sr 0)) = 56)
    (k : ZMod 19) :
    InvolutionFixedSetStar56 Γ (h.smulEquiv (DihedralGroup.sr k)) :=
  D19ActsOnMoore57.involutionFixedSetStar56_of_d19TraceInputComplementAndReflectionFixedCount_raw_reflection
    h data.traceInput reflection_fixed_count k

/-- Orbit contribution data plus the standard reflection fixed count gives
`K_{1,55}` witnesses for all reflections through the fixed-count-only
complementary minus-8 route. -/
theorem nonempty_involutionK155_of_complementAndReflectionFixedCount_raw_reflection
    (data : D19OrbitContributionData h)
    (reflection_fixed_count :
      fixedVertexCount (h.smulEquiv (DihedralGroup.sr 0)) = 56)
    (k : ZMod 19) :
    Nonempty (InvolutionK155 Γ (h.smulEquiv (DihedralGroup.sr k))) :=
  D19ActsOnMoore57.nonempty_involutionK155_of_d19TraceInputComplementAndReflectionFixedCount_raw_reflection
    h data.traceInput reflection_fixed_count k

/-- Orbit contribution data plus the standard reflection fixed count gives the
fixed-center leaf boundary through the fixed-count-only complementary minus-8
route. -/
theorem reflectionFixedCenterLeafBoundary_of_complementAndReflectionFixedCount
    (data : D19OrbitContributionData h)
    (reflection_fixed_count :
      fixedVertexCount (h.smulEquiv (DihedralGroup.sr 0)) = 56) :
    ReflectionFixedCenterLeafBoundary h :=
  D19ActsOnMoore57.reflectionFixedCenterLeafBoundary_of_d19TraceInputComplementAndReflectionFixedCount
    h data.traceInput reflection_fixed_count

/-- Orbit contribution data plus the standard reflection fixed count gives the
representation character component boundary. -/
theorem representationCharacterComponentsBoundary_of_complementAndReflectionFixedCount
    (data : D19OrbitContributionData h)
    (reflection_fixed_count :
      fixedVertexCount (h.smulEquiv (DihedralGroup.sr 0)) = 56) :
    D19ActsOnMoore57.RepresentationCharacterComponentsBoundary h :=
  D19ActsOnMoore57.representationCharacterComponentsBoundary_of_d19TraceInputComplementAndReflectionFixedCount
    h data.traceInput reflection_fixed_count

/-- Orbit contribution data plus the standard reflection fixed count rules out
the current branch-orbit final-gap boundary. -/
theorem no_currentFinalGapBoundary_of_complementAndReflectionFixedCount
    (data : D19OrbitContributionData h)
    (reflection_fixed_count :
      fixedVertexCount (h.smulEquiv (DihedralGroup.sr 0)) = 56) :
    ¬ Nonempty (BranchOrbitABCCurrentFinalGapBoundary h) :=
  D19ActsOnMoore57.no_currentFinalGapBoundary_of_d19TraceInputComplementAndReflectionFixedCount
    h data.traceInput reflection_fixed_count

end D19OrbitContributionData

namespace D19ReducedHypotheses

variable {h : D19ActsOnMoore57 V Γ}

/-- Reduced hypotheses plus the standard reflection fixed count give a
nonempty linear-character input through the fixed-count-only complementary
minus-8 route. -/
theorem nonempty_d19LinearCharacterInput_of_complementAndReflectionFixedCount
    (data : D19ReducedHypotheses h)
    (reflection_fixed_count :
      fixedVertexCount (h.smulEquiv (DihedralGroup.sr 0)) = 56) :
    Nonempty (D19ActsOnMoore57.D19LinearCharacterInput h) :=
  D19ActsOnMoore57.nonempty_d19LinearCharacterInput_of_d19TraceInputComplementAndReflectionFixedCount
    h data.characterInput.toD19TraceInput reflection_fixed_count

/-- Reduced hypotheses plus the standard reflection fixed count give fixed-star
boundaries for all reflections through the fixed-count-only complementary
minus-8 route. -/
theorem involutionFixedSetStar56_of_complementAndReflectionFixedCount_raw_reflection
    (data : D19ReducedHypotheses h)
    (reflection_fixed_count :
      fixedVertexCount (h.smulEquiv (DihedralGroup.sr 0)) = 56)
    (k : ZMod 19) :
    InvolutionFixedSetStar56 Γ (h.smulEquiv (DihedralGroup.sr k)) :=
  D19ActsOnMoore57.involutionFixedSetStar56_of_d19TraceInputComplementAndReflectionFixedCount_raw_reflection
    h data.characterInput.toD19TraceInput reflection_fixed_count k

/-- Reduced hypotheses plus the standard reflection fixed count give
`K_{1,55}` witnesses for all reflections through the fixed-count-only
complementary minus-8 route. -/
theorem nonempty_involutionK155_of_complementAndReflectionFixedCount_raw_reflection
    (data : D19ReducedHypotheses h)
    (reflection_fixed_count :
      fixedVertexCount (h.smulEquiv (DihedralGroup.sr 0)) = 56)
    (k : ZMod 19) :
    Nonempty (InvolutionK155 Γ (h.smulEquiv (DihedralGroup.sr k))) :=
  D19ActsOnMoore57.nonempty_involutionK155_of_d19TraceInputComplementAndReflectionFixedCount_raw_reflection
    h data.characterInput.toD19TraceInput reflection_fixed_count k

/-- Reduced hypotheses plus the standard reflection fixed count give the
fixed-center leaf boundary through the fixed-count-only complementary minus-8
route. -/
theorem reflectionFixedCenterLeafBoundary_of_complementAndReflectionFixedCount
    (data : D19ReducedHypotheses h)
    (reflection_fixed_count :
      fixedVertexCount (h.smulEquiv (DihedralGroup.sr 0)) = 56) :
    ReflectionFixedCenterLeafBoundary h :=
  D19ActsOnMoore57.reflectionFixedCenterLeafBoundary_of_d19TraceInputComplementAndReflectionFixedCount
    h data.characterInput.toD19TraceInput reflection_fixed_count

/-- Reduced hypotheses plus the standard reflection fixed count give the
representation character component boundary through the fixed-count-only
complementary minus-8 route. -/
theorem representationCharacterComponentsBoundary_of_complementAndReflectionFixedCount
    (data : D19ReducedHypotheses h)
    (reflection_fixed_count :
      fixedVertexCount (h.smulEquiv (DihedralGroup.sr 0)) = 56) :
    D19ActsOnMoore57.RepresentationCharacterComponentsBoundary h :=
  D19ActsOnMoore57.representationCharacterComponentsBoundary_of_d19TraceInputComplementAndReflectionFixedCount
    h data.characterInput.toD19TraceInput reflection_fixed_count

/-- Reduced hypotheses plus the standard reflection fixed count rule out the
current final-gap boundary through the fixed-count-only complementary minus-8
route. -/
theorem no_currentFinalGapBoundary_of_complementAndReflectionFixedCount
    (data : D19ReducedHypotheses h)
    (reflection_fixed_count :
      fixedVertexCount (h.smulEquiv (DihedralGroup.sr 0)) = 56) :
    ¬ Nonempty (BranchOrbitABCCurrentFinalGapBoundary h) :=
  D19ActsOnMoore57.no_currentFinalGapBoundary_of_d19TraceInputComplementAndReflectionFixedCount
    h data.characterInput.toD19TraceInput reflection_fixed_count

end D19ReducedHypotheses

namespace D19GeometricInputs

variable {h : D19ActsOnMoore57 V Γ}

/-- Geometric inputs plus the standard reflection fixed count give a nonempty
linear-character input through the fixed-count-only complementary minus-8
route. -/
theorem nonempty_d19LinearCharacterInput_of_complementAndReflectionFixedCount
    (data : D19GeometricInputs h)
    (reflection_fixed_count :
      fixedVertexCount (h.smulEquiv (DihedralGroup.sr 0)) = 56) :
    Nonempty (D19ActsOnMoore57.D19LinearCharacterInput h) :=
  D19ReducedHypotheses.nonempty_d19LinearCharacterInput_of_complementAndReflectionFixedCount
    data.toD19ReducedHypotheses reflection_fixed_count

/-- Geometric inputs plus the standard reflection fixed count give fixed-star
boundaries for all reflections through the fixed-count-only complementary
minus-8 route. -/
theorem involutionFixedSetStar56_of_complementAndReflectionFixedCount_raw_reflection
    (data : D19GeometricInputs h)
    (reflection_fixed_count :
      fixedVertexCount (h.smulEquiv (DihedralGroup.sr 0)) = 56)
    (k : ZMod 19) :
    InvolutionFixedSetStar56 Γ (h.smulEquiv (DihedralGroup.sr k)) :=
  D19ReducedHypotheses.involutionFixedSetStar56_of_complementAndReflectionFixedCount_raw_reflection
    data.toD19ReducedHypotheses reflection_fixed_count k

/-- Geometric inputs plus the standard reflection fixed count give `K_{1,55}`
witnesses for all reflections through the fixed-count-only complementary
minus-8 route. -/
theorem nonempty_involutionK155_of_complementAndReflectionFixedCount_raw_reflection
    (data : D19GeometricInputs h)
    (reflection_fixed_count :
      fixedVertexCount (h.smulEquiv (DihedralGroup.sr 0)) = 56)
    (k : ZMod 19) :
    Nonempty (InvolutionK155 Γ (h.smulEquiv (DihedralGroup.sr k))) :=
  D19ReducedHypotheses.nonempty_involutionK155_of_complementAndReflectionFixedCount_raw_reflection
    data.toD19ReducedHypotheses reflection_fixed_count k

/-- Geometric inputs plus the standard reflection fixed count give the
fixed-center leaf boundary through the fixed-count-only complementary minus-8
route. -/
theorem reflectionFixedCenterLeafBoundary_of_complementAndReflectionFixedCount
    (data : D19GeometricInputs h)
    (reflection_fixed_count :
      fixedVertexCount (h.smulEquiv (DihedralGroup.sr 0)) = 56) :
    ReflectionFixedCenterLeafBoundary h :=
  D19ReducedHypotheses.reflectionFixedCenterLeafBoundary_of_complementAndReflectionFixedCount
    data.toD19ReducedHypotheses reflection_fixed_count

/-- Geometric inputs plus the standard reflection fixed count give the
representation character component boundary through the fixed-count-only
complementary minus-8 route. -/
theorem representationCharacterComponentsBoundary_of_complementAndReflectionFixedCount
    (data : D19GeometricInputs h)
    (reflection_fixed_count :
      fixedVertexCount (h.smulEquiv (DihedralGroup.sr 0)) = 56) :
    D19ActsOnMoore57.RepresentationCharacterComponentsBoundary h :=
  D19ReducedHypotheses.representationCharacterComponentsBoundary_of_complementAndReflectionFixedCount
    data.toD19ReducedHypotheses reflection_fixed_count

/-- Geometric inputs plus the standard reflection fixed count rule out the
current final-gap boundary through the fixed-count-only complementary minus-8
route. -/
theorem no_currentFinalGapBoundary_of_complementAndReflectionFixedCount
    (data : D19GeometricInputs h)
    (reflection_fixed_count :
      fixedVertexCount (h.smulEquiv (DihedralGroup.sr 0)) = 56) :
    ¬ Nonempty (BranchOrbitABCCurrentFinalGapBoundary h) :=
  D19ReducedHypotheses.no_currentFinalGapBoundary_of_complementAndReflectionFixedCount
    data.toD19ReducedHypotheses reflection_fixed_count

end D19GeometricInputs

end

end Moore57

