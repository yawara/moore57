import Moore57.E7Minus8D19TraceInputComplementFixedCount
import Moore57.E7Minus8D19FinalCharacterInputComplementBoundary
import Moore57.E7Minus8RepresentationInputComplementAutoFixed

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
