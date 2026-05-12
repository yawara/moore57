import Moore57.D19OnMoore57.E7Projection.Minus8D19CharacterInputComplementNoGoConnectors
import Moore57.D19OnMoore57.Trace.CoreRepresentationBoundary
import Moore57.D19OnMoore57.Rotation.FixedCountOneFrontier

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
