import Moore57.D19RepresentationCharacterFromData
import Moore57.TraceCoreCharacterBoundary
import Moore57.RotationOneFixedBoundBoundary

/-!
# Direct bridge from trace-core boundary data to representation inputs

This file keeps final-boundary APIs from reintroducing
`TraceCharacterCoreData` when all they need is the direct bridge between
`TraceCoreCharacterBoundary` and `D19RepresentationCharacterInput`.
-/

namespace Moore57

namespace D19ActsOnMoore57

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

namespace TraceCoreCharacterBoundary

variable {h : D19ActsOnMoore57 V Γ}

/-- Forget the trace-core boundary presentation directly to the
representation-character input. -/
def toD19RepresentationCharacterInput
    (data : TraceCoreCharacterBoundary h) :
    D19RepresentationCharacterInput h where
  multiplicity := data.multiplicity
  rotation_character := data.rotation_character

/-- Repackage a representation-character input as the trace-core boundary
presentation. -/
def ofD19RepresentationCharacterInput
    (input : D19RepresentationCharacterInput h) :
    TraceCoreCharacterBoundary h where
  multiplicity := input.multiplicity
  rotation_character := input.rotation_character

@[simp] theorem toD19RepresentationCharacterInput_multiplicity
    (data : TraceCoreCharacterBoundary h) :
    data.toD19RepresentationCharacterInput.multiplicity = data.multiplicity :=
  rfl

@[simp] theorem toD19RepresentationCharacterInput_rotation_character
    (data : TraceCoreCharacterBoundary h) :
    data.toD19RepresentationCharacterInput.rotation_character =
      data.rotation_character :=
  rfl

@[simp] theorem ofD19RepresentationCharacterInput_multiplicity
    (input : D19RepresentationCharacterInput h) :
    (ofD19RepresentationCharacterInput input).multiplicity =
      input.multiplicity :=
  rfl

@[simp] theorem ofD19RepresentationCharacterInput_rotation_character
    (input : D19RepresentationCharacterInput h) :
    (ofD19RepresentationCharacterInput input).rotation_character =
      input.rotation_character :=
  rfl

@[simp] theorem ofD19RepresentationCharacterInput_toD19RepresentationCharacterInput
    (data : TraceCoreCharacterBoundary h) :
    ofD19RepresentationCharacterInput data.toD19RepresentationCharacterInput =
      data := by
  cases data
  rfl

@[simp] theorem toD19RepresentationCharacterInput_ofD19RepresentationCharacterInput
    (input : D19RepresentationCharacterInput h) :
    toD19RepresentationCharacterInput
        (ofD19RepresentationCharacterInput input) =
      input := by
  cases input
  rfl

/-- The direct bridge agrees with the older trace-core-data bridge. -/
theorem toD19RepresentationCharacterInput_eq_ofTraceCharacterCoreData
    (data : TraceCoreCharacterBoundary h) :
    data.toD19RepresentationCharacterInput =
      D19RepresentationCharacterInput.ofTraceCharacterCoreData
        data.toTraceCharacterCoreData :=
  rfl

/-- Repackaging agrees with the older trace-core-data bridge. -/
theorem ofD19RepresentationCharacterInput_eq_ofTraceCharacterCoreData
    (input : D19RepresentationCharacterInput h) :
    ofD19RepresentationCharacterInput input =
      ofTraceCharacterCoreData input.toTraceCharacterCoreData :=
  rfl

/-- The trace-core boundary record is equivalent to the representation-character
input once the ambient D19 action supplies the `a1` compatibility. -/
def equivD19RepresentationCharacterInput
    (h : D19ActsOnMoore57 V Γ) :
    TraceCoreCharacterBoundary h ≃ D19RepresentationCharacterInput h where
  toFun := toD19RepresentationCharacterInput
  invFun := ofD19RepresentationCharacterInput
  left_inv := by
    intro data
    exact ofD19RepresentationCharacterInput_toD19RepresentationCharacterInput data
  right_inv := by
    intro input
    exact toD19RepresentationCharacterInput_ofD19RepresentationCharacterInput input

/-- Nonemptiness form of `equivD19RepresentationCharacterInput`. -/
theorem nonempty_iff_d19RepresentationCharacterInput
    (h : D19ActsOnMoore57 V Γ) :
    Nonempty (TraceCoreCharacterBoundary h) ↔
      Nonempty (D19RepresentationCharacterInput h) := by
  constructor
  · rintro ⟨data⟩
    exact ⟨data.toD19RepresentationCharacterInput⟩
  · rintro ⟨input⟩
    exact ⟨ofD19RepresentationCharacterInput input⟩

/-- Combine trace-core representation data with the packaged rotation-one
fixed bound to produce the current final character input boundary. -/
def toD19FinalCharacterInputs
    (data : TraceCoreCharacterBoundary h)
    (fixedBound : RotationOneFixedBoundBoundaryInput h) :
    D19FinalCharacterInputs h where
  representation := data.toD19RepresentationCharacterInput
  fixedUpperBound := fixedBound.toRotationFixedUpperBoundInput

@[simp] theorem toD19FinalCharacterInputs_representation
    (data : TraceCoreCharacterBoundary h)
    (fixedBound : RotationOneFixedBoundBoundaryInput h) :
    (data.toD19FinalCharacterInputs fixedBound).representation =
      data.toD19RepresentationCharacterInput :=
  rfl

@[simp] theorem toD19FinalCharacterInputs_fixedUpperBound
    (data : TraceCoreCharacterBoundary h)
    (fixedBound : RotationOneFixedBoundBoundaryInput h) :
    (data.toD19FinalCharacterInputs fixedBound).fixedUpperBound =
      fixedBound.toRotationFixedUpperBoundInput :=
  rfl

end TraceCoreCharacterBoundary

end D19ActsOnMoore57

end Moore57
