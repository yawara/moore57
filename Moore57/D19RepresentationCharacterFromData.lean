import Moore57.D19FinalInputs
import Moore57.D19LinearCharacterInput

/-!
# D19 representation-character inputs from lower-level trace data

This file records small bridges that let downstream final boundaries consume
existing trace/multiplicity/linear-character packages directly, then forget
them to `D19RepresentationCharacterInput` only at the last step.
-/

namespace Moore57

namespace D19ActsOnMoore57

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

namespace D19RepresentationCharacterInput

variable {h : D19ActsOnMoore57 V Γ}

/-- Build representation-character input from split trace core data specialized
to the rotation action of `h`.  The extra `rotation_a1` field in the core data
is intentionally ignored here; it is supplied by `h` when going the other way. -/
def ofTraceCharacterCoreData
    (core : TraceCharacterCoreData Γ h.rotation h.a1) :
    D19RepresentationCharacterInput h where
  multiplicity := core.toTraceMultiplicityData
  rotation_character := core.rotation_character

/-- Forget representation-character input to split trace core data.  The
`a1` compatibility field is recovered from the ambient `D19ActsOnMoore57`
witness. -/
def toTraceCharacterCoreData
    (hin : D19RepresentationCharacterInput h) :
    TraceCharacterCoreData Γ h.rotation h.a1 where
  toTraceMultiplicityData := hin.multiplicity
  rotation_a1 := h.rotation_a1_def_of_ne_zero
  rotation_character := hin.rotation_character

@[simp] theorem ofTraceCharacterCoreData_multiplicity
    (core : TraceCharacterCoreData Γ h.rotation h.a1) :
    (ofTraceCharacterCoreData core).multiplicity = core.toTraceMultiplicityData :=
  rfl

@[simp] theorem ofTraceCharacterCoreData_rotation_character
    (core : TraceCharacterCoreData Γ h.rotation h.a1) :
    (ofTraceCharacterCoreData core).rotation_character = core.rotation_character :=
  rfl

@[simp] theorem toTraceCharacterCoreData_toTraceMultiplicityData
    (hin : D19RepresentationCharacterInput h) :
    hin.toTraceCharacterCoreData.toTraceMultiplicityData = hin.multiplicity :=
  rfl

@[simp] theorem toTraceCharacterCoreData_rotation_character
    (hin : D19RepresentationCharacterInput h) :
    hin.toTraceCharacterCoreData.rotation_character = hin.rotation_character :=
  rfl

@[simp] theorem of_toTraceCharacterCoreData
    (hin : D19RepresentationCharacterInput h) :
    ofTraceCharacterCoreData hin.toTraceCharacterCoreData = hin :=
  rfl

@[simp] theorem toTraceCharacterCoreData_ofTraceCharacterCoreData
    (core : TraceCharacterCoreData Γ h.rotation h.a1) :
    (ofTraceCharacterCoreData core).toTraceCharacterCoreData = core := by
  cases core
  rfl

/-- Split trace core data is equivalent to the representation-character input
once the ambient D19 action supplies the canonical `a1` compatibility. -/
def traceCharacterCoreDataEquiv
    (h : D19ActsOnMoore57 V Γ) :
    TraceCharacterCoreData Γ h.rotation h.a1 ≃ D19RepresentationCharacterInput h where
  toFun := ofTraceCharacterCoreData
  invFun := toTraceCharacterCoreData
  left_inv := by
    intro core
    exact toTraceCharacterCoreData_ofTraceCharacterCoreData core
  right_inv := by
    intro hin
    exact of_toTraceCharacterCoreData hin

/-- Existence of split trace core data is exactly existence of the
representation-character input at the final boundary. -/
theorem exists_traceCharacterCoreData_iff
    (h : D19ActsOnMoore57 V Γ) :
    (∃ _ : TraceCharacterCoreData Γ h.rotation h.a1, True) ↔
      Nonempty (D19RepresentationCharacterInput h) := by
  constructor
  · rintro ⟨core, _⟩
    exact ⟨ofTraceCharacterCoreData core⟩
  · rintro ⟨hin⟩
    exact ⟨hin.toTraceCharacterCoreData, trivial⟩

/-- Nonemptiness of split trace core data is exactly nonemptiness of the
representation-character input at the final boundary. -/
theorem nonempty_traceCharacterCoreData_iff
    (h : D19ActsOnMoore57 V Γ) :
    Nonempty (TraceCharacterCoreData Γ h.rotation h.a1) ↔
      Nonempty (D19RepresentationCharacterInput h) := by
  constructor
  · rintro ⟨core⟩
    exact ⟨ofTraceCharacterCoreData core⟩
  · rintro ⟨hin⟩
    exact ⟨hin.toTraceCharacterCoreData⟩

/-- A reduced trace input contains the representation-character data plus fixed
data; this constructor keeps only the representation part. -/
def ofD19TraceInput
    (hin : D19TraceInput h) :
    D19RepresentationCharacterInput h where
  multiplicity := hin.multiplicity
  rotation_character := hin.rotation_character

@[simp] theorem ofD19TraceInput_multiplicity
    (hin : D19TraceInput h) :
    (ofD19TraceInput hin).multiplicity = hin.multiplicity :=
  rfl

@[simp] theorem ofD19TraceInput_rotation_character
    (hin : D19TraceInput h) :
    (ofD19TraceInput hin).rotation_character = hin.rotation_character :=
  rfl

/-- A coarse D19 character input contains exactly the representation-character
data plus the fixed-count upper bound; this constructor keeps only the
representation part. -/
def ofD19CharacterInput
    (hin : D19CharacterInput h) :
    D19RepresentationCharacterInput h :=
  hin.toD19RepresentationCharacterInput

@[simp] theorem ofD19CharacterInput_eq_toD19RepresentationCharacterInput
    (hin : D19CharacterInput h) :
    ofD19CharacterInput hin = hin.toD19RepresentationCharacterInput :=
  rfl

/-- A full D19 linear-character equality restricts to the nontrivial-rotation
character input used by the final boundary. -/
def ofD19LinearCharacterInput
    (hin : D19LinearCharacterInput h) :
    D19RepresentationCharacterInput h :=
  hin.toD19RepresentationCharacterInput

@[simp] theorem ofD19LinearCharacterInput_eq_toD19RepresentationCharacterInput
    (hin : D19LinearCharacterInput h) :
    ofD19LinearCharacterInput hin = hin.toD19RepresentationCharacterInput :=
  rfl

@[simp] theorem ofTraceCharacterData_eq_ofTraceCharacterCoreData
    (h : D19ActsOnMoore57 V Γ)
    (hold : TraceCharacterData Γ h.rotation h.a1) :
    D19RepresentationCharacterInput.ofTraceCharacterData h hold =
      ofTraceCharacterCoreData hold.toTraceCharacterCoreData :=
  rfl

end D19RepresentationCharacterInput

end D19ActsOnMoore57

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- Final character inputs whose representation side is supplied as split trace
core data instead of the already-forgotten `D19RepresentationCharacterInput`.

This is the wrapper intended for future final boundaries that want to ask for
trace/multiplicity data directly and only lower it at the conversion point to
`D19FinalCharacterInputs`. -/
structure D19FinalCharacterFromTraceCoreInputs
    (h : D19ActsOnMoore57 V Γ) where
  /-- Split trace/multiplicity data for the representation-character side. -/
  traceCore : TraceCharacterCoreData Γ h.rotation h.a1
  /-- Coarse upper bound for nontrivial rotation fixed vertices. -/
  fixedUpperBound : D19ActsOnMoore57.RotationFixedUpperBoundInput h

namespace D19FinalCharacterFromTraceCoreInputs

variable {h : D19ActsOnMoore57 V Γ}

/-- Lower the trace-core final character wrapper to the current split final
character input boundary. -/
def toD19FinalCharacterInputs
    (data : D19FinalCharacterFromTraceCoreInputs h) :
    D19FinalCharacterInputs h where
  representation :=
    D19ActsOnMoore57.D19RepresentationCharacterInput.ofTraceCharacterCoreData
      data.traceCore
  fixedUpperBound := data.fixedUpperBound

@[simp] theorem toD19FinalCharacterInputs_representation
    (data : D19FinalCharacterFromTraceCoreInputs h) :
    data.toD19FinalCharacterInputs.representation =
      D19ActsOnMoore57.D19RepresentationCharacterInput.ofTraceCharacterCoreData
        data.traceCore :=
  rfl

@[simp] theorem toD19FinalCharacterInputs_fixedUpperBound
    (data : D19FinalCharacterFromTraceCoreInputs h) :
    data.toD19FinalCharacterInputs.fixedUpperBound = data.fixedUpperBound :=
  rfl

/-- Repackage the existing final character boundary as trace core data. -/
def ofD19FinalCharacterInputs
    (data : D19FinalCharacterInputs h) :
    D19FinalCharacterFromTraceCoreInputs h where
  traceCore := data.representation.toTraceCharacterCoreData
  fixedUpperBound := data.fixedUpperBound

@[simp] theorem toD19FinalCharacterInputs_ofD19FinalCharacterInputs
    (data : D19FinalCharacterInputs h) :
    (ofD19FinalCharacterInputs data).toD19FinalCharacterInputs = data := by
  cases data
  rfl

@[simp] theorem ofD19FinalCharacterInputs_toD19FinalCharacterInputs
    (data : D19FinalCharacterFromTraceCoreInputs h) :
    ofD19FinalCharacterInputs data.toD19FinalCharacterInputs = data := by
  cases data
  simp only [ofD19FinalCharacterInputs, toD19FinalCharacterInputs]
  rw [D19ActsOnMoore57.D19RepresentationCharacterInput.toTraceCharacterCoreData_ofTraceCharacterCoreData]

/-- The trace-core final character wrapper is equivalent to the current final
character input record. -/
def equivD19FinalCharacterInputs
    (h : D19ActsOnMoore57 V Γ) :
    D19FinalCharacterFromTraceCoreInputs h ≃ D19FinalCharacterInputs h where
  toFun := toD19FinalCharacterInputs
  invFun := ofD19FinalCharacterInputs
  left_inv := by
    intro data
    exact ofD19FinalCharacterInputs_toD19FinalCharacterInputs data
  right_inv := by
    intro data
    exact toD19FinalCharacterInputs_ofD19FinalCharacterInputs data

/-- Nonemptiness can be transported between the trace-core wrapper and the
current final character input boundary. -/
theorem nonempty_iff_d19FinalCharacterInputs
    (h : D19ActsOnMoore57 V Γ) :
    Nonempty (D19FinalCharacterFromTraceCoreInputs h) ↔
      Nonempty (D19FinalCharacterInputs h) := by
  constructor
  · rintro ⟨data⟩
    exact ⟨data.toD19FinalCharacterInputs⟩
  · rintro ⟨data⟩
    exact ⟨ofD19FinalCharacterInputs data⟩

end D19FinalCharacterFromTraceCoreInputs

end Moore57
