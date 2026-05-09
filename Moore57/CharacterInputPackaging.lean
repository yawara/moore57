import Moore57.RotationFixedUpperBoundInputs
import Moore57.TraceCharacterInputReduction

/-!
# Split packaging for D19 character inputs

This file separates the true representation-character input from the geometric
fixed-count upper-bound input.  The two pieces can be recombined to recover the
existing `D19CharacterInput` and hence `TraceRepresentationData`.
-/

namespace Moore57

namespace D19ActsOnMoore57

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- The representation-theoretic part of the D19 character input.

This contains only the multiplicity data and the character value for
nontrivial rotations.  The fixed-vertex upper bound is supplied separately by
`RotationFixedUpperBoundInput`. -/
structure D19RepresentationCharacterInput (h : D19ActsOnMoore57 V Γ) where
  /-- Representation-theoretic multiplicities and their arithmetic constraints. -/
  multiplicity : TraceMultiplicityData
  /-- The character value for every nontrivial rotation. -/
  rotation_character :
    ∀ d : ZMod 19, d ≠ 0 →
      Matrix.trace (E7Matrix Γ * permMatrix (h.rotation d)) =
        (multiplicity.alpha : ℚ) + (multiplicity.beta : ℚ) - (multiplicity.gamma : ℚ)

namespace D19RepresentationCharacterInput

variable {h : D19ActsOnMoore57 V Γ}

/-- Combine representation-character data with the fixed-count upper-bound
input to recover the existing coarse `D19CharacterInput`. -/
def toD19CharacterInput
    (hin : D19RepresentationCharacterInput h)
    (hfixed : RotationFixedUpperBoundInput h) :
    D19CharacterInput h where
  multiplicity := hin.multiplicity
  rotation_character := hin.rotation_character
  fixed_le_nineteen := hfixed.fixed_le_nineteen

/-- Combine representation-character data with the fixed-count upper-bound
input to produce the reduced trace input. -/
def toD19TraceInput
    (hin : D19RepresentationCharacterInput h)
    (hfixed : RotationFixedUpperBoundInput h) :
    D19TraceInput h :=
  hfixed.toD19TraceInput hin.multiplicity hin.rotation_character

/-- Combine representation-character data with the fixed-count upper-bound
input and produce arithmetic trace data. -/
noncomputable def toTraceRepresentationData
    (hin : D19RepresentationCharacterInput h)
    (hfixed : RotationFixedUpperBoundInput h) :
    TraceRepresentationData h.a1 :=
  (hin.toD19TraceInput hfixed).toTraceRepresentationData

end D19RepresentationCharacterInput

namespace D19CharacterInput

variable {h : D19ActsOnMoore57 V Γ}

/-- Forget the fixed-count upper-bound input, retaining only the
representation-character part. -/
def toD19RepresentationCharacterInput
    (hin : D19CharacterInput h) :
    D19RepresentationCharacterInput h where
  multiplicity := hin.multiplicity
  rotation_character := hin.rotation_character

/-- Extract the fixed-count upper-bound part of the coarse character input. -/
def toRotationFixedUpperBoundInput
    (hin : D19CharacterInput h) :
    RotationFixedUpperBoundInput h where
  fixed_le_nineteen := hin.fixed_le_nineteen

@[simp] theorem toD19RepresentationCharacterInput_multiplicity
    (hin : D19CharacterInput h) :
    hin.toD19RepresentationCharacterInput.multiplicity = hin.multiplicity :=
  rfl

@[simp] theorem toRotationFixedUpperBoundInput_fixed_le_nineteen
    (hin : D19CharacterInput h) :
    hin.toRotationFixedUpperBoundInput.fixed_le_nineteen = hin.fixed_le_nineteen :=
  rfl

/-- Splitting and recombining a coarse character input is definitionally the
same data. -/
@[simp] theorem split_toD19CharacterInput
    (hin : D19CharacterInput h) :
    hin.toD19RepresentationCharacterInput.toD19CharacterInput
        hin.toRotationFixedUpperBoundInput = hin :=
  rfl

end D19CharacterInput

/-- Old bundled `TraceCharacterData` gives the representation-character input
when specialized to the rotation and `a1` of the `D19ActsOnMoore57` witness. -/
noncomputable def D19RepresentationCharacterInput.ofTraceCharacterData
    (h : D19ActsOnMoore57 V Γ)
    (hold : TraceCharacterData Γ h.rotation h.a1) :
    D19RepresentationCharacterInput h where
  multiplicity := hold.toTraceMultiplicityData
  rotation_character := hold.rotation_character

/-- Old bundled `TraceCharacterData` also gives the fixed-count upper-bound
input via its exact fixed-point equality. -/
noncomputable def RotationFixedUpperBoundInput.ofTraceCharacterData
    (h : D19ActsOnMoore57 V Γ)
    (hold : TraceCharacterData Γ h.rotation h.a1) :
    RotationFixedUpperBoundInput h where
  fixed_le_nineteen := by
    intro d hd
    rw [hold.rotation_fixed d hd]
    norm_num

/-- Rebuild the old coarse character input by first splitting old bundled
`TraceCharacterData` into representation-character and fixed-bound inputs. -/
noncomputable def D19CharacterInput.ofTraceCharacterData_split
    (h : D19ActsOnMoore57 V Γ)
    (hold : TraceCharacterData Γ h.rotation h.a1) :
    D19CharacterInput h :=
  (D19RepresentationCharacterInput.ofTraceCharacterData h hold).toD19CharacterInput
    (RotationFixedUpperBoundInput.ofTraceCharacterData h hold)

/-- Build arithmetic trace data from split inputs obtained from old bundled
`TraceCharacterData`. -/
noncomputable def TraceCharacterData.toTraceRepresentationData_d19Split
    (h : D19ActsOnMoore57 V Γ)
    (hold : TraceCharacterData Γ h.rotation h.a1) :
    TraceRepresentationData h.a1 :=
  (D19RepresentationCharacterInput.ofTraceCharacterData h hold).toTraceRepresentationData
    (RotationFixedUpperBoundInput.ofTraceCharacterData h hold)

end D19ActsOnMoore57

end Moore57
