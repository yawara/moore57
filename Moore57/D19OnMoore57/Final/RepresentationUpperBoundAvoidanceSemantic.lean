import Moore57.D19OnMoore57.Final.RepresentationUpperBoundAvoidanceCarrier
import Moore57.D19OnMoore57.Orbit.BaseSelectionCarrierCriteria
import Moore57.D19OnMoore57.Rotation.FixedUpperBoundFromData
import Moore57.D19OnMoore57.AdjacentMoved.ReflectionAvoidanceSplit
import Moore57.D19OnMoore57.LinearCharacter.Input

/-!
# Semantic final D19 inputs for representation upper-bound avoidance

This file adds a thin semantic boundary above
`D19FinalRepresentationUpperBoundAvoidanceCarrierInputs`.  Each major final
input is stored behind a constructor-style wrapper, and the whole package
forgets to the existing carrier boundary.
-/

namespace Moore57

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

namespace D19ActsOnMoore57

variable {h : D19ActsOnMoore57 V Γ}

/-- Semantic wrapper for the representation-character input. -/
structure D19RepresentationCharacterSemanticWitness
    (h : D19ActsOnMoore57 V Γ) where
  /-- The downstream representation-character input. -/
  input : D19RepresentationCharacterInput h

namespace D19RepresentationCharacterSemanticWitness

/-- Forget the semantic wrapper to the downstream representation input. -/
def toD19RepresentationCharacterInput
    (w : D19RepresentationCharacterSemanticWitness h) :
    D19RepresentationCharacterInput h :=
  w.input

/-- Wrap an already constructed representation-character input. -/
def ofRepresentationCharacterInput
    (input : D19RepresentationCharacterInput h) :
    D19RepresentationCharacterSemanticWitness h where
  input := input

/-- Build the semantic representation witness from a full D19 linear-character
witness. -/
def ofLinearCharacterInput
    (linearCharacter : D19LinearCharacterInput h) :
    D19RepresentationCharacterSemanticWitness h where
  input := linearCharacter.toD19RepresentationCharacterInput

/-- Build the semantic representation witness from old bundled trace-character
data. -/
noncomputable def ofTraceCharacterData
    (h : D19ActsOnMoore57 V Γ)
    (hold : TraceCharacterData Γ h.rotation h.a1) :
    D19RepresentationCharacterSemanticWitness h where
  input := D19RepresentationCharacterInput.ofTraceCharacterData h hold

end D19RepresentationCharacterSemanticWitness

/-- Semantic wrapper for the coarse fixed-upper-bound input. -/
structure RotationFixedUpperBoundSemanticWitness
    (h : D19ActsOnMoore57 V Γ) where
  /-- The downstream fixed-upper-bound input. -/
  input : RotationFixedUpperBoundInput h

namespace RotationFixedUpperBoundSemanticWitness

/-- Forget the semantic wrapper to the downstream fixed-upper-bound input. -/
def toRotationFixedUpperBoundInput
    (w : RotationFixedUpperBoundSemanticWitness h) :
    RotationFixedUpperBoundInput h :=
  w.input

/-- Wrap an already constructed fixed-upper-bound input. -/
def ofRotationFixedUpperBoundInput
    (input : RotationFixedUpperBoundInput h) :
    RotationFixedUpperBoundSemanticWitness h where
  input := input

/-- Exact fixed-point data for all nontrivial rotations gives the semantic
fixed-upper-bound witness. -/
def ofRotationFixedData
    (hfixed : RotationFixedData h.rotation) :
    RotationFixedUpperBoundSemanticWitness h where
  input := RotationFixedUpperBoundInput.of_rotationFixedData hfixed

/-- Exact fixed count `1` for every nontrivial rotation gives the semantic
fixed-upper-bound witness. -/
def ofAllFixedVertexCountEqOne
    (hcount :
      ∀ d : ZMod 19, d ≠ 0 → fixedVertexCount (h.rotation d) = 1) :
    RotationFixedUpperBoundSemanticWitness h where
  input := RotationFixedUpperBoundInput.of_all_fixedVertexCount_eq_one hcount

/-- A rotation-one fixed-count bound gives the semantic fixed-upper-bound
witness. -/
def ofRotationOneFixedVertexCountLeNineteen
    (hcount : fixedVertexCount (h.rotation 1) ≤ 19) :
    RotationFixedUpperBoundSemanticWitness h where
  input := RotationFixedUpperBoundInput.of_rotation_one_le_nineteen hcount

/-- An exact rotation-one fixed count gives the semantic fixed-upper-bound
witness. -/
noncomputable def ofRotationOneFixedVertexCountEqOne
    (hcount : fixedVertexCount (h.rotation 1) = 1) :
    RotationFixedUpperBoundSemanticWitness h where
  input := RotationFixedUpperBoundInput.of_rotation_one_fixedVertexCount_eq_one'
    hcount

/-- A unique fixed point for rotation by one gives the semantic
fixed-upper-bound witness. -/
def ofExistsUniqueFixedRotationOne
    (hunique : ∃! v : V, h.rotation 1 v = v) :
    RotationFixedUpperBoundSemanticWitness h where
  input := RotationFixedUpperBoundInput.of_existsUnique_fixed_rotation_one
    hunique

end RotationFixedUpperBoundSemanticWitness

end D19ActsOnMoore57

/-- Semantic wrapper for the selected orbit bases, using the bounded carrier
criterion as the constructor-style source. -/
structure OrbitBaseSelectionCarrierSemanticWitness
    (h : D19ActsOnMoore57 V Γ) where
  /-- Bounded carrier witness for the selected moved rotation orbits. -/
  carrier : OrbitBaseSelectionCarrierWitness h

namespace OrbitBaseSelectionCarrierSemanticWitness

variable {h : D19ActsOnMoore57 V Γ}

/-- Forget the semantic wrapper to the carrier witness. -/
def toCarrierWitness
    (w : OrbitBaseSelectionCarrierSemanticWitness h) :
    OrbitBaseSelectionCarrierWitness h :=
  w.carrier

/-- Convert the semantic wrapper to the coordinate-injective witness. -/
noncomputable def toWitness
    (w : OrbitBaseSelectionCarrierSemanticWitness h) :
    OrbitBaseSelectionWitness h :=
  w.toCarrierWitness.toWitness

/-- Convert the semantic wrapper to the downstream orbit-base input. -/
noncomputable def toInput
    (w : OrbitBaseSelectionCarrierSemanticWitness h) :
    OrbitBaseSelectionInput h :=
  w.toCarrierWitness.toInput

/-- Wrap a bounded carrier witness as the semantic orbit-base witness. -/
def ofCarrierWitness
    (carrier : OrbitBaseSelectionCarrierWitness h) :
    OrbitBaseSelectionCarrierSemanticWitness h where
  carrier := carrier

end OrbitBaseSelectionCarrierSemanticWitness

/-- Semantic wrapper for split reflected-base avoidance over semantic orbit
bases. -/
structure AdjacentMovedReflectionAvoidanceSemanticWitness
    (h : D19ActsOnMoore57 V Γ)
    (orbitBase : OrbitBaseSelectionCarrierSemanticWitness h) where
  /-- Split avoidance witness over the downstream input of the semantic bases. -/
  split :
    AdjacentMovedReflectionAvoidanceSplit38Witness h orbitBase.toInput

namespace AdjacentMovedReflectionAvoidanceSemanticWitness

variable {h : D19ActsOnMoore57 V Γ}
variable {orbitBase : OrbitBaseSelectionCarrierSemanticWitness h}

/-- Forget the semantic wrapper to the split avoidance witness. -/
noncomputable def toSplitAvoidance
    (w : AdjacentMovedReflectionAvoidanceSemanticWitness h orbitBase) :
    AdjacentMovedReflectionAvoidanceSplit38Witness h orbitBase.toInput :=
  w.split

/-- Convert to the compact avoidance witness. -/
noncomputable def toAvoidanceComplementResidual38Witness
    (w : AdjacentMovedReflectionAvoidanceSemanticWitness h orbitBase) :
    AdjacentMovedReflectionAvoidanceComplementResidual38Witness
      h orbitBase.toInput :=
  w.toSplitAvoidance.toAvoidanceComplementResidual38Witness

/-- Wrap an already constructed split avoidance witness. -/
noncomputable def ofSplitAvoidance
    (split : AdjacentMovedReflectionAvoidanceSplit38Witness h orbitBase.toInput) :
    AdjacentMovedReflectionAvoidanceSemanticWitness h orbitBase where
  split := split

end AdjacentMovedReflectionAvoidanceSemanticWitness

/-- Final D19 input package whose major fields are semantic constructor-style
wrappers, with orbit bases still normalized through the carrier criterion. -/
structure D19FinalRepresentationUpperBoundAvoidanceSemanticInputs
    (h : D19ActsOnMoore57 V Γ) where
  /-- Semantic representation-character witness. -/
  representation :
    D19ActsOnMoore57.D19RepresentationCharacterSemanticWitness h
  /-- Semantic fixed-upper-bound witness. -/
  fixedUpperBound :
    D19ActsOnMoore57.RotationFixedUpperBoundSemanticWitness h
  /-- Semantic carrier witness for the selected moved rotation orbits. -/
  orbitBase : OrbitBaseSelectionCarrierSemanticWitness h
  /-- Semantic split avoidance witness over the semantic orbit bases. -/
  adjacentMoved :
    AdjacentMovedReflectionAvoidanceSemanticWitness h orbitBase

namespace D19FinalRepresentationUpperBoundAvoidanceSemanticInputs

variable {h : D19ActsOnMoore57 V Γ}

/-- Convert the semantic final boundary to the carrier final boundary. -/
noncomputable def toD19FinalRepresentationUpperBoundAvoidanceCarrierInputs
    (data : D19FinalRepresentationUpperBoundAvoidanceSemanticInputs h) :
    D19FinalRepresentationUpperBoundAvoidanceCarrierInputs h where
  representation :=
    data.representation.toD19RepresentationCharacterInput
  fixedUpperBound :=
    data.fixedUpperBound.toRotationFixedUpperBoundInput
  orbitBase :=
    data.orbitBase.toCarrierWitness
  adjacentMoved := by
    simpa [OrbitBaseSelectionCarrierSemanticWitness.toInput,
      OrbitBaseSelectionCarrierSemanticWitness.toCarrierWitness,
      AdjacentMovedReflectionAvoidanceSemanticWitness.toSplitAvoidance] using
      data.adjacentMoved.toSplitAvoidance

/-- Convert the semantic final boundary to the split avoidance final boundary.
-/
noncomputable def toD19FinalRepresentationUpperBoundAvoidanceSplitInputs
    (data : D19FinalRepresentationUpperBoundAvoidanceSemanticInputs h) :
    D19FinalRepresentationUpperBoundAvoidanceSplitInputs h :=
  data.toD19FinalRepresentationUpperBoundAvoidanceCarrierInputs
    |>.toD19FinalRepresentationUpperBoundAvoidanceSplitInputs

/-- Convert the semantic final boundary to the avoidance final boundary. -/
noncomputable def toD19FinalRepresentationUpperBoundAvoidanceInputs
    (data : D19FinalRepresentationUpperBoundAvoidanceSemanticInputs h) :
    D19FinalRepresentationUpperBoundAvoidanceInputs h :=
  data.toD19FinalRepresentationUpperBoundAvoidanceCarrierInputs
    |>.toD19FinalRepresentationUpperBoundAvoidanceInputs

/-- Forget the semantic final boundary down to the final input record. -/
noncomputable def toD19FinalInputs
    (data : D19FinalRepresentationUpperBoundAvoidanceSemanticInputs h) :
    D19FinalInputs h :=
  data.toD19FinalRepresentationUpperBoundAvoidanceCarrierInputs
    |>.toD19FinalInputs

/-- Semantic final representation, fixed-upper-bound, carrier-base, and split
avoidance inputs cannot exist. -/
theorem not_nonempty (h : D19ActsOnMoore57 V Γ) :
    ¬ Nonempty (D19FinalRepresentationUpperBoundAvoidanceSemanticInputs h) := by
  rintro ⟨data⟩
  exact D19FinalRepresentationUpperBoundAvoidanceCarrierInputs.not_nonempty h
    ⟨data.toD19FinalRepresentationUpperBoundAvoidanceCarrierInputs⟩

end D19FinalRepresentationUpperBoundAvoidanceSemanticInputs

end Moore57
