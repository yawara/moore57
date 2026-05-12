import Moore57.D19OnMoore57.AdjacentMoved.ReflectionAvoidanceCriteria
import Moore57.D19OnMoore57.AdjacentMoved.ReflectionAvoidanceSplit
import Moore57.D19OnMoore57.AdjacentMoved.ReflectionCompactCriteria
import Moore57.D19OnMoore57.AdjacentMoved.ReflectionCompactSplit
import Moore57.D19OnMoore57.Final.Inputs
import Moore57.D19OnMoore57.LinearCharacter.Input
import Moore57.D19OnMoore57.Misc.CharacterInputPackaging
import Moore57.D19OnMoore57.Orbit.BaseSelectionCarrierCriteria
import Moore57.D19OnMoore57.Orbit.BaseSelectionEnumeration
import Moore57.D19OnMoore57.Orbit.BaseSelectionInputBridge
import Moore57.D19OnMoore57.Rotation.FixedUpperBoundFromData

/-!
# Final D19 inputs from representation data and compact adjacent-moved data

This file removes the exact fixed-count field from the current compact final
boundary: the fixed side is supplied by the coarse `RotationFixedUpperBoundInput`,
which already implies exact fixed count `1` for nontrivial rotations.
-/

namespace Moore57

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- Final D19 input package using representation-character data, the coarse
fixed-count upper bound, downstream base-selection input, and the compact
adjacent-moved complement-residual criterion. -/
structure D19FinalRepresentationUpperBoundCompactInputs
    (h : D19ActsOnMoore57 V Γ) where
  /-- Representation-theoretic multiplicities and nontrivial rotation
  character values. -/
  representation : D19ActsOnMoore57.D19RepresentationCharacterInput h
  /-- Coarse upper bound for nontrivial rotation fixed vertices. -/
  fixedUpperBound : D19ActsOnMoore57.RotationFixedUpperBoundInput h
  /-- Pairwise-disjoint selected moved rotation orbits. -/
  orbitBase : OrbitBaseSelectionInput h
  /-- Compact adjacent-moved complement-residual witness over the selected
  bases. -/
  adjacentMoved :
    AdjacentMovedReflectionComplementResidual38Witness h orbitBase

namespace D19FinalRepresentationUpperBoundCompactInputs

variable {h : D19ActsOnMoore57 V Γ}

/-- Convert to the split final character input. -/
def toD19FinalCharacterInputs
    (data : D19FinalRepresentationUpperBoundCompactInputs h) :
    D19FinalCharacterInputs h where
  representation := data.representation
  fixedUpperBound := data.fixedUpperBound

/-- Forget the compact presentation down to the final input record. -/
noncomputable def toD19FinalInputs
    (data : D19FinalRepresentationUpperBoundCompactInputs h) :
    D19FinalInputs h where
  character := data.toD19FinalCharacterInputs
  orbitBase := data.orbitBase.toWitness
  fixedOrAContribution := fixedOrAContribution38
  fixed_or_A_contribution := by
    intro d hd
    rfl
  adjacentMovedDecomposition := by
    simpa [OrbitBaseSelectionInput.toWitness] using
      data.adjacentMoved.toDecomposition

/-- The upper-bound input gives the exact fixed count used by older final
boundaries. -/
theorem rotation_one_fixed_count_eq_one
    (data : D19FinalRepresentationUpperBoundCompactInputs h) :
    fixedVertexCount (h.rotation 1) = 1 :=
  data.fixedUpperBound.rotation_one_fixed_count_eq_one

/-- Final representation-character, fixed-upper-bound, compact adjacent-moved
inputs cannot exist. -/
theorem not_nonempty (h : D19ActsOnMoore57 V Γ) :
    ¬ Nonempty (D19FinalRepresentationUpperBoundCompactInputs h) := by
  rintro ⟨data⟩
  exact D19FinalInputs.not_nonempty h ⟨data.toD19FinalInputs⟩

end D19FinalRepresentationUpperBoundCompactInputs

end Moore57

/-!
# Final D19 inputs from split compact adjacent-moved data

This file combines the fixed-upper-bound final boundary with the split version
of the compact complement-residual adjacent-moved witness.
-/

namespace Moore57

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- Final D19 input package using representation-character data, the coarse
fixed-count upper bound, downstream base-selection input, and a split compact
complement-residual adjacent-moved witness. -/
structure D19FinalRepresentationUpperBoundCompactSplitInputs
    (h : D19ActsOnMoore57 V Γ) where
  /-- Representation-theoretic multiplicities and nontrivial rotation
  character values. -/
  representation : D19ActsOnMoore57.D19RepresentationCharacterInput h
  /-- Coarse upper bound for nontrivial rotation fixed vertices. -/
  fixedUpperBound : D19ActsOnMoore57.RotationFixedUpperBoundInput h
  /-- Pairwise-disjoint selected moved rotation orbits. -/
  orbitBase : OrbitBaseSelectionInput h
  /-- Split compact adjacent-moved complement-residual witness over the
  selected bases. -/
  adjacentMoved :
    AdjacentMovedReflectionComplementResidualSplit38Witness h orbitBase

namespace D19FinalRepresentationUpperBoundCompactSplitInputs

variable {h : D19ActsOnMoore57 V Γ}

/-- Forget the split residual presentation to the compact final boundary. -/
noncomputable def toD19FinalRepresentationUpperBoundCompactInputs
    (data : D19FinalRepresentationUpperBoundCompactSplitInputs h) :
    D19FinalRepresentationUpperBoundCompactInputs h where
  representation := data.representation
  fixedUpperBound := data.fixedUpperBound
  orbitBase := data.orbitBase
  adjacentMoved := data.adjacentMoved.toComplementResidual38Witness

/-- Forget the split compact presentation down to the final input record. -/
noncomputable def toD19FinalInputs
    (data : D19FinalRepresentationUpperBoundCompactSplitInputs h) :
    D19FinalInputs h :=
  data.toD19FinalRepresentationUpperBoundCompactInputs.toD19FinalInputs

/-- Final representation-character, fixed-upper-bound, split compact
adjacent-moved inputs cannot exist. -/
theorem not_nonempty (h : D19ActsOnMoore57 V Γ) :
    ¬ Nonempty (D19FinalRepresentationUpperBoundCompactSplitInputs h) := by
  rintro ⟨data⟩
  exact D19FinalRepresentationUpperBoundCompactInputs.not_nonempty h
    ⟨data.toD19FinalRepresentationUpperBoundCompactInputs⟩

end D19FinalRepresentationUpperBoundCompactSplitInputs

end Moore57

/-!
# Final D19 inputs from reflection avoidance

This file states the current compact final boundary with the mixed
original/reflected disjointness reduced to reflected-base avoidance of the
selected orbit family.
-/

namespace Moore57

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- Final D19 input package using representation-character data, the coarse
fixed-count upper bound, downstream base-selection input, and an avoidance
criterion for the compact adjacent-moved witness. -/
structure D19FinalRepresentationUpperBoundAvoidanceInputs
    (h : D19ActsOnMoore57 V Γ) where
  /-- Representation-theoretic multiplicities and nontrivial rotation
  character values. -/
  representation : D19ActsOnMoore57.D19RepresentationCharacterInput h
  /-- Coarse upper bound for nontrivial rotation fixed vertices. -/
  fixedUpperBound : D19ActsOnMoore57.RotationFixedUpperBoundInput h
  /-- Pairwise-disjoint selected moved rotation orbits. -/
  orbitBase : OrbitBaseSelectionInput h
  /-- Avoidance-based compact adjacent-moved witness over the selected bases. -/
  adjacentMoved :
    AdjacentMovedReflectionAvoidanceComplementResidual38Witness h orbitBase

namespace D19FinalRepresentationUpperBoundAvoidanceInputs

variable {h : D19ActsOnMoore57 V Γ}

/-- Convert the avoidance criterion to the compact final boundary. -/
noncomputable def toD19FinalRepresentationUpperBoundCompactInputs
    (data : D19FinalRepresentationUpperBoundAvoidanceInputs h) :
    D19FinalRepresentationUpperBoundCompactInputs h where
  representation := data.representation
  fixedUpperBound := data.fixedUpperBound
  orbitBase := data.orbitBase
  adjacentMoved := data.adjacentMoved.toComplementResidual38Witness

/-- Forget the avoidance presentation down to the final input record. -/
noncomputable def toD19FinalInputs
    (data : D19FinalRepresentationUpperBoundAvoidanceInputs h) :
    D19FinalInputs h :=
  data.toD19FinalRepresentationUpperBoundCompactInputs.toD19FinalInputs

/-- Final representation-character, fixed-upper-bound, avoidance-based
adjacent-moved inputs cannot exist. -/
theorem not_nonempty (h : D19ActsOnMoore57 V Γ) :
    ¬ Nonempty (D19FinalRepresentationUpperBoundAvoidanceInputs h) := by
  rintro ⟨data⟩
  exact D19FinalRepresentationUpperBoundCompactInputs.not_nonempty h
    ⟨data.toD19FinalRepresentationUpperBoundCompactInputs⟩

end D19FinalRepresentationUpperBoundAvoidanceInputs

end Moore57

/-!
# Final D19 inputs from split reflection avoidance

This file states the current final boundary with fixed upper bound,
reflected-base avoidance, and a split presentation of the canonical complement
residual.
-/

namespace Moore57

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- Final D19 input package using representation-character data, the coarse
fixed-count upper bound, downstream base-selection input, and a split
avoidance-based adjacent-moved witness. -/
structure D19FinalRepresentationUpperBoundAvoidanceSplitInputs
    (h : D19ActsOnMoore57 V Γ) where
  /-- Representation-theoretic multiplicities and nontrivial rotation
  character values. -/
  representation : D19ActsOnMoore57.D19RepresentationCharacterInput h
  /-- Coarse upper bound for nontrivial rotation fixed vertices. -/
  fixedUpperBound : D19ActsOnMoore57.RotationFixedUpperBoundInput h
  /-- Pairwise-disjoint selected moved rotation orbits. -/
  orbitBase : OrbitBaseSelectionInput h
  /-- Split avoidance-based adjacent-moved witness over the selected bases. -/
  adjacentMoved :
    AdjacentMovedReflectionAvoidanceSplit38Witness h orbitBase

namespace D19FinalRepresentationUpperBoundAvoidanceSplitInputs

variable {h : D19ActsOnMoore57 V Γ}

/-- Forget the split residual presentation to the avoidance final boundary. -/
noncomputable def toD19FinalRepresentationUpperBoundAvoidanceInputs
    (data : D19FinalRepresentationUpperBoundAvoidanceSplitInputs h) :
    D19FinalRepresentationUpperBoundAvoidanceInputs h where
  representation := data.representation
  fixedUpperBound := data.fixedUpperBound
  orbitBase := data.orbitBase
  adjacentMoved := data.adjacentMoved.toAvoidanceComplementResidual38Witness

/-- Forget the split avoidance presentation down to the final input record. -/
noncomputable def toD19FinalInputs
    (data : D19FinalRepresentationUpperBoundAvoidanceSplitInputs h) :
    D19FinalInputs h :=
  data.toD19FinalRepresentationUpperBoundAvoidanceInputs.toD19FinalInputs

/-- Final representation-character, fixed-upper-bound, split avoidance
adjacent-moved inputs cannot exist. -/
theorem not_nonempty (h : D19ActsOnMoore57 V Γ) :
    ¬ Nonempty (D19FinalRepresentationUpperBoundAvoidanceSplitInputs h) := by
  rintro ⟨data⟩
  exact D19FinalRepresentationUpperBoundAvoidanceInputs.not_nonempty h
    ⟨data.toD19FinalRepresentationUpperBoundAvoidanceInputs⟩

end D19FinalRepresentationUpperBoundAvoidanceSplitInputs

end Moore57

/-!
# Final D19 inputs from carrier-style base-selection witnesses

This file gives final-boundary wrappers whose selected rotation-orbit bases are
provided by the more constructive carrier, witness, and enumeration interfaces,
then converted to the downstream `OrbitBaseSelectionInput` used by the split
avoidance boundary.
-/

namespace Moore57

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- Final D19 input package using a constructive base-selection witness instead
of storing the downstream `OrbitBaseSelectionInput` directly. -/
structure D19FinalRepresentationUpperBoundAvoidanceWitnessInputs
    (h : D19ActsOnMoore57 V Γ) where
  /-- Representation-theoretic multiplicities and nontrivial rotation
  character values. -/
  representation : D19ActsOnMoore57.D19RepresentationCharacterInput h
  /-- Coarse upper bound for nontrivial rotation fixed vertices. -/
  fixedUpperBound : D19ActsOnMoore57.RotationFixedUpperBoundInput h
  /-- Constructive witness for the selected moved rotation orbits. -/
  orbitBase : OrbitBaseSelectionWitness h
  /-- Split avoidance-based adjacent-moved witness over the input produced from
  the constructive base-selection witness. -/
  adjacentMoved :
    AdjacentMovedReflectionAvoidanceSplit38Witness h orbitBase.toInput

namespace D19FinalRepresentationUpperBoundAvoidanceWitnessInputs

variable {h : D19ActsOnMoore57 V Γ}

/-- Convert the witness-based final boundary to the split final boundary. -/
noncomputable def toD19FinalRepresentationUpperBoundAvoidanceSplitInputs
    (data : D19FinalRepresentationUpperBoundAvoidanceWitnessInputs h) :
    D19FinalRepresentationUpperBoundAvoidanceSplitInputs h where
  representation := data.representation
  fixedUpperBound := data.fixedUpperBound
  orbitBase := data.orbitBase.toInput
  adjacentMoved := data.adjacentMoved

/-- Convert the witness-based final boundary to the avoidance final boundary. -/
noncomputable def toD19FinalRepresentationUpperBoundAvoidanceInputs
    (data : D19FinalRepresentationUpperBoundAvoidanceWitnessInputs h) :
    D19FinalRepresentationUpperBoundAvoidanceInputs h :=
  data.toD19FinalRepresentationUpperBoundAvoidanceSplitInputs
    |>.toD19FinalRepresentationUpperBoundAvoidanceInputs

/-- Forget the witness presentation down to the final input record. -/
noncomputable def toD19FinalInputs
    (data : D19FinalRepresentationUpperBoundAvoidanceWitnessInputs h) :
    D19FinalInputs h :=
  data.toD19FinalRepresentationUpperBoundAvoidanceSplitInputs.toD19FinalInputs

/-- Final witness-based, split avoidance adjacent-moved inputs cannot exist. -/
theorem not_nonempty (h : D19ActsOnMoore57 V Γ) :
    ¬ Nonempty (D19FinalRepresentationUpperBoundAvoidanceWitnessInputs h) := by
  rintro ⟨data⟩
  exact D19FinalRepresentationUpperBoundAvoidanceSplitInputs.not_nonempty h
    ⟨data.toD19FinalRepresentationUpperBoundAvoidanceSplitInputs⟩

end D19FinalRepresentationUpperBoundAvoidanceWitnessInputs

/-- Final D19 input package using a bounded carrier witness instead of storing
the downstream `OrbitBaseSelectionInput` directly. -/
structure D19FinalRepresentationUpperBoundAvoidanceCarrierInputs
    (h : D19ActsOnMoore57 V Γ) where
  /-- Representation-theoretic multiplicities and nontrivial rotation
  character values. -/
  representation : D19ActsOnMoore57.D19RepresentationCharacterInput h
  /-- Coarse upper bound for nontrivial rotation fixed vertices. -/
  fixedUpperBound : D19ActsOnMoore57.RotationFixedUpperBoundInput h
  /-- Bounded carrier witness for the selected moved rotation orbits. -/
  orbitBase : OrbitBaseSelectionCarrierWitness h
  /-- Split avoidance-based adjacent-moved witness over the input produced from
  the carrier witness. -/
  adjacentMoved :
    AdjacentMovedReflectionAvoidanceSplit38Witness h orbitBase.toInput

namespace D19FinalRepresentationUpperBoundAvoidanceCarrierInputs

variable {h : D19ActsOnMoore57 V Γ}

/-- Convert the carrier-based final boundary to the witness-based boundary. -/
noncomputable def toWitnessInputs
    (data : D19FinalRepresentationUpperBoundAvoidanceCarrierInputs h) :
    D19FinalRepresentationUpperBoundAvoidanceWitnessInputs h where
  representation := data.representation
  fixedUpperBound := data.fixedUpperBound
  orbitBase := data.orbitBase.toWitness
  adjacentMoved := by
    simpa [OrbitBaseSelectionCarrierWitness.toInput] using data.adjacentMoved

/-- Convert the carrier-based final boundary to the split final boundary. -/
noncomputable def toD19FinalRepresentationUpperBoundAvoidanceSplitInputs
    (data : D19FinalRepresentationUpperBoundAvoidanceCarrierInputs h) :
    D19FinalRepresentationUpperBoundAvoidanceSplitInputs h :=
  data.toWitnessInputs.toD19FinalRepresentationUpperBoundAvoidanceSplitInputs

/-- Convert the carrier-based final boundary to the avoidance final boundary.
-/
noncomputable def toD19FinalRepresentationUpperBoundAvoidanceInputs
    (data : D19FinalRepresentationUpperBoundAvoidanceCarrierInputs h) :
    D19FinalRepresentationUpperBoundAvoidanceInputs h :=
  data.toD19FinalRepresentationUpperBoundAvoidanceSplitInputs
    |>.toD19FinalRepresentationUpperBoundAvoidanceInputs

/-- Forget the carrier presentation down to the final input record. -/
noncomputable def toD19FinalInputs
    (data : D19FinalRepresentationUpperBoundAvoidanceCarrierInputs h) :
    D19FinalInputs h :=
  data.toD19FinalRepresentationUpperBoundAvoidanceSplitInputs.toD19FinalInputs

/-- Final carrier-based, split avoidance adjacent-moved inputs cannot exist. -/
theorem not_nonempty (h : D19ActsOnMoore57 V Γ) :
    ¬ Nonempty (D19FinalRepresentationUpperBoundAvoidanceCarrierInputs h) := by
  rintro ⟨data⟩
  exact D19FinalRepresentationUpperBoundAvoidanceSplitInputs.not_nonempty h
    ⟨data.toD19FinalRepresentationUpperBoundAvoidanceSplitInputs⟩

end D19FinalRepresentationUpperBoundAvoidanceCarrierInputs

/-- Final D19 input package using an explicit coordinate enumeration for the
selected moved rotation orbits. -/
structure D19FinalRepresentationUpperBoundAvoidanceEnumerationInputs
    (h : D19ActsOnMoore57 V Γ) where
  /-- Representation-theoretic multiplicities and nontrivial rotation
  character values. -/
  representation : D19ActsOnMoore57.D19RepresentationCharacterInput h
  /-- Coarse upper bound for nontrivial rotation fixed vertices. -/
  fixedUpperBound : D19ActsOnMoore57.RotationFixedUpperBoundInput h
  /-- Coordinate enumeration of the selected moved rotation orbits. -/
  orbitBase : OrbitBaseSelectionEnumeration h
  /-- Split avoidance-based adjacent-moved witness over the input produced from
  the coordinate enumeration. -/
  adjacentMoved :
    AdjacentMovedReflectionAvoidanceSplit38Witness h orbitBase.toInput

namespace D19FinalRepresentationUpperBoundAvoidanceEnumerationInputs

variable {h : D19ActsOnMoore57 V Γ}

/-- Convert the enumeration-based final boundary to the witness-based boundary.
-/
noncomputable def toWitnessInputs
    (data : D19FinalRepresentationUpperBoundAvoidanceEnumerationInputs h) :
    D19FinalRepresentationUpperBoundAvoidanceWitnessInputs h where
  representation := data.representation
  fixedUpperBound := data.fixedUpperBound
  orbitBase := data.orbitBase.toWitness
  adjacentMoved := by
    simpa [OrbitBaseSelectionEnumeration.toInput] using data.adjacentMoved

/-- Convert the enumeration-based final boundary to the split final boundary.
-/
noncomputable def toD19FinalRepresentationUpperBoundAvoidanceSplitInputs
    (data : D19FinalRepresentationUpperBoundAvoidanceEnumerationInputs h) :
    D19FinalRepresentationUpperBoundAvoidanceSplitInputs h :=
  data.toWitnessInputs.toD19FinalRepresentationUpperBoundAvoidanceSplitInputs

/-- Convert the enumeration-based final boundary to the avoidance final
boundary. -/
noncomputable def toD19FinalRepresentationUpperBoundAvoidanceInputs
    (data : D19FinalRepresentationUpperBoundAvoidanceEnumerationInputs h) :
    D19FinalRepresentationUpperBoundAvoidanceInputs h :=
  data.toD19FinalRepresentationUpperBoundAvoidanceSplitInputs
    |>.toD19FinalRepresentationUpperBoundAvoidanceInputs

/-- Forget the enumeration presentation down to the final input record. -/
noncomputable def toD19FinalInputs
    (data : D19FinalRepresentationUpperBoundAvoidanceEnumerationInputs h) :
    D19FinalInputs h :=
  data.toD19FinalRepresentationUpperBoundAvoidanceSplitInputs.toD19FinalInputs

/-- Final enumeration-based, split avoidance adjacent-moved inputs cannot
exist. -/
theorem not_nonempty (h : D19ActsOnMoore57 V Γ) :
    ¬ Nonempty (D19FinalRepresentationUpperBoundAvoidanceEnumerationInputs h) := by
  rintro ⟨data⟩
  exact D19FinalRepresentationUpperBoundAvoidanceSplitInputs.not_nonempty h
    ⟨data.toD19FinalRepresentationUpperBoundAvoidanceSplitInputs⟩

end D19FinalRepresentationUpperBoundAvoidanceEnumerationInputs

end Moore57

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

