import Moore57.D19OnMoore57.AdjacentMoved.TwoCopyCriteria
import Moore57.D19OnMoore57.Final.Inputs
import Moore57.D19OnMoore57.Fixed.UpperBoundEnumeration
import Moore57.D19OnMoore57.LinearCharacter.Input
import Moore57.D19OnMoore57.Misc.CharacterInputPackaging
import Moore57.D19OnMoore57.Orbit.BaseSelection
import Moore57.D19OnMoore57.Rotation.FixedUniqueCriteria

/-!
# Constructive final D19 input packaging

This file gives a more constructive high-level boundary for the final D19
contradiction inputs: orbit bases are supplied by an explicit coordinate
enumeration, and the adjacent-moved contribution is supplied by the specialized
two-copy partition witness with residual contribution `38`.
-/

namespace Moore57

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- Constructive final input record for the D19 contradiction.

Compared with `D19FinalInputs`, this asks for the orbit base via an injective
coordinate enumeration and asks for the adjacent-moved decomposition via the
specialized two-copy partition witness whose residual contribution is `38`. -/
structure D19ConstructiveFinalInputs (h : D19ActsOnMoore57 V Γ) where
  /-- Split final character input. -/
  character : D19FinalCharacterInputs h
  /-- Constructive enumeration of the selected 56 moved rotation orbits. -/
  orbitBase : OrbitBaseSelectionEnumeration h
  /-- Constructive two-copy adjacent-moved partition over the selected bases. -/
  adjacentMoved :
    AdjacentMovedTwoCopyPartition38Witness h orbitBase.base

namespace D19ConstructiveFinalInputs

variable {h : D19ActsOnMoore57 V Γ}

/-- Forget the constructive witnesses down to the final input boundary. -/
noncomputable def toD19FinalInputs
    (data : D19ConstructiveFinalInputs h) :
    D19FinalInputs h where
  character := data.character
  orbitBase := data.orbitBase.toWitness
  fixedOrAContribution := fixedOrAContribution38
  fixed_or_A_contribution := by
    intro d hd
    rfl
  adjacentMovedDecomposition := by
    simpa [OrbitBaseSelectionEnumeration.toWitness,
      OrbitBaseSelectionWitness.ofOrbitCoordinateInjective] using
      data.adjacentMoved.toDecomposition

/-- Constructive final inputs cannot exist. -/
theorem not_nonempty (h : D19ActsOnMoore57 V Γ) :
    ¬ Nonempty (D19ConstructiveFinalInputs h) := by
  rintro ⟨data⟩
  exact D19FinalInputs.not_nonempty h ⟨data.toD19FinalInputs⟩

/-- Convenience constructor from old bundled `TraceCharacterData`, an orbit
enumeration, and the two-copy-`38` adjacent-moved witness. -/
noncomputable def ofTraceCharacterData
    (h : D19ActsOnMoore57 V Γ)
    (hold : TraceCharacterData Γ h.rotation h.a1)
    (orbitBase : OrbitBaseSelectionEnumeration h)
    (adjacentMoved :
      AdjacentMovedTwoCopyPartition38Witness h orbitBase.base) :
    D19ConstructiveFinalInputs h where
  character := D19FinalCharacterInputs.ofTraceCharacterData h hold
  orbitBase := orbitBase
  adjacentMoved := adjacentMoved

/-- Constructor from a final character input, an embedding-valued orbit
enumeration, and the matching two-copy-`38` witness. -/
noncomputable def ofEmbedding
    (character : D19FinalCharacterInputs h)
    (orbitBase : OrbitBaseSelectionEmbeddingWitness h)
    (adjacentMoved :
      AdjacentMovedTwoCopyPartition38Witness h orbitBase.base) :
    D19ConstructiveFinalInputs h where
  character := character
  orbitBase := orbitBase.toEnumeration
  adjacentMoved := by
    simpa [OrbitBaseSelectionEmbeddingWitness.toEnumeration] using
      adjacentMoved

/-- Convert a subtype-equivalence orbit witness into the enumeration form used
by `D19ConstructiveFinalInputs`. -/
noncomputable def enumerationOfSubtypeEquiv
    (orbitBase : OrbitBaseSelectionSubtypeEquivWitness h) :
    OrbitBaseSelectionEnumeration h where
  base := orbitBase.base
  coord := fun qi => orbitBase.coordEquiv qi
  coord_eq_rotation := orbitBase.coord_eq_rotation
  coord_injective := by
    intro qi qj heq
    apply orbitBase.coordEquiv.injective
    apply Subtype.ext
    exact heq

/-- Constructor from a final character input, a subtype-equivalence orbit
enumeration, and the matching two-copy-`38` witness. -/
noncomputable def ofSubtypeEquiv
    (character : D19FinalCharacterInputs h)
    (orbitBase : OrbitBaseSelectionSubtypeEquivWitness h)
    (adjacentMoved :
      AdjacentMovedTwoCopyPartition38Witness h orbitBase.base) :
    D19ConstructiveFinalInputs h where
  character := character
  orbitBase := enumerationOfSubtypeEquiv orbitBase
  adjacentMoved := by
    simpa [enumerationOfSubtypeEquiv] using
      adjacentMoved

/-- Old bundled `TraceCharacterData` plus an embedding-valued orbit
enumeration gives constructive final inputs. -/
noncomputable def ofTraceCharacterDataEmbedding
    (h : D19ActsOnMoore57 V Γ)
    (hold : TraceCharacterData Γ h.rotation h.a1)
    (orbitBase : OrbitBaseSelectionEmbeddingWitness h)
    (adjacentMoved :
      AdjacentMovedTwoCopyPartition38Witness h orbitBase.base) :
    D19ConstructiveFinalInputs h :=
  ofEmbedding (D19FinalCharacterInputs.ofTraceCharacterData h hold)
    orbitBase adjacentMoved

/-- Old bundled `TraceCharacterData` plus a subtype-equivalence orbit
enumeration gives constructive final inputs. -/
noncomputable def ofTraceCharacterDataSubtypeEquiv
    (h : D19ActsOnMoore57 V Γ)
    (hold : TraceCharacterData Γ h.rotation h.a1)
    (orbitBase : OrbitBaseSelectionSubtypeEquivWitness h)
    (adjacentMoved :
      AdjacentMovedTwoCopyPartition38Witness h orbitBase.base) :
    D19ConstructiveFinalInputs h :=
  ofSubtypeEquiv (D19FinalCharacterInputs.ofTraceCharacterData h hold)
    orbitBase adjacentMoved

end D19ConstructiveFinalInputs

end Moore57

/-!
# Constructive final D19 inputs from a unique rotation fixed point

This file packages the final constructive D19 boundary in the common case
where rotation by `1` has a unique fixed vertex.  The character input is split:
the representation-theoretic part is supplied directly, while the fixed-count
upper bound is derived from the unique fixed point.
-/

namespace Moore57

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- Constructive final input record where the fixed-count input is replaced by
a unique fixed point for rotation by `1`.

This boundary does not depend on the old bundled `TraceCharacterData`; it keeps
only the representation-character input, a unique fixed-point statement, an
explicit orbit-base enumeration, and the specialized two-copy adjacent-moved
partition witness. -/
structure D19ConstructiveFinalUniqueInputs (h : D19ActsOnMoore57 V Γ) where
  /-- Representation-theoretic multiplicities and rotation character values. -/
  representation : D19ActsOnMoore57.D19RepresentationCharacterInput h
  /-- Rotation by `1` has a unique fixed vertex. -/
  rotationOne_unique_fixed : ∃! v : V, h.rotation 1 v = v
  /-- Constructive enumeration of the selected 56 moved rotation orbits. -/
  orbitBase : OrbitBaseSelectionEnumeration h
  /-- Constructive two-copy adjacent-moved partition over the selected bases. -/
  adjacentMoved :
    AdjacentMovedTwoCopyPartition38Witness h orbitBase.base

namespace D19ConstructiveFinalUniqueInputs

variable {h : D19ActsOnMoore57 V Γ}

/-- The unique fixed point supplies the final split character input. -/
def toD19FinalCharacterInputs
    (data : D19ConstructiveFinalUniqueInputs h) :
    D19FinalCharacterInputs h where
  representation := data.representation
  fixedUpperBound :=
    D19ActsOnMoore57.RotationFixedUpperBoundInput.of_existsUnique_rotation_one_fixed
      h data.rotationOne_unique_fixed

/-- Forget the unique-fixed-point witness down to the constructive final input
boundary. -/
noncomputable def toD19ConstructiveFinalInputs
    (data : D19ConstructiveFinalUniqueInputs h) :
    D19ConstructiveFinalInputs h where
  character := data.toD19FinalCharacterInputs
  orbitBase := data.orbitBase
  adjacentMoved := data.adjacentMoved

/-- Forget the unique-fixed-point witness down to the final input boundary. -/
noncomputable def toD19FinalInputs
    (data : D19ConstructiveFinalUniqueInputs h) :
    D19FinalInputs h :=
  data.toD19ConstructiveFinalInputs.toD19FinalInputs

/-- Constructive final unique inputs cannot exist. -/
theorem not_nonempty (h : D19ActsOnMoore57 V Γ) :
    ¬ Nonempty (D19ConstructiveFinalUniqueInputs h) := by
  rintro ⟨data⟩
  exact D19ConstructiveFinalInputs.not_nonempty h
    ⟨data.toD19ConstructiveFinalInputs⟩

end D19ConstructiveFinalUniqueInputs

end Moore57

/-!
# Constructive final D19 inputs with fixed-point enumeration

This file refines `D19ConstructiveFinalInputs` by replacing the fixed-count
part of the final character input with an explicit enumeration of the
rotation-one fixed vertices.  The representation-character input remains
separate from the geometric fixed-count bound.
-/

namespace Moore57

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- Constructive final input record whose fixed-count bound is supplied by an
explicit finite enumeration of the vertices fixed by `h.rotation 1`.

The old bundled `TraceCharacterData` is not needed for the fixed-count part:
the field `fixedEnumeration` is converted to `RotationFixedUpperBoundInput`
independently. -/
structure D19ConstructiveFinalFixedEnumerationInputs
    (h : D19ActsOnMoore57 V Γ) where
  /-- Representation-theoretic multiplicities and rotation character values. -/
  representation : D19ActsOnMoore57.D19RepresentationCharacterInput h
  /-- Explicit finite cover of the rotation-one fixed vertices, of size at
  most nineteen. -/
  fixedEnumeration : D19ActsOnMoore57.RotationOneFixedEnumeration h
  /-- Constructive enumeration of the selected 56 moved rotation orbits. -/
  orbitBase : OrbitBaseSelectionEnumeration h
  /-- Constructive two-copy adjacent-moved partition over the selected bases. -/
  adjacentMoved :
    AdjacentMovedTwoCopyPartition38Witness h orbitBase.base

namespace D19ConstructiveFinalFixedEnumerationInputs

variable {h : D19ActsOnMoore57 V Γ}

/-- Convert the representation input and fixed-point enumeration into the
split final character input. -/
def toD19FinalCharacterInputs
    (data : D19ConstructiveFinalFixedEnumerationInputs h) :
    D19FinalCharacterInputs h where
  representation := data.representation
  fixedUpperBound := data.fixedEnumeration.toRotationFixedUpperBoundInput

/-- Forget the fixed-point enumeration boundary down to the existing
constructive final input record. -/
def toD19ConstructiveFinalInputs
    (data : D19ConstructiveFinalFixedEnumerationInputs h) :
    D19ConstructiveFinalInputs h where
  character := data.toD19FinalCharacterInputs
  orbitBase := data.orbitBase
  adjacentMoved := data.adjacentMoved

/-- Forget the fixed-point enumeration boundary all the way to final inputs. -/
noncomputable def toD19FinalInputs
    (data : D19ConstructiveFinalFixedEnumerationInputs h) :
    D19FinalInputs h :=
  data.toD19ConstructiveFinalInputs.toD19FinalInputs

/-- Constructive final inputs with fixed-point enumeration cannot exist. -/
theorem not_nonempty (h : D19ActsOnMoore57 V Γ) :
    ¬ Nonempty (D19ConstructiveFinalFixedEnumerationInputs h) := by
  rintro ⟨data⟩
  exact D19ConstructiveFinalInputs.not_nonempty h
    ⟨data.toD19ConstructiveFinalInputs⟩

/-- Convenience constructor using old bundled `TraceCharacterData` only for
the representation-character input.  The fixed-count upper bound is supplied
independently by `fixedEnumeration`. -/
noncomputable def ofTraceCharacterDataRepresentation
    (h : D19ActsOnMoore57 V Γ)
    (hold : TraceCharacterData Γ h.rotation h.a1)
    (fixedEnumeration : D19ActsOnMoore57.RotationOneFixedEnumeration h)
    (orbitBase : OrbitBaseSelectionEnumeration h)
    (adjacentMoved :
      AdjacentMovedTwoCopyPartition38Witness h orbitBase.base) :
    D19ConstructiveFinalFixedEnumerationInputs h where
  representation :=
    D19ActsOnMoore57.D19RepresentationCharacterInput.ofTraceCharacterData
      h hold
  fixedEnumeration := fixedEnumeration
  orbitBase := orbitBase
  adjacentMoved := adjacentMoved

end D19ConstructiveFinalFixedEnumerationInputs

end Moore57

/-!
# Constructive final D19 inputs from a linear character and unique fixed point

This file packages the final constructive input boundary when the character
input is supplied as a full D19 linear-character equality and the fixed-count
input is supplied by a unique fixed point of rotation by `1`.
-/

namespace Moore57

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- Constructive final inputs using a full linear-character witness and a
unique fixed point for rotation by `1`.

The full linear-character witness is forgotten to the representation-character
input consumed by `D19ConstructiveFinalUniqueInputs`. -/
structure D19ConstructiveFinalLinearUniqueInputs
    (h : D19ActsOnMoore57 V Γ) where
  /-- Full D19 linear-character equality for the trace representation. -/
  linearCharacter : D19ActsOnMoore57.D19LinearCharacterInput h
  /-- Rotation by `1` has a unique fixed vertex. -/
  rotationOne_unique_fixed : ∃! v : V, h.rotation 1 v = v
  /-- Constructive enumeration of the selected 56 moved rotation orbits. -/
  orbitBase : OrbitBaseSelectionEnumeration h
  /-- Constructive two-copy adjacent-moved partition over the selected bases. -/
  adjacentMoved :
    AdjacentMovedTwoCopyPartition38Witness h orbitBase.base

namespace D19ConstructiveFinalLinearUniqueInputs

variable {h : D19ActsOnMoore57 V Γ}

/-- Forget the full linear-character witness to the unique-fixed final
constructive boundary. -/
noncomputable def toD19ConstructiveFinalUniqueInputs
    (data : D19ConstructiveFinalLinearUniqueInputs h) :
    D19ConstructiveFinalUniqueInputs h where
  representation := data.linearCharacter.toD19RepresentationCharacterInput
  rotationOne_unique_fixed := data.rotationOne_unique_fixed
  orbitBase := data.orbitBase
  adjacentMoved := data.adjacentMoved

/-- Forget the linear-character and unique-fixed witnesses down to the
constructive final input boundary. -/
noncomputable def toD19ConstructiveFinalInputs
    (data : D19ConstructiveFinalLinearUniqueInputs h) :
    D19ConstructiveFinalInputs h :=
  data.toD19ConstructiveFinalUniqueInputs.toD19ConstructiveFinalInputs

/-- Forget the linear-character and unique-fixed witnesses down to the final
input boundary. -/
noncomputable def toD19FinalInputs
    (data : D19ConstructiveFinalLinearUniqueInputs h) :
    D19FinalInputs h :=
  data.toD19ConstructiveFinalUniqueInputs.toD19FinalInputs

/-- Constructive final linear-character plus unique-fixed inputs cannot exist. -/
theorem not_nonempty (h : D19ActsOnMoore57 V Γ) :
    ¬ Nonempty (D19ConstructiveFinalLinearUniqueInputs h) := by
  rintro ⟨data⟩
  exact D19ConstructiveFinalUniqueInputs.not_nonempty h
    ⟨data.toD19ConstructiveFinalUniqueInputs⟩

end D19ConstructiveFinalLinearUniqueInputs

end Moore57

/-!
# Constructive final D19 inputs with linear character and fixed enumeration

This file combines the full linear-character input with the fixed-point
enumeration boundary.  The linear-character witness is reduced to the
representation-character input consumed by
`D19ConstructiveFinalFixedEnumerationInputs`.
-/

namespace Moore57

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- Constructive final input record whose character input is supplied as a
full D19 linear-character equality and whose fixed-count bound is supplied by
an explicit enumeration of the rotation-one fixed vertices. -/
structure D19ConstructiveFinalLinearFixedEnumerationInputs
    (h : D19ActsOnMoore57 V Γ) where
  /-- Full D19 linear-character witness for the trace representation. -/
  linearCharacter : D19ActsOnMoore57.D19LinearCharacterInput h
  /-- Explicit finite cover of the rotation-one fixed vertices. -/
  fixedEnumeration : D19ActsOnMoore57.RotationOneFixedEnumeration h
  /-- Constructive enumeration of the selected 56 moved rotation orbits. -/
  orbitBase : OrbitBaseSelectionEnumeration h
  /-- Constructive two-copy adjacent-moved partition over the selected bases. -/
  adjacentMoved :
    AdjacentMovedTwoCopyPartition38Witness h orbitBase.base

namespace D19ConstructiveFinalLinearFixedEnumerationInputs

variable {h : D19ActsOnMoore57 V Γ}

/-- Convert the full linear-character input and fixed-point enumeration into
the split final character input. -/
def toD19FinalCharacterInputs
    (data : D19ConstructiveFinalLinearFixedEnumerationInputs h) :
    D19FinalCharacterInputs h where
  representation := data.linearCharacter.toD19RepresentationCharacterInput
  fixedUpperBound := data.fixedEnumeration.toRotationFixedUpperBoundInput

/-- Forget the linear-character boundary down to the fixed-enumeration final
input record. -/
def toD19ConstructiveFinalFixedEnumerationInputs
    (data : D19ConstructiveFinalLinearFixedEnumerationInputs h) :
    D19ConstructiveFinalFixedEnumerationInputs h where
  representation := data.linearCharacter.toD19RepresentationCharacterInput
  fixedEnumeration := data.fixedEnumeration
  orbitBase := data.orbitBase
  adjacentMoved := data.adjacentMoved

/-- Forget the linear-character and fixed-enumeration boundaries down to the
constructive final input record. -/
def toD19ConstructiveFinalInputs
    (data : D19ConstructiveFinalLinearFixedEnumerationInputs h) :
    D19ConstructiveFinalInputs h :=
  data.toD19ConstructiveFinalFixedEnumerationInputs.toD19ConstructiveFinalInputs

/-- Forget the constructive boundaries all the way to final inputs. -/
noncomputable def toD19FinalInputs
    (data : D19ConstructiveFinalLinearFixedEnumerationInputs h) :
    D19FinalInputs h :=
  data.toD19ConstructiveFinalFixedEnumerationInputs.toD19FinalInputs

/-- Constructive final inputs with linear character and fixed-point
enumeration cannot exist. -/
theorem not_nonempty (h : D19ActsOnMoore57 V Γ) :
    ¬ Nonempty (D19ConstructiveFinalLinearFixedEnumerationInputs h) := by
  rintro ⟨data⟩
  exact D19ConstructiveFinalFixedEnumerationInputs.not_nonempty h
    ⟨data.toD19ConstructiveFinalFixedEnumerationInputs⟩

end D19ConstructiveFinalLinearFixedEnumerationInputs

end Moore57

