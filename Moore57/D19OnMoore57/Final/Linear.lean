import Moore57.D19OnMoore57.AdjacentMoved.Reflection
import Moore57.D19OnMoore57.D19Core.ConstructiveFinalLinearFixedEnumeration
import Moore57.D19OnMoore57.D19Core.ConstructiveFinalLinearUnique
import Moore57.D19OnMoore57.Final.Inputs
import Moore57.D19OnMoore57.Fixed.UpperBoundEnumeration
import Moore57.D19OnMoore57.LinearCharacter.Input
import Moore57.D19OnMoore57.Orbit.BaseSelection
import Moore57.D19OnMoore57.Rotation.FixedCountUnique
import Moore57.D19OnMoore57.Rotation.FixedUniqueCriteria

/-!
# Final D19 inputs from base-selection inputs and reflection copies

This file lowers the orbit-base boundary from an explicit coordinate
enumeration to the downstream base-selection input: moved bases with pairwise
disjoint rotation orbits.  The bridge to `OrbitBaseSelectionWitness` supplies
the global orbit-coordinate injectivity required by `D19FinalInputs`.
-/

namespace Moore57

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- Final D19 input package using a full linear-character witness, a unique
rotation-one fixed point, a downstream base-selection input, and a
reflection-copy adjacent-moved partition. -/
structure D19FinalLinearUniqueReflectionBaseInputs
    (h : D19ActsOnMoore57 V Γ) where
  /-- Full D19 linear-character witness for the trace representation. -/
  linearCharacter : D19ActsOnMoore57.D19LinearCharacterInput h
  /-- Rotation by `1` has a unique fixed vertex. -/
  rotationOne_unique_fixed : ∃! v : V, h.rotation 1 v = v
  /-- Pairwise-disjoint selected moved rotation orbits. -/
  orbitBase : OrbitBaseSelectionInput h
  /-- Reflection-copy adjacent-moved partition over the selected bases. -/
  adjacentMoved :
    AdjacentMovedReflectionCopyPartition38Witness h orbitBase.base

namespace D19FinalLinearUniqueReflectionBaseInputs

variable {h : D19ActsOnMoore57 V Γ}

/-- Convert the linear-character and unique-fixed inputs into the split final
character input. -/
def toD19FinalCharacterInputs
    (data : D19FinalLinearUniqueReflectionBaseInputs h) :
    D19FinalCharacterInputs h where
  representation := data.linearCharacter.toD19RepresentationCharacterInput
  fixedUpperBound :=
    D19ActsOnMoore57.RotationFixedUpperBoundInput.of_existsUnique_rotation_one_fixed
      h data.rotationOne_unique_fixed

/-- Forget the specialized base and reflection-copy presentation down to the
final input boundary. -/
noncomputable def toD19FinalInputs
    (data : D19FinalLinearUniqueReflectionBaseInputs h) :
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

/-- Final linear-character, unique-fixed, reflection-copy base inputs cannot
exist. -/
theorem not_nonempty (h : D19ActsOnMoore57 V Γ) :
    ¬ Nonempty (D19FinalLinearUniqueReflectionBaseInputs h) := by
  rintro ⟨data⟩
  exact D19FinalInputs.not_nonempty h ⟨data.toD19FinalInputs⟩

end D19FinalLinearUniqueReflectionBaseInputs

end Moore57

/-!
# Final D19 base-selection inputs from fixed enumeration

This file lowers the orbit-base boundary in the fixed-enumeration,
reflection-copy final input package from an explicit orbit-base enumeration to
the downstream base-selection input: moved bases with pairwise disjoint
rotation orbits.
-/

namespace Moore57

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- Final D19 input package using a full linear-character witness, an explicit
rotation-one fixed-point enumeration, a downstream base-selection input, and a
reflection-copy adjacent-moved partition. -/
structure D19FinalLinearFixedEnumerationReflectionBaseInputs
    (h : D19ActsOnMoore57 V Γ) where
  /-- Full D19 linear-character witness for the trace representation. -/
  linearCharacter : D19ActsOnMoore57.D19LinearCharacterInput h
  /-- Explicit finite cover of the rotation-one fixed vertices. -/
  fixedEnumeration : D19ActsOnMoore57.RotationOneFixedEnumeration h
  /-- Pairwise-disjoint selected moved rotation orbits. -/
  orbitBase : OrbitBaseSelectionInput h
  /-- Reflection-copy adjacent-moved partition over the selected bases. -/
  adjacentMoved :
    AdjacentMovedReflectionCopyPartition38Witness h orbitBase.base

namespace D19FinalLinearFixedEnumerationReflectionBaseInputs

variable {h : D19ActsOnMoore57 V Γ}

/-- Convert the linear-character and fixed-enumeration inputs into the split
final character input. -/
def toD19FinalCharacterInputs
    (data : D19FinalLinearFixedEnumerationReflectionBaseInputs h) :
    D19FinalCharacterInputs h where
  representation := data.linearCharacter.toD19RepresentationCharacterInput
  fixedUpperBound := data.fixedEnumeration.toRotationFixedUpperBoundInput

/-- Forget the specialized base and reflection-copy presentation down to the
final input boundary. -/
noncomputable def toD19FinalInputs
    (data : D19FinalLinearFixedEnumerationReflectionBaseInputs h) :
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

/-- Final linear-character, fixed-enumeration, reflection-copy base inputs
cannot exist. -/
theorem not_nonempty (h : D19ActsOnMoore57 V Γ) :
    ¬ Nonempty (D19FinalLinearFixedEnumerationReflectionBaseInputs h) := by
  rintro ⟨data⟩
  exact D19FinalInputs.not_nonempty h ⟨data.toD19FinalInputs⟩

end D19FinalLinearFixedEnumerationReflectionBaseInputs

end Moore57

/-!
# Final D19 base-selection inputs from exact fixed count

This file replaces the unique fixed-point field in
`D19FinalLinearUniqueReflectionBaseInputs` by the exact fixed count
`fixedVertexCount (h.rotation 1) = 1`.
-/

namespace Moore57

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- Final D19 input package using a full linear-character witness, exact
rotation-one fixed count, downstream base-selection input, and a
reflection-copy adjacent-moved partition. -/
structure D19FinalLinearCountReflectionBaseInputs
    (h : D19ActsOnMoore57 V Γ) where
  /-- Full D19 linear-character witness for the trace representation. -/
  linearCharacter : D19ActsOnMoore57.D19LinearCharacterInput h
  /-- Rotation by `1` has exactly one fixed vertex. -/
  rotationOne_fixed_count : fixedVertexCount (h.rotation 1) = 1
  /-- Pairwise-disjoint selected moved rotation orbits. -/
  orbitBase : OrbitBaseSelectionInput h
  /-- Reflection-copy adjacent-moved partition over the selected bases. -/
  adjacentMoved :
    AdjacentMovedReflectionCopyPartition38Witness h orbitBase.base

namespace D19FinalLinearCountReflectionBaseInputs

variable {h : D19ActsOnMoore57 V Γ}

/-- Exact fixed count `1` supplies the unique-fixed base-input boundary. -/
noncomputable def toD19FinalLinearUniqueReflectionBaseInputs
    (data : D19FinalLinearCountReflectionBaseInputs h) :
    D19FinalLinearUniqueReflectionBaseInputs h where
  linearCharacter := data.linearCharacter
  rotationOne_unique_fixed :=
    h.existsUnique_rotation_one_fixed_of_fixedVertexCount_eq_one
      data.rotationOne_fixed_count
  orbitBase := data.orbitBase
  adjacentMoved := data.adjacentMoved

/-- Forget the exact-count presentation down to the final input boundary. -/
noncomputable def toD19FinalInputs
    (data : D19FinalLinearCountReflectionBaseInputs h) :
    D19FinalInputs h :=
  data.toD19FinalLinearUniqueReflectionBaseInputs.toD19FinalInputs

/-- Final linear-character, exact-count, reflection-copy base inputs cannot
exist. -/
theorem not_nonempty (h : D19ActsOnMoore57 V Γ) :
    ¬ Nonempty (D19FinalLinearCountReflectionBaseInputs h) := by
  rintro ⟨data⟩
  exact D19FinalLinearUniqueReflectionBaseInputs.not_nonempty h
    ⟨data.toD19FinalLinearUniqueReflectionBaseInputs⟩

end D19FinalLinearCountReflectionBaseInputs

end Moore57

/-!
# Final D19 base-selection inputs from fixed-set cardinality

This file supplies a `Fintype.card` variant of
`D19FinalLinearCountReflectionBaseInputs`.
-/

namespace Moore57

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- Final D19 input package using a full linear-character witness, cardinality
one of the rotation-one fixed subtype, downstream base-selection input, and a
reflection-copy adjacent-moved partition. -/
structure D19FinalLinearCardReflectionBaseInputs
    (h : D19ActsOnMoore57 V Γ) where
  /-- Full D19 linear-character witness for the trace representation. -/
  linearCharacter : D19ActsOnMoore57.D19LinearCharacterInput h
  /-- The fixed subtype for rotation by `1` has cardinality one. -/
  rotationOne_fixed_card : Fintype.card (fixedVertexSet (h.rotation 1)) = 1
  /-- Pairwise-disjoint selected moved rotation orbits. -/
  orbitBase : OrbitBaseSelectionInput h
  /-- Reflection-copy adjacent-moved partition over the selected bases. -/
  adjacentMoved :
    AdjacentMovedReflectionCopyPartition38Witness h orbitBase.base

namespace D19FinalLinearCardReflectionBaseInputs

variable {h : D19ActsOnMoore57 V Γ}

/-- Convert fixed-subtype cardinality `1` to the exact fixed-count base
boundary. -/
noncomputable def toD19FinalLinearCountReflectionBaseInputs
    (data : D19FinalLinearCardReflectionBaseInputs h) :
    D19FinalLinearCountReflectionBaseInputs h where
  linearCharacter := data.linearCharacter
  rotationOne_fixed_count := by
    simpa [fixedVertexCount_eq_card_fixedVertexSet] using
      data.rotationOne_fixed_card
  orbitBase := data.orbitBase
  adjacentMoved := data.adjacentMoved

/-- Forget the cardinality presentation down to the final input boundary. -/
noncomputable def toD19FinalInputs
    (data : D19FinalLinearCardReflectionBaseInputs h) :
    D19FinalInputs h :=
  data.toD19FinalLinearCountReflectionBaseInputs.toD19FinalInputs

/-- Final linear-character, fixed-cardinality, reflection-copy base inputs
cannot exist. -/
theorem not_nonempty (h : D19ActsOnMoore57 V Γ) :
    ¬ Nonempty (D19FinalLinearCardReflectionBaseInputs h) := by
  rintro ⟨data⟩
  exact D19FinalLinearCountReflectionBaseInputs.not_nonempty h
    ⟨data.toD19FinalLinearCountReflectionBaseInputs⟩

end D19FinalLinearCardReflectionBaseInputs

end Moore57

/-!
# Final D19 base-selection inputs from unique fixed point and constant residual

This file combines the unique-fixed linear-character input package with the
constant-residual reflection-copy adjacent-moved criterion at the downstream
`OrbitBaseSelectionInput` boundary.
-/

namespace Moore57

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- Final D19 input package using a full linear-character witness, a unique
rotation-one fixed point, downstream base-selection input, and a
constant-residual reflection-copy adjacent-moved partition. -/
structure D19FinalLinearUniqueConstantResidualBaseInputs
    (h : D19ActsOnMoore57 V Γ) where
  /-- Full D19 linear-character witness for the trace representation. -/
  linearCharacter : D19ActsOnMoore57.D19LinearCharacterInput h
  /-- Rotation by `1` has a unique fixed vertex. -/
  rotationOne_unique_fixed : ∃! v : V, h.rotation 1 v = v
  /-- Pairwise-disjoint selected moved rotation orbits. -/
  orbitBase : OrbitBaseSelectionInput h
  /-- Constant-residual reflection-copy adjacent-moved partition over the
  selected bases. -/
  adjacentMoved :
    AdjacentMovedReflectionConstantResidual38Witness h orbitBase.base

namespace D19FinalLinearUniqueConstantResidualBaseInputs

variable {h : D19ActsOnMoore57 V Γ}

/-- Forget the constant-residual presentation to the existing unique-fixed,
reflection-copy base-input boundary. -/
noncomputable def toD19FinalLinearUniqueReflectionBaseInputs
    (data : D19FinalLinearUniqueConstantResidualBaseInputs h) :
    D19FinalLinearUniqueReflectionBaseInputs h where
  linearCharacter := data.linearCharacter
  rotationOne_unique_fixed := data.rotationOne_unique_fixed
  orbitBase := data.orbitBase
  adjacentMoved := data.adjacentMoved.toReflectionCopyPartition38Witness

/-- Forget the constant-residual presentation down to final inputs. -/
noncomputable def toD19FinalInputs
    (data : D19FinalLinearUniqueConstantResidualBaseInputs h) :
    D19FinalInputs h :=
  data.toD19FinalLinearUniqueReflectionBaseInputs.toD19FinalInputs

/-- Final linear-character, unique-fixed, constant-residual reflection-copy
base inputs cannot exist. -/
theorem not_nonempty (h : D19ActsOnMoore57 V Γ) :
    ¬ Nonempty (D19FinalLinearUniqueConstantResidualBaseInputs h) := by
  rintro ⟨data⟩
  exact D19FinalLinearUniqueReflectionBaseInputs.not_nonempty h
    ⟨data.toD19FinalLinearUniqueReflectionBaseInputs⟩

end D19FinalLinearUniqueConstantResidualBaseInputs

end Moore57

/-!
# Final D19 base-selection inputs from fixed enumeration and constant residual

This file combines the fixed-enumeration final input package with the
constant-residual reflection-copy adjacent-moved criterion at the downstream
`OrbitBaseSelectionInput` boundary.
-/

namespace Moore57

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- Final D19 input package using a full linear-character witness, an explicit
rotation-one fixed-point enumeration, a downstream base-selection input, and a
constant-residual reflection-copy adjacent-moved partition. -/
structure D19FinalLinearFixedEnumerationConstantResidualBaseInputs
    (h : D19ActsOnMoore57 V Γ) where
  /-- Full D19 linear-character witness for the trace representation. -/
  linearCharacter : D19ActsOnMoore57.D19LinearCharacterInput h
  /-- Explicit finite cover of the rotation-one fixed vertices. -/
  fixedEnumeration : D19ActsOnMoore57.RotationOneFixedEnumeration h
  /-- Pairwise-disjoint selected moved rotation orbits. -/
  orbitBase : OrbitBaseSelectionInput h
  /-- Constant-residual reflection-copy adjacent-moved partition over the
  selected bases. -/
  adjacentMoved :
    AdjacentMovedReflectionConstantResidual38Witness h orbitBase.base

namespace D19FinalLinearFixedEnumerationConstantResidualBaseInputs

variable {h : D19ActsOnMoore57 V Γ}

/-- Forget the constant-residual presentation to the existing fixed-enumeration,
reflection-copy base-input boundary. -/
noncomputable def toD19FinalLinearFixedEnumerationReflectionBaseInputs
    (data : D19FinalLinearFixedEnumerationConstantResidualBaseInputs h) :
    D19FinalLinearFixedEnumerationReflectionBaseInputs h where
  linearCharacter := data.linearCharacter
  fixedEnumeration := data.fixedEnumeration
  orbitBase := data.orbitBase
  adjacentMoved := data.adjacentMoved.toReflectionCopyPartition38Witness

/-- Forget the constant-residual presentation down to final inputs. -/
noncomputable def toD19FinalInputs
    (data : D19FinalLinearFixedEnumerationConstantResidualBaseInputs h) :
    D19FinalInputs h :=
  data.toD19FinalLinearFixedEnumerationReflectionBaseInputs.toD19FinalInputs

/-- Final linear-character, fixed-enumeration, constant-residual reflection-copy
base inputs cannot exist. -/
theorem not_nonempty (h : D19ActsOnMoore57 V Γ) :
    ¬ Nonempty (D19FinalLinearFixedEnumerationConstantResidualBaseInputs h) := by
  rintro ⟨data⟩
  exact D19FinalLinearFixedEnumerationReflectionBaseInputs.not_nonempty h
    ⟨data.toD19FinalLinearFixedEnumerationReflectionBaseInputs⟩

end D19FinalLinearFixedEnumerationConstantResidualBaseInputs

end Moore57

/-!
# Final D19 base-selection inputs from exact fixed count and constant residual

This file combines the exact fixed count and constant-residual
reflection-copy package with the weaker downstream `OrbitBaseSelectionInput`
boundary.
-/

namespace Moore57

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- Final D19 input package using a full linear-character witness, exact
rotation-one fixed count, downstream base-selection input, and a
constant-residual reflection-copy adjacent-moved partition. -/
structure D19FinalLinearCountConstantResidualBaseInputs
    (h : D19ActsOnMoore57 V Γ) where
  /-- Full D19 linear-character witness for the trace representation. -/
  linearCharacter : D19ActsOnMoore57.D19LinearCharacterInput h
  /-- Rotation by `1` has exactly one fixed vertex. -/
  rotationOne_fixed_count : fixedVertexCount (h.rotation 1) = 1
  /-- Pairwise-disjoint selected moved rotation orbits. -/
  orbitBase : OrbitBaseSelectionInput h
  /-- Constant-residual reflection-copy adjacent-moved partition over the
  selected bases. -/
  adjacentMoved :
    AdjacentMovedReflectionConstantResidual38Witness h orbitBase.base

namespace D19FinalLinearCountConstantResidualBaseInputs

variable {h : D19ActsOnMoore57 V Γ}

/-- Forget the constant-residual presentation to the existing exact-count,
reflection-copy base-input boundary. -/
noncomputable def toD19FinalLinearCountReflectionBaseInputs
    (data : D19FinalLinearCountConstantResidualBaseInputs h) :
    D19FinalLinearCountReflectionBaseInputs h where
  linearCharacter := data.linearCharacter
  rotationOne_fixed_count := data.rotationOne_fixed_count
  orbitBase := data.orbitBase
  adjacentMoved := data.adjacentMoved.toReflectionCopyPartition38Witness

/-- Forget the constant-residual and exact-count presentations down to final
inputs. -/
noncomputable def toD19FinalInputs
    (data : D19FinalLinearCountConstantResidualBaseInputs h) :
    D19FinalInputs h :=
  data.toD19FinalLinearCountReflectionBaseInputs.toD19FinalInputs

/-- Cardinality-one fixed set variant of the exact-count input constructor. -/
noncomputable def of_fixedVertexSet_card_eq_one
    (linearCharacter : D19ActsOnMoore57.D19LinearCharacterInput h)
    (rotationOne_fixed_card :
      Fintype.card (fixedVertexSet (h.rotation 1)) = 1)
    (orbitBase : OrbitBaseSelectionInput h)
    (adjacentMoved :
      AdjacentMovedReflectionConstantResidual38Witness h orbitBase.base) :
    D19FinalLinearCountConstantResidualBaseInputs h where
  linearCharacter := linearCharacter
  rotationOne_fixed_count := by
    simpa [fixedVertexCount_eq_card_fixedVertexSet] using rotationOne_fixed_card
  orbitBase := orbitBase
  adjacentMoved := adjacentMoved

/-- Final linear-character, exact-count, constant-residual reflection-copy
base inputs cannot exist. -/
theorem not_nonempty (h : D19ActsOnMoore57 V Γ) :
    ¬ Nonempty (D19FinalLinearCountConstantResidualBaseInputs h) := by
  rintro ⟨data⟩
  exact D19FinalLinearCountReflectionBaseInputs.not_nonempty h
    ⟨data.toD19FinalLinearCountReflectionBaseInputs⟩

end D19FinalLinearCountConstantResidualBaseInputs

end Moore57

/-!
# Final D19 base-selection inputs from fixed-set cardinality and constant residual

This file supplies a `Fintype.card` variant of
`D19FinalLinearCountConstantResidualBaseInputs`.
-/

namespace Moore57

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- Final D19 input package using a full linear-character witness, cardinality
one of the rotation-one fixed subtype, downstream base-selection input, and a
constant-residual reflection-copy adjacent-moved partition. -/
structure D19FinalLinearCardConstantResidualBaseInputs
    (h : D19ActsOnMoore57 V Γ) where
  /-- Full D19 linear-character witness for the trace representation. -/
  linearCharacter : D19ActsOnMoore57.D19LinearCharacterInput h
  /-- The fixed subtype for rotation by `1` has cardinality one. -/
  rotationOne_fixed_card : Fintype.card (fixedVertexSet (h.rotation 1)) = 1
  /-- Pairwise-disjoint selected moved rotation orbits. -/
  orbitBase : OrbitBaseSelectionInput h
  /-- Constant-residual reflection-copy adjacent-moved partition over the
  selected bases. -/
  adjacentMoved :
    AdjacentMovedReflectionConstantResidual38Witness h orbitBase.base

namespace D19FinalLinearCardConstantResidualBaseInputs

variable {h : D19ActsOnMoore57 V Γ}

/-- Convert fixed-subtype cardinality `1` to the exact fixed-count,
constant-residual base boundary. -/
noncomputable def toD19FinalLinearCountConstantResidualBaseInputs
    (data : D19FinalLinearCardConstantResidualBaseInputs h) :
    D19FinalLinearCountConstantResidualBaseInputs h where
  linearCharacter := data.linearCharacter
  rotationOne_fixed_count := by
    simpa [fixedVertexCount_eq_card_fixedVertexSet] using
      data.rotationOne_fixed_card
  orbitBase := data.orbitBase
  adjacentMoved := data.adjacentMoved

/-- Forget the cardinality presentation down to the final input boundary. -/
noncomputable def toD19FinalInputs
    (data : D19FinalLinearCardConstantResidualBaseInputs h) :
    D19FinalInputs h :=
  data.toD19FinalLinearCountConstantResidualBaseInputs.toD19FinalInputs

/-- Final linear-character, fixed-cardinality, constant-residual reflection-copy
base inputs cannot exist. -/
theorem not_nonempty (h : D19ActsOnMoore57 V Γ) :
    ¬ Nonempty (D19FinalLinearCardConstantResidualBaseInputs h) := by
  rintro ⟨data⟩
  exact D19FinalLinearCountConstantResidualBaseInputs.not_nonempty h
    ⟨data.toD19FinalLinearCountConstantResidualBaseInputs⟩

end D19FinalLinearCardConstantResidualBaseInputs

end Moore57

/-!
# Final D19 inputs from a linear character, unique fixed point, and reflection copy

This file packages the final constructive input boundary in the common case
where the two-copy adjacent-moved partition is supplied by a reflection-copy
witness.
-/

namespace Moore57

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- Final constructive inputs using a full linear-character witness, a unique
fixed point for rotation by `1`, and a reflection-copy adjacent-moved
partition. -/
structure D19FinalLinearUniqueReflectionInputs
    (h : D19ActsOnMoore57 V Γ) where
  /-- Full D19 linear-character equality for the trace representation. -/
  linearCharacter : D19ActsOnMoore57.D19LinearCharacterInput h
  /-- Rotation by `1` has a unique fixed vertex. -/
  rotationOne_unique_fixed : ∃! v : V, h.rotation 1 v = v
  /-- Constructive enumeration of the selected 56 moved rotation orbits. -/
  orbitBase : OrbitBaseSelectionEnumeration h
  /-- Reflection-copy adjacent-moved partition over the selected bases. -/
  adjacentMoved :
    AdjacentMovedReflectionCopyPartition38Witness h orbitBase.base

namespace D19FinalLinearUniqueReflectionInputs

variable {h : D19ActsOnMoore57 V Γ}

/-- Forget the reflection-copy presentation to the existing linear-character
and unique-fixed constructive boundary. -/
noncomputable def toD19ConstructiveFinalLinearUniqueInputs
    (data : D19FinalLinearUniqueReflectionInputs h) :
    D19ConstructiveFinalLinearUniqueInputs h where
  linearCharacter := data.linearCharacter
  rotationOne_unique_fixed := data.rotationOne_unique_fixed
  orbitBase := data.orbitBase
  adjacentMoved := data.adjacentMoved.toTwoCopyPartition38Witness

/-- Forget the reflection-copy, linear-character, and unique-fixed witnesses
down to the constructive final input boundary. -/
noncomputable def toD19ConstructiveFinalInputs
    (data : D19FinalLinearUniqueReflectionInputs h) :
    D19ConstructiveFinalInputs h :=
  data.toD19ConstructiveFinalLinearUniqueInputs.toD19ConstructiveFinalInputs

/-- Forget the reflection-copy, linear-character, and unique-fixed witnesses
down to the final input boundary. -/
noncomputable def toD19FinalInputs
    (data : D19FinalLinearUniqueReflectionInputs h) :
    D19FinalInputs h :=
  data.toD19ConstructiveFinalLinearUniqueInputs.toD19FinalInputs

/-- Final linear-character, unique-fixed, reflection-copy inputs cannot exist. -/
theorem not_nonempty (h : D19ActsOnMoore57 V Γ) :
    ¬ Nonempty (D19FinalLinearUniqueReflectionInputs h) := by
  rintro ⟨data⟩
  exact D19ConstructiveFinalLinearUniqueInputs.not_nonempty h
    ⟨data.toD19ConstructiveFinalLinearUniqueInputs⟩

end D19FinalLinearUniqueReflectionInputs

end Moore57

/-!
# Final D19 inputs from linear character, fixed enumeration, and reflection copies

This file packages the final contradiction input where the character side is a
full linear-character equality, the fixed-vertex bound is supplied by an
explicit rotation-one fixed enumeration, and the adjacent-moved partition is
given by the reflection-copy criterion.
-/

namespace Moore57

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- Final D19 input package using the linear-character criterion, an explicit
fixed-point enumeration, an orbit-base enumeration, and a reflection-copy
adjacent-moved partition. -/
structure D19FinalLinearFixedEnumerationReflectionInputs
    (h : D19ActsOnMoore57 V Γ) where
  /-- Full D19 linear-character witness for the trace representation. -/
  linearCharacter : D19ActsOnMoore57.D19LinearCharacterInput h
  /-- Explicit finite cover of the rotation-one fixed vertices. -/
  fixedEnumeration : D19ActsOnMoore57.RotationOneFixedEnumeration h
  /-- Constructive enumeration of the selected 56 moved rotation orbits. -/
  orbitBase : OrbitBaseSelectionEnumeration h
  /-- Reflection-copy adjacent-moved partition over the selected bases. -/
  adjacentMoved :
    AdjacentMovedReflectionCopyPartition38Witness h orbitBase.base

namespace D19FinalLinearFixedEnumerationReflectionInputs

variable {h : D19ActsOnMoore57 V Γ}

/-- Forget the reflection-copy adjacent-moved boundary to the two-copy final
input with linear character and fixed-point enumeration. -/
noncomputable def toD19ConstructiveFinalLinearFixedEnumerationInputs
    (data : D19FinalLinearFixedEnumerationReflectionInputs h) :
    D19ConstructiveFinalLinearFixedEnumerationInputs h where
  linearCharacter := data.linearCharacter
  fixedEnumeration := data.fixedEnumeration
  orbitBase := data.orbitBase
  adjacentMoved := data.adjacentMoved.toTwoCopyPartition38Witness

/-- Forget the specialized boundaries down to constructive final inputs. -/
noncomputable def toD19ConstructiveFinalInputs
    (data : D19FinalLinearFixedEnumerationReflectionInputs h) :
    D19ConstructiveFinalInputs h :=
  data.toD19ConstructiveFinalLinearFixedEnumerationInputs.toD19ConstructiveFinalInputs

/-- Forget all specialized boundaries down to final inputs. -/
noncomputable def toD19FinalInputs
    (data : D19FinalLinearFixedEnumerationReflectionInputs h) :
    D19FinalInputs h :=
  data.toD19ConstructiveFinalLinearFixedEnumerationInputs.toD19FinalInputs

/-- Final inputs in the linear-character, fixed-enumeration, reflection-copy
form cannot exist. -/
theorem not_nonempty (h : D19ActsOnMoore57 V Γ) :
    ¬ Nonempty (D19FinalLinearFixedEnumerationReflectionInputs h) := by
  rintro ⟨data⟩
  exact D19ConstructiveFinalLinearFixedEnumerationInputs.not_nonempty h
    ⟨data.toD19ConstructiveFinalLinearFixedEnumerationInputs⟩

end D19FinalLinearFixedEnumerationReflectionInputs

end Moore57

/-!
# Final D19 inputs from an exact fixed count and reflection copy

This file packages the final constructive input boundary when the rotation-one
fixed side is supplied as the exact count `1`, and the adjacent-moved side is
supplied by a reflection-copy witness.
-/

namespace Moore57

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- Final linear-character inputs using the exact fixed count
`fixedVertexCount (h.rotation 1) = 1` and a reflection-copy adjacent-moved
partition. -/
structure D19FinalLinearCountReflectionInputs
    (h : D19ActsOnMoore57 V Γ) where
  /-- Full D19 linear-character equality for the trace representation. -/
  linearCharacter : D19ActsOnMoore57.D19LinearCharacterInput h
  /-- Rotation by `1` has exactly one fixed vertex. -/
  rotationOne_fixed_count : fixedVertexCount (h.rotation 1) = 1
  /-- Constructive enumeration of the selected 56 moved rotation orbits. -/
  orbitBase : OrbitBaseSelectionEnumeration h
  /-- Reflection-copy adjacent-moved partition over the selected bases. -/
  adjacentMoved :
    AdjacentMovedReflectionCopyPartition38Witness h orbitBase.base

namespace D19FinalLinearCountReflectionInputs

variable {h : D19ActsOnMoore57 V Γ}

/-- Convert exact fixed count `1` to the unique-fixed reflection boundary. -/
noncomputable def toD19FinalLinearUniqueReflectionInputs
    (data : D19FinalLinearCountReflectionInputs h) :
    D19FinalLinearUniqueReflectionInputs h where
  linearCharacter := data.linearCharacter
  rotationOne_unique_fixed :=
    h.existsUnique_rotation_one_fixed_of_fixedVertexCount_eq_one
      data.rotationOne_fixed_count
  orbitBase := data.orbitBase
  adjacentMoved := data.adjacentMoved

/-- Forget to the existing linear-character and unique-fixed constructive
boundary. -/
noncomputable def toD19ConstructiveFinalLinearUniqueInputs
    (data : D19FinalLinearCountReflectionInputs h) :
    D19ConstructiveFinalLinearUniqueInputs h :=
  data.toD19FinalLinearUniqueReflectionInputs
    |>.toD19ConstructiveFinalLinearUniqueInputs

/-- Forget to the constructive final input boundary. -/
noncomputable def toD19ConstructiveFinalInputs
    (data : D19FinalLinearCountReflectionInputs h) :
    D19ConstructiveFinalInputs h :=
  data.toD19FinalLinearUniqueReflectionInputs.toD19ConstructiveFinalInputs

/-- Forget to the final input boundary. -/
noncomputable def toD19FinalInputs
    (data : D19FinalLinearCountReflectionInputs h) :
    D19FinalInputs h :=
  data.toD19FinalLinearUniqueReflectionInputs.toD19FinalInputs

/-- Final linear-character, exact-count, reflection-copy inputs cannot exist. -/
theorem not_nonempty (h : D19ActsOnMoore57 V Γ) :
    ¬ Nonempty (D19FinalLinearCountReflectionInputs h) := by
  rintro ⟨data⟩
  exact D19FinalLinearUniqueReflectionInputs.not_nonempty h
    ⟨data.toD19FinalLinearUniqueReflectionInputs⟩

end D19FinalLinearCountReflectionInputs

/-- Variant of the final linear-character reflection-copy inputs where the
fixed side is supplied as cardinality one of the fixed subtype. -/
structure D19FinalLinearCardReflectionInputs
    (h : D19ActsOnMoore57 V Γ) where
  /-- Full D19 linear-character equality for the trace representation. -/
  linearCharacter : D19ActsOnMoore57.D19LinearCharacterInput h
  /-- The fixed subtype for rotation by `1` has cardinality one. -/
  rotationOne_fixed_card : Fintype.card (fixedVertexSet (h.rotation 1)) = 1
  /-- Constructive enumeration of the selected 56 moved rotation orbits. -/
  orbitBase : OrbitBaseSelectionEnumeration h
  /-- Reflection-copy adjacent-moved partition over the selected bases. -/
  adjacentMoved :
    AdjacentMovedReflectionCopyPartition38Witness h orbitBase.base

namespace D19FinalLinearCardReflectionInputs

variable {h : D19ActsOnMoore57 V Γ}

/-- Convert fixed-subtype cardinality `1` to the exact-count reflection
boundary. -/
noncomputable def toD19FinalLinearCountReflectionInputs
    (data : D19FinalLinearCardReflectionInputs h) :
    D19FinalLinearCountReflectionInputs h where
  linearCharacter := data.linearCharacter
  rotationOne_fixed_count := by
    simpa [fixedVertexCount_eq_card_fixedVertexSet] using
      data.rotationOne_fixed_card
  orbitBase := data.orbitBase
  adjacentMoved := data.adjacentMoved

/-- Convert fixed-subtype cardinality `1` to the unique-fixed reflection
boundary. -/
noncomputable def toD19FinalLinearUniqueReflectionInputs
    (data : D19FinalLinearCardReflectionInputs h) :
    D19FinalLinearUniqueReflectionInputs h :=
  data.toD19FinalLinearCountReflectionInputs.toD19FinalLinearUniqueReflectionInputs

/-- Forget to the existing linear-character and unique-fixed constructive
boundary. -/
noncomputable def toD19ConstructiveFinalLinearUniqueInputs
    (data : D19FinalLinearCardReflectionInputs h) :
    D19ConstructiveFinalLinearUniqueInputs h :=
  data.toD19FinalLinearCountReflectionInputs
    |>.toD19ConstructiveFinalLinearUniqueInputs

/-- Forget to the constructive final input boundary. -/
noncomputable def toD19ConstructiveFinalInputs
    (data : D19FinalLinearCardReflectionInputs h) :
    D19ConstructiveFinalInputs h :=
  data.toD19FinalLinearCountReflectionInputs.toD19ConstructiveFinalInputs

/-- Forget to the final input boundary. -/
noncomputable def toD19FinalInputs
    (data : D19FinalLinearCardReflectionInputs h) :
    D19FinalInputs h :=
  data.toD19FinalLinearCountReflectionInputs.toD19FinalInputs

/-- Final linear-character, fixed-cardinality, reflection-copy inputs cannot
exist. -/
theorem not_nonempty (h : D19ActsOnMoore57 V Γ) :
    ¬ Nonempty (D19FinalLinearCardReflectionInputs h) := by
  rintro ⟨data⟩
  exact D19FinalLinearCountReflectionInputs.not_nonempty h
    ⟨data.toD19FinalLinearCountReflectionInputs⟩

end D19FinalLinearCardReflectionInputs

end Moore57

/-!
# Final D19 inputs from exact fixed count and constant residual

This file packages the final contradiction input where the linear-character
side is paired with the exact count `fixedVertexCount (h.rotation 1) = 1`,
and the adjacent-moved side is supplied by the constant-residual
reflection-copy criterion.
-/

namespace Moore57

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- Final D19 input package using the linear-character criterion, exact
rotation-one fixed count `1`, an orbit-base enumeration, and the
constant-residual reflection-copy adjacent-moved partition. -/
structure D19FinalLinearCountConstantResidualInputs
    (h : D19ActsOnMoore57 V Γ) where
  /-- Full D19 linear-character witness for the trace representation. -/
  linearCharacter : D19ActsOnMoore57.D19LinearCharacterInput h
  /-- Rotation by `1` fixes exactly one vertex. -/
  rotationOne_fixed_count : fixedVertexCount (h.rotation 1) = 1
  /-- Constructive enumeration of the selected 56 moved rotation orbits. -/
  orbitBase : OrbitBaseSelectionEnumeration h
  /-- Constant-residual reflection-copy adjacent-moved partition over the
  selected bases. -/
  adjacentMoved :
    AdjacentMovedReflectionConstantResidual38Witness h orbitBase.base

namespace D19FinalLinearCountConstantResidualInputs

variable {h : D19ActsOnMoore57 V Γ}

/-- Convert exact count and constant-residual data to the existing
linear-character, unique-fixed, reflection-copy final boundary. -/
noncomputable def toD19FinalLinearUniqueReflectionInputs
    (data : D19FinalLinearCountConstantResidualInputs h) :
    D19FinalLinearUniqueReflectionInputs h where
  linearCharacter := data.linearCharacter
  rotationOne_unique_fixed :=
    h.existsUnique_rotation_one_fixed_of_fixedVertexCount_eq_one
      data.rotationOne_fixed_count
  orbitBase := data.orbitBase
  adjacentMoved := data.adjacentMoved.toReflectionCopyPartition38Witness

/-- Forget the constant-residual and exact-count presentations to the existing
linear-character and unique-fixed constructive boundary. -/
noncomputable def toD19ConstructiveFinalLinearUniqueInputs
    (data : D19FinalLinearCountConstantResidualInputs h) :
    D19ConstructiveFinalLinearUniqueInputs h :=
  data.toD19FinalLinearUniqueReflectionInputs
    |>.toD19ConstructiveFinalLinearUniqueInputs

/-- Forget the specialized boundaries down to constructive final inputs. -/
noncomputable def toD19ConstructiveFinalInputs
    (data : D19FinalLinearCountConstantResidualInputs h) :
    D19ConstructiveFinalInputs h :=
  data.toD19FinalLinearUniqueReflectionInputs.toD19ConstructiveFinalInputs

/-- Forget all specialized boundaries down to final inputs. -/
noncomputable def toD19FinalInputs
    (data : D19FinalLinearCountConstantResidualInputs h) :
    D19FinalInputs h :=
  data.toD19FinalLinearUniqueReflectionInputs.toD19FinalInputs

/-- Cardinality-one fixed set variant of the exact-count input constructor. -/
noncomputable def of_fixedVertexSet_card_eq_one
    (linearCharacter : D19ActsOnMoore57.D19LinearCharacterInput h)
    (rotationOne_fixed_card :
      Fintype.card (fixedVertexSet (h.rotation 1)) = 1)
    (orbitBase : OrbitBaseSelectionEnumeration h)
    (adjacentMoved :
      AdjacentMovedReflectionConstantResidual38Witness h orbitBase.base) :
    D19FinalLinearCountConstantResidualInputs h where
  linearCharacter := linearCharacter
  rotationOne_fixed_count := by
    simpa [fixedVertexCount_eq_card_fixedVertexSet] using rotationOne_fixed_card
  orbitBase := orbitBase
  adjacentMoved := adjacentMoved

/-- Final inputs in the linear-character, exact-count, constant-residual
reflection-copy form cannot exist. -/
theorem not_nonempty (h : D19ActsOnMoore57 V Γ) :
    ¬ Nonempty (D19FinalLinearCountConstantResidualInputs h) := by
  rintro ⟨data⟩
  exact D19FinalLinearUniqueReflectionInputs.not_nonempty h
    ⟨data.toD19FinalLinearUniqueReflectionInputs⟩

end D19FinalLinearCountConstantResidualInputs

end Moore57

