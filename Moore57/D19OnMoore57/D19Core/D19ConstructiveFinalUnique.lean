import Moore57.D19OnMoore57.D19Core.D19ConstructiveFinalInputs
import Moore57.D19OnMoore57.Misc.CharacterInputPackaging
import Moore57.D19OnMoore57.Rotation.RotationFixedUniqueCriteria

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
