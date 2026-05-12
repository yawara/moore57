import Moore57.D19OnMoore57.Final.D19FinalInputs
import Moore57.D19OnMoore57.Misc.CharacterInputPackaging
import Moore57.D19OnMoore57.Rotation.RotationFixedCountUnique
import Moore57.D19OnMoore57.Orbit.OrbitBaseSelectionInputBridge
import Moore57.D19OnMoore57.AdjacentMoved.AdjacentMovedReflectionConstantResidual

/-!
# Final D19 inputs from representation data and constant residual

This file records the current final boundary without requiring a full
class-character equality on every element of `D19`: the downstream contradiction
only uses the representation-character input on nontrivial rotations.
-/

namespace Moore57

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- Final D19 input package using representation-character data, exact
rotation-one fixed count, downstream base-selection input, and a
constant-residual reflection-copy adjacent-moved partition. -/
structure D19FinalRepresentationCountConstantResidualBaseInputs
    (h : D19ActsOnMoore57 V Γ) where
  /-- Representation-theoretic multiplicities and nontrivial rotation
  character values. -/
  representation : D19ActsOnMoore57.D19RepresentationCharacterInput h
  /-- Rotation by `1` has exactly one fixed vertex. -/
  rotationOne_fixed_count : fixedVertexCount (h.rotation 1) = 1
  /-- Pairwise-disjoint selected moved rotation orbits. -/
  orbitBase : OrbitBaseSelectionInput h
  /-- Constant-residual reflection-copy adjacent-moved partition over the
  selected bases. -/
  adjacentMoved :
    AdjacentMovedReflectionConstantResidual38Witness h orbitBase.base

namespace D19FinalRepresentationCountConstantResidualBaseInputs

variable {h : D19ActsOnMoore57 V Γ}

/-- Convert the representation and fixed-count inputs into the split final
character input. -/
noncomputable def toD19FinalCharacterInputs
    (data : D19FinalRepresentationCountConstantResidualBaseInputs h) :
    D19FinalCharacterInputs h where
  representation := data.representation
  fixedUpperBound :=
    D19ActsOnMoore57.RotationFixedUpperBoundInput.of_rotation_one_fixedVertexCount_eq_one
      h data.rotationOne_fixed_count

/-- Forget the specialized boundary down to the final input record. -/
noncomputable def toD19FinalInputs
    (data : D19FinalRepresentationCountConstantResidualBaseInputs h) :
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

/-- Final representation-character, exact-count, constant-residual base inputs
cannot exist. -/
theorem not_nonempty (h : D19ActsOnMoore57 V Γ) :
    ¬ Nonempty (D19FinalRepresentationCountConstantResidualBaseInputs h) := by
  rintro ⟨data⟩
  exact D19FinalInputs.not_nonempty h ⟨data.toD19FinalInputs⟩

end D19FinalRepresentationCountConstantResidualBaseInputs

end Moore57
