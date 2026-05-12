import Moore57.D19OnMoore57.Final.Inputs
import Moore57.D19OnMoore57.Misc.CharacterInputPackaging
import Moore57.D19OnMoore57.Orbit.BaseSelectionInputBridge
import Moore57.D19OnMoore57.AdjacentMoved.ReflectionCompactCriteria

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
