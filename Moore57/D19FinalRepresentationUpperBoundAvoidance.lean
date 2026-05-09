import Moore57.D19FinalRepresentationUpperBoundCompact
import Moore57.AdjacentMovedReflectionAvoidanceCriteria

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
