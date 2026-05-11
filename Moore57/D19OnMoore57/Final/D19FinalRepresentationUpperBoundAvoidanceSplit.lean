import Moore57.D19OnMoore57.Final.D19FinalRepresentationUpperBoundAvoidance
import Moore57.D19OnMoore57.AdjacentMoved.AdjacentMovedReflectionAvoidanceSplit

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
