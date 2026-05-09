import Moore57.D19FinalRepresentationUpperBoundCompact
import Moore57.AdjacentMovedReflectionCompactSplit

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
