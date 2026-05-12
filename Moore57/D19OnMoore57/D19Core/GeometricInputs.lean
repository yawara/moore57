import Moore57.D19OnMoore57.D19Core.ReducedMain
import Moore57.D19OnMoore57.Orbit.BaseSelectionInputs
import Moore57.D19OnMoore57.AdjacentMoved.PartitionContribution
import Moore57.D19OnMoore57.Rotation.FixedUpperBoundInputs

/-!
# Higher-level geometric inputs for the D19 contradiction

This file packages the geometric and trace inputs that remain after the
reduced D19 contradiction pipeline has been isolated.  Constructing this single
record from an actual graph action is enough to invoke the reduced
contradiction.
-/

namespace Moore57

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- Higher-level D19 inputs combining the currently separated trace, orbit-base,
and adjacent-moved contribution data.

The fields are intentionally close to the remaining geometric tasks: choose the
56 moved rotation-orbit bases, identify the fixed/`A` contribution, and prove
the adjacent-moved decomposition over those bases. -/
structure D19GeometricInputs (h : D19ActsOnMoore57 V Γ) where
  /-- Coarse trace-character input for the action. -/
  characterInput : D19ActsOnMoore57.D19CharacterInput h
  /-- Selection of the 56 moved rotation-orbit bases. -/
  orbitBase : OrbitBaseSelectionInput h
  /-- Contribution from the fixed vertices and the `A`-side part. -/
  fixedOrAContribution : ZMod 19 → ℕ
  /-- The fixed/`A`-side contribution is `38` for nontrivial rotations. -/
  fixed_or_A_contribution :
    ∀ d : ZMod 19, d ≠ 0 → fixedOrAContribution d = 38
  /-- Adjacent-moved decomposition using the selected orbit bases. -/
  adjacentMovedDecomposition :
    D19AdjacentMovedDecomposition h orbitBase.base fixedOrAContribution

namespace D19GeometricInputs

variable {h : D19ActsOnMoore57 V Γ}

/-- Forget the higher-level geometric packaging down to the reduced hypotheses
used by the existing contradiction pipeline. -/
noncomputable def toD19ReducedHypotheses
    (data : D19GeometricInputs h) :
    D19ReducedHypotheses h where
  characterInput := data.characterInput
  base := data.orbitBase.base
  base_moved := data.orbitBase.base_moved
  fixedOrAContribution := data.fixedOrAContribution
  fixed_or_A_contribution := data.fixed_or_A_contribution
  a1_decomposition := data.adjacentMovedDecomposition.a1_decomposition

/-- The higher-level D19 geometric inputs cannot exist. -/
theorem not_nonempty (h : D19ActsOnMoore57 V Γ) :
    ¬ Nonempty (D19GeometricInputs h) := by
  rintro ⟨data⟩
  exact D19ReducedHypotheses.not_nonempty h
    ⟨data.toD19ReducedHypotheses⟩

end D19GeometricInputs

end Moore57
