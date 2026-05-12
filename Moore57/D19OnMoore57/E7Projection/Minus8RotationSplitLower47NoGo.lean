import Moore57.D19OnMoore57.E7Projection.Minus8CharacterBoundariesFromRotationSplit
import Moore57.D19OnMoore57.LinearCharacter.Nonempty

/-!
# Rotation-split no-go from the trace-refined reflection lower bound

The representation-theoretic part is now supplied directly by the rotation
split for the concrete E7 and `(-8)` projection representations.  Therefore
the current final-gap no-go needs only the remaining reflection fixed-count
lower bound `47`, which the trace-refined candidate list upgrades to the
paper count `56`.
-/

namespace Moore57

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

namespace D19ActsOnMoore57

/-- Rotation-split character construction plus one per-reflection lower bound
`fixedVertexCount ≥ 47` rules out the current final-gap boundary. -/
theorem no_currentFinalGapBoundary_of_rotation_split_and_reflectionFixedCount_ge_fortySeven
    (h : D19ActsOnMoore57 V Γ)
    {dt : ZMod 19}
    (hlower :
      47 ≤ fixedVertexCount (h.smulEquiv (DihedralGroup.sr dt))) :
    ¬ Nonempty (BranchOrbitABCCurrentFinalGapBoundary h) :=
  no_D19_currentFinalGapBoundary_of_nonempty_linearCharacterInput h
    (h.nonempty_d19LinearCharacterInput_of_rotation_split_and_reflectionFixedCount_ge_fortySeven
      hlower)

/-- Uniform lower-bound package version of
`no_currentFinalGapBoundary_of_rotation_split_and_reflectionFixedCount_ge_fortySeven`. -/
theorem no_currentFinalGapBoundary_of_rotation_split_and_reflectionFixedCountLower47
    (h : D19ActsOnMoore57 V Γ)
    (bounds : ReflectionFixedCountLower47 h)
    (dt : ZMod 19) :
    ¬ Nonempty (BranchOrbitABCCurrentFinalGapBoundary h) :=
  h.no_currentFinalGapBoundary_of_rotation_split_and_reflectionFixedCount_ge_fortySeven
    (bounds.lower dt)

end D19ActsOnMoore57

end

end Moore57
