import Moore57.D19OnMoore57.BranchOrbit.ABCReferenceMatchingPipeline
import Moore57.D19OnMoore57.D19Core.ReflectionLabeledBranchCompactSplitBoundary

/-!
# Fixed-star final bridge

This file wires the fixed-star/reference matching cardinality pipeline into
the reflection-labeled compact-split boundary.
-/

namespace Moore57

open Finset

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

local instance instFixedStarFinalBridgePFintype
    {h : D19ActsOnMoore57 V Γ}
    (labeling : BranchOrbitABCReflectionLabeling h) :
    Fintype labeling.data.toAFiberCoordinates.P :=
  labeling.data.toAFiberCoordinates.P_fintype

local instance instFixedStarFinalBridgeDecidableEq
    (α : Type*) : DecidableEq α :=
  Classical.decEq α

namespace D19ReflectionLabeledBranchCompactSplitBoundaryInputs

variable {h : D19ActsOnMoore57 V Γ}

/-- Constructor from the fixed-star/reference matching cardinality pipeline. -/
noncomputable def ofFixedStarReferenceMatchingCardinalityPipeline
    (representationComponents :
      D19ActsOnMoore57.RepresentationCharacterComponentsBoundary h)
    (star : ReflectionFixedStarBoundary h)
    (labeling : BranchOrbitABCReflectionLabeling h)
    (boundary :
      BranchOrbitABCReflectionLabeling.FixedStarReferenceMatchingCardinalityPipelineBoundary
        star labeling) :
    D19ReflectionLabeledBranchCompactSplitBoundaryInputs h where
  representationComponents := representationComponents
  labeling := labeling
  aFiberCardinality := boundary.toAFiberCardinality38Boundary

/-- Constructor from a mathlib character class boundary and the fixed-star
reference matching cardinality pipeline. -/
noncomputable def ofCharacterClassBoundaryFixedStarReferenceMatchingCardinalityPipeline
    {W : Type*} [AddCommGroup W] [Module ℚ W] [FiniteDimensional ℚ W]
    (ρ : Representation ℚ (DihedralGroup 19) W)
    (alpha beta gamma : ℕ)
    (finrank_eq : Module.finrank ℚ W = 1729)
    (trace_eq_character :
      ∀ g : DihedralGroup 19,
        Matrix.trace (E7Matrix Γ * permMatrix (h.smulEquiv g)) =
          ρ.character g)
    (characterClass : D19CharacterClassBoundary ρ alpha beta gamma)
    (reflection : (alpha : ℤ) - (beta : ℤ) = 33)
    (minus8_trivial_nonneg : alpha ≤ 113)
    (minus8_sign_nonneg : beta ≤ 58)
    (star : ReflectionFixedStarBoundary h)
    (labeling : BranchOrbitABCReflectionLabeling h)
    (boundary :
      BranchOrbitABCReflectionLabeling.FixedStarReferenceMatchingCardinalityPipelineBoundary
        star labeling) :
    D19ReflectionLabeledBranchCompactSplitBoundaryInputs h :=
  ofFixedStarReferenceMatchingCardinalityPipeline
    (D19ActsOnMoore57.representationCharacterComponentsBoundary_of_representationCharacterClassBoundary
        h ρ alpha beta gamma finrank_eq trace_eq_character characterClass
        reflection minus8_trivial_nonneg minus8_sign_nonneg)
    star labeling boundary

end D19ReflectionLabeledBranchCompactSplitBoundaryInputs

/-- No fixed-star/reference matching cardinality pipeline can coexist with
the representation-character component boundary. -/
theorem no_D19_fixedStarReferenceMatchingCardinalityPipeline_boundary
    (h : D19ActsOnMoore57 V Γ) :
    ¬ ∃ _representationComponents :
          D19ActsOnMoore57.RepresentationCharacterComponentsBoundary h,
        ∃ star : ReflectionFixedStarBoundary h,
        ∃ labeling : BranchOrbitABCReflectionLabeling h,
          BranchOrbitABCReflectionLabeling.FixedStarReferenceMatchingCardinalityPipelineBoundary
            star labeling := by
  rintro ⟨representationComponents, star, labeling, boundary⟩
  exact no_D19_reflection_labeled_branch_compact_split_boundary h
    ⟨D19ReflectionLabeledBranchCompactSplitBoundaryInputs.ofFixedStarReferenceMatchingCardinalityPipeline
        representationComponents star labeling boundary⟩

/-- Character-class version of
`no_D19_fixedStarReferenceMatchingCardinalityPipeline_boundary`, with the
representation component boundary supplied by a mathlib representation. -/
theorem no_D19_characterClassBoundary_fixedStarReferenceMatchingCardinalityPipeline_boundary
    (h : D19ActsOnMoore57 V Γ)
    {W : Type*} [AddCommGroup W] [Module ℚ W] [FiniteDimensional ℚ W]
    (ρ : Representation ℚ (DihedralGroup 19) W)
    (alpha beta gamma : ℕ)
    (finrank_eq : Module.finrank ℚ W = 1729)
    (trace_eq_character :
      ∀ g : DihedralGroup 19,
        Matrix.trace (E7Matrix Γ * permMatrix (h.smulEquiv g)) =
          ρ.character g)
    (characterClass : D19CharacterClassBoundary ρ alpha beta gamma)
    (reflection : (alpha : ℤ) - (beta : ℤ) = 33)
    (minus8_trivial_nonneg : alpha ≤ 113)
    (minus8_sign_nonneg : beta ≤ 58) :
    ¬ ∃ star : ReflectionFixedStarBoundary h,
        ∃ labeling : BranchOrbitABCReflectionLabeling h,
          BranchOrbitABCReflectionLabeling.FixedStarReferenceMatchingCardinalityPipelineBoundary
            star labeling := by
  intro hpipeline
  rcases hpipeline with ⟨star, labeling, boundary⟩
  exact no_D19_fixedStarReferenceMatchingCardinalityPipeline_boundary h
    ⟨D19ActsOnMoore57.representationCharacterComponentsBoundary_of_representationCharacterClassBoundary
        h ρ alpha beta gamma finrank_eq trace_eq_character characterClass
        reflection minus8_trivial_nonneg minus8_sign_nonneg,
      star, labeling, boundary⟩

end

end Moore57
