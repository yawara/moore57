import Moore57.D19OnMoore57.BranchOrbit.BranchOrbitABCReferenceMatchingPipeline

/-!
# Branch-orbit support-complement sum boundary

This file packages the remaining support-complement lower-bound input used by
the reference matching cardinality pipeline.  The useful boundary is local and
readable: every nonzero offset and every A-fiber contributes at least two
fixed matching coordinates.  Since there are nineteen A-fibers, this implies
the required total lower bound `supportCompl_sum_ge`.
-/

namespace Moore57

open Finset

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

local instance instSupportComplementSumBoundaryPFintype
    {h : D19ActsOnMoore57 V Γ}
    (labeling : BranchOrbitABCReflectionLabeling h) :
    Fintype labeling.data.toAFiberCoordinates.P :=
  labeling.data.toAFiberCoordinates.P_fintype

local instance instSupportComplementSumBoundaryDecidableEq
    (α : Type*) : DecidableEq α :=
  Classical.decEq α

namespace BranchOrbitABCReflectionLabeling

variable {h : D19ActsOnMoore57 V Γ}

/-- Local lower-bound boundary for the support-complement sum: every nonzero
matching offset contributes at least two fixed matching coordinates in every
A-fiber. -/
structure AllFibersSupportComplementAtLeastTwoBoundary
    (labeling : BranchOrbitABCReflectionLabeling h) : Prop where
  supportCompl_card_ge_two :
    ∀ d : ZMod 19, ∀ hd : d ≠ 0, ∀ i : ZMod 19,
      2 ≤
        (labeling.data.toAFiberRotationEquivariance.matchingRotationPerm
          d i hd).supportᶜ.card

namespace AllFibersSupportComplementAtLeastTwoBoundary

variable {labeling : BranchOrbitABCReflectionLabeling h}

/-- The local lower-bound boundary implies the aggregate lower bound consumed
by `ReferenceMatchingCardinalityPipelineBoundary`. -/
theorem supportCompl_sum_ge
    (boundary : AllFibersSupportComplementAtLeastTwoBoundary labeling) :
    ∀ d : ZMod 19, ∀ hd : d ≠ 0,
      38 ≤
        ∑ i ∈ (Finset.univ : Finset (ZMod 19)),
          (labeling.data.toAFiberRotationEquivariance.matchingRotationPerm
            d i hd).supportᶜ.card := by
  intro d hd
  calc
    38 = ∑ i ∈ (Finset.univ : Finset (ZMod 19)), 2 := by
      rw [Finset.sum_const, zmod19_univ_card]
      norm_num
    _ ≤
        ∑ i ∈ (Finset.univ : Finset (ZMod 19)),
          (labeling.data.toAFiberRotationEquivariance.matchingRotationPerm
            d i hd).supportᶜ.card := by
      refine Finset.sum_le_sum ?_
      intro i _hi
      exact boundary.supportCompl_card_ge_two d hd i

/-- Build the local lower-bound boundary from exact two fixed matching
coordinates in every fiber. -/
noncomputable def of_allFibers_matchingRotationPerm_support_compl_card_eq_two
    (hfixed :
      ∀ d : ZMod 19, ∀ hd : d ≠ 0, ∀ i : ZMod 19,
        (labeling.data.toAFiberRotationEquivariance.matchingRotationPerm
          d i hd).supportᶜ.card = 2) :
    AllFibersSupportComplementAtLeastTwoBoundary labeling where
  supportCompl_card_ge_two := by
    intro d hd i
    rw [hfixed d hd i]

/-- Build the local lower-bound boundary by checking exact two fixed matching
coordinates on the reference fiber `0`; rotation invariance carries the count
to every fiber. -/
noncomputable def of_referenceFiber_matchingRotationPerm_support_compl_card_eq_two
    (hfixed_zero :
      ∀ d : ZMod 19, ∀ hd : d ≠ 0,
        (labeling.data.toAFiberRotationEquivariance.matchingRotationPerm
          d 0 hd).supportᶜ.card = 2) :
    AllFibersSupportComplementAtLeastTwoBoundary labeling :=
  of_allFibers_matchingRotationPerm_support_compl_card_eq_two (by
    intro d hd i
    calc
      (labeling.data.toAFiberRotationEquivariance.matchingRotationPerm
          d i hd).supportᶜ.card =
          (labeling.data.toAFiberRotationEquivariance.matchingRotationPerm
            d (0 + i) hd).supportᶜ.card := by
            simp
      _ =
          (labeling.data.toAFiberRotationEquivariance.matchingRotationPerm
            d 0 hd).supportᶜ.card := by
            exact
              (labeling.data.toAFiberRotationEquivariance
                |>.matchingRotationPerm_support_compl_card_eq_shift
                  d 0 i hd).symm
      _ = 2 := hfixed_zero d hd)

/-- Package reference matching data together with this local lower-bound
boundary into the pipeline input expected by
`ReferenceMatchingCardinalityPipelineBoundary.toAFiberCardinality38Boundary`. -/
noncomputable def toReferenceMatchingCardinalityPipelineBoundary
    (referenceMatching : ReferenceMatchingPipelineBoundary labeling)
    (boundary : AllFibersSupportComplementAtLeastTwoBoundary labeling) :
    ReferenceMatchingCardinalityPipelineBoundary labeling where
  referenceMatching := referenceMatching
  supportCompl_sum_ge := boundary.supportCompl_sum_ge

end AllFibersSupportComplementAtLeastTwoBoundary

/-- Direct constructor for the cardinality pipeline boundary from the local
per-fiber support-complement lower bound. -/
noncomputable def toReferenceMatchingCardinalityPipelineBoundary_of_supportCompl_card_ge_two
    (labeling : BranchOrbitABCReflectionLabeling h)
    (referenceMatching : ReferenceMatchingPipelineBoundary labeling)
    (hge_two :
      ∀ d : ZMod 19, ∀ hd : d ≠ 0, ∀ i : ZMod 19,
        2 ≤
          (labeling.data.toAFiberRotationEquivariance.matchingRotationPerm
            d i hd).supportᶜ.card) :
    ReferenceMatchingCardinalityPipelineBoundary labeling :=
  AllFibersSupportComplementAtLeastTwoBoundary.toReferenceMatchingCardinalityPipelineBoundary
    referenceMatching
    ⟨hge_two⟩

/-- Direct constructor for the cardinality pipeline boundary from exact two
fixed matching coordinates in every fiber. -/
noncomputable def toReferenceMatchingCardinalityPipelineBoundary_of_supportCompl_card_eq_two
    (labeling : BranchOrbitABCReflectionLabeling h)
    (referenceMatching : ReferenceMatchingPipelineBoundary labeling)
    (hfixed :
      ∀ d : ZMod 19, ∀ hd : d ≠ 0, ∀ i : ZMod 19,
        (labeling.data.toAFiberRotationEquivariance.matchingRotationPerm
          d i hd).supportᶜ.card = 2) :
    ReferenceMatchingCardinalityPipelineBoundary labeling :=
  AllFibersSupportComplementAtLeastTwoBoundary.toReferenceMatchingCardinalityPipelineBoundary
    referenceMatching
    (AllFibersSupportComplementAtLeastTwoBoundary.of_allFibers_matchingRotationPerm_support_compl_card_eq_two
        (labeling := labeling) hfixed)

/-- Direct constructor for the cardinality pipeline boundary from exact two
fixed matching coordinates on the reference fiber `0`; rotation invariance
fills the remaining fibers. -/
noncomputable def toReferenceMatchingCardinalityPipelineBoundary_of_referenceFiber_supportCompl_card_eq_two
    (labeling : BranchOrbitABCReflectionLabeling h)
    (referenceMatching : ReferenceMatchingPipelineBoundary labeling)
    (hfixed_zero :
      ∀ d : ZMod 19, ∀ hd : d ≠ 0,
        (labeling.data.toAFiberRotationEquivariance.matchingRotationPerm
          d 0 hd).supportᶜ.card = 2) :
    ReferenceMatchingCardinalityPipelineBoundary labeling :=
  AllFibersSupportComplementAtLeastTwoBoundary.toReferenceMatchingCardinalityPipelineBoundary
    referenceMatching
    (AllFibersSupportComplementAtLeastTwoBoundary.of_referenceFiber_matchingRotationPerm_support_compl_card_eq_two
        (labeling := labeling) hfixed_zero)

end BranchOrbitABCReflectionLabeling

end

end Moore57
