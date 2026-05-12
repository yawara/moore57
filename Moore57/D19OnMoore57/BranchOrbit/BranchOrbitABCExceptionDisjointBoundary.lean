import Moore57.D19OnMoore57.BranchOrbit.BranchOrbitABCAFixingReflectionSupportBoundary
import Moore57.D19OnMoore57.BranchOrbit.BranchOrbitABCSupportComplementSumBoundary

/-!
# Midpoint exceptions disjoint from the A-fixing support

This file isolates the remaining natural-language boundary near Lemmas 6.3/6.4:
the midpoint exception set on the reference fiber is disjoint from the moving
support of the A-fixing reflection.  From that boundary, the midpoint
exception points are fixed by the reference matching-rotation permutation.

The direct geometric disjointness is left as an explicit boundary field.  The
finite-set consequences are formal: it gives the local lower bound
`2 ≤ supportᶜ.card`, and together with the existing reference-matching upper
bound it gives the exact two fixed points on the reference fiber.
-/

namespace Moore57

open Finset

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

local instance instExceptionDisjointBoundaryPFintype
    {h : D19ActsOnMoore57 V Γ}
    (labeling : BranchOrbitABCReflectionLabeling h) :
    Fintype labeling.data.toAFiberCoordinates.P :=
  labeling.data.toAFiberCoordinates.P_fintype

local instance instExceptionDisjointBoundaryDecidableEq
    (α : Type*) : DecidableEq α :=
  Classical.decEq α

namespace BranchOrbitABCReflectionLabeling

variable {h : D19ActsOnMoore57 V Γ}

/-- Boundary form of the natural-language disjointness statement: the midpoint
exception set `S_{d/2}` on the reference fiber is disjoint from the moving
support of the A-fixing reflection. -/
structure MidpointExceptionDisjointAFixingSupportBoundary
    (labeling : BranchOrbitABCReflectionLabeling h) : Prop where
  midpointException_disjoint_aFiberReflectionSupport :
    ∀ d : ZMod 19, ∀ hd : d ≠ 0,
      Disjoint
        (labeling.midpointExceptionSet (midpointOf d)
          (midpointOf_ne_zero hd))
        labeling.aFiberReflectionSupport

namespace MidpointExceptionDisjointAFixingSupportBoundary

variable {labeling : BranchOrbitABCReflectionLabeling h}

/-- Pointwise form of the disjointness boundary. -/
theorem not_mem_aFiberReflectionSupport_of_mem_midpointException
    (boundary : MidpointExceptionDisjointAFixingSupportBoundary labeling)
    {d : ZMod 19} (hd : d ≠ 0)
    {p : labeling.data.toAFiberCoordinates.P}
    (hp :
      p ∈ labeling.midpointExceptionSet (midpointOf d)
        (midpointOf_ne_zero hd)) :
    p ∉ labeling.aFiberReflectionSupport := by
  exact fun hpSupport =>
    (Finset.disjoint_left.mp
      (boundary.midpointException_disjoint_aFiberReflectionSupport d hd))
      hp hpSupport

/-- A midpoint-exception point is fixed by the A-fixing reflection on reference
coordinates, provided it is disjoint from the A-fixing moving support. -/
theorem aFiberReflectionCoordPerm_eq_self_of_mem_midpointException
    (boundary : MidpointExceptionDisjointAFixingSupportBoundary labeling)
    {d : ZMod 19} (hd : d ≠ 0)
    {p : labeling.data.toAFiberCoordinates.P}
    (hp :
      p ∈ labeling.midpointExceptionSet (midpointOf d)
        (midpointOf_ne_zero hd)) :
    labeling.aFiberReflectionCoordPerm p = p := by
  classical
  by_contra hne
  exact
    boundary.not_mem_aFiberReflectionSupport_of_mem_midpointException hd hp
      ((labeling.mem_aFiberReflectionSupport p).2 hne)

/-- Under the midpoint criterion and the disjointness boundary, each midpoint
exception point `S_{d/2}` is fixed by the reference matching-rotation
permutation for offset `d`. -/
theorem midpointExceptionSet_subset_reference_matching_supportCompl
    (boundary : MidpointExceptionDisjointAFixingSupportBoundary labeling)
    (criterion : MidpointReflectionCriterionBoundary labeling)
    (d : ZMod 19) (hd : d ≠ 0) :
    labeling.midpointExceptionSet (midpointOf d) (midpointOf_ne_zero hd) ⊆
      (labeling.data.toAFiberRotationEquivariance.matchingRotationPerm
        d 0 hd).supportᶜ := by
  classical
  intro p hp
  let m : ZMod 19 := midpointOf d
  have hm : m ≠ 0 := midpointOf_ne_zero hd
  have hpEq : p ∈ labeling.midpointEquationSet m hm :=
    (criterion.midpoint_equation_iff_exception m hm p).2 hp
  have hmatch_mid :
      AFiberCoordinates.matchingEquiv h.isMoore
          labeling.data.toAFiberCoordinates 0 (0 + (m + m))
          (index_ne_add_of_ne_zero (add_self_ne_zero_zmod19 hm)) p =
        labeling.midpointReflectionCoordPerm m p :=
    (labeling.mem_midpointEquationSet m hm p).1 hpEq
  have hAFixed : labeling.aFiberReflectionCoordPerm p = p :=
    boundary.aFiberReflectionCoordPerm_eq_self_of_mem_midpointException hd hp
  have hrot_mid :
      labeling.data.toAFiberRotationEquivariance.coordPerm d 0 p =
        labeling.midpointReflectionCoordPerm m p := by
    simpa [m] using
      (labeling.rotationCoordPerm_eq_midpointReflectionCoordPerm_midpointOf_iff
        d p).2 hAFixed
  have hmatch_rot :
      AFiberCoordinates.matchingEquiv h.isMoore
          labeling.data.toAFiberCoordinates 0 (0 + d)
          (index_ne_add_of_ne_zero hd) p =
        labeling.data.toAFiberRotationEquivariance.coordPerm d 0 p := by
    have hdd : m + m = d := by
      simpa [m] using midpointOf_add_self d
    simpa [hdd] using hmatch_mid.trans hrot_mid.symm
  exact
    (AFiberRotationEquivariance.mem_matchingRotationPerm_support_compl_iff
      labeling.data.toAFiberRotationEquivariance d 0 hd p).2 hmatch_rot

/-- The disjointness boundary gives the reference-fiber lower bound
`2 ≤ supportᶜ.card`: the two midpoint-exception points are fixed by the
matching-rotation permutation. -/
theorem reference_matching_supportCompl_card_ge_two
    (boundary : MidpointExceptionDisjointAFixingSupportBoundary labeling)
    (criterion : MidpointReflectionCriterionBoundary labeling)
    (cardTwo : MidpointMiddleSupportCardTwoBoundary labeling)
    (d : ZMod 19) (hd : d ≠ 0) :
    2 ≤
      (labeling.data.toAFiberRotationEquivariance.matchingRotationPerm
        d 0 hd).supportᶜ.card := by
  classical
  calc
    2 =
        (labeling.midpointExceptionSet (midpointOf d)
          (midpointOf_ne_zero hd)).card := by
          rw [cardTwo.midpointExceptionSet_card_two
            (midpointOf d) (midpointOf_ne_zero hd)]
    _ ≤
        (labeling.data.toAFiberRotationEquivariance.matchingRotationPerm
          d 0 hd).supportᶜ.card :=
          Finset.card_le_card
            (boundary.midpointExceptionSet_subset_reference_matching_supportCompl
              criterion d hd)

/-- Transport the reference-fiber lower bound to every A-fiber by rotation
invariance, producing the existing support-complement-sum boundary. -/
noncomputable def toAllFibersSupportComplementAtLeastTwoBoundary
    (boundary : MidpointExceptionDisjointAFixingSupportBoundary labeling)
    (criterion : MidpointReflectionCriterionBoundary labeling)
    (cardTwo : MidpointMiddleSupportCardTwoBoundary labeling) :
    AllFibersSupportComplementAtLeastTwoBoundary labeling where
  supportCompl_card_ge_two := by
    intro d hd i
    calc
      2 ≤
          (labeling.data.toAFiberRotationEquivariance.matchingRotationPerm
            d 0 hd).supportᶜ.card :=
            boundary.reference_matching_supportCompl_card_ge_two
              criterion cardTwo d hd
      _ =
          (labeling.data.toAFiberRotationEquivariance.matchingRotationPerm
            d i hd).supportᶜ.card := by
            simpa using
              labeling.data.toAFiberRotationEquivariance
                |>.matchingRotationPerm_support_compl_card_eq_shift
                  d 0 i hd

/-- Combining the disjointness lower bound with the existing reference-matching
upper bound gives exactly two fixed coordinates on the reference fiber. -/
theorem reference_matching_supportCompl_card_eq_two
    (boundary : MidpointExceptionDisjointAFixingSupportBoundary labeling)
    (referenceMatching : ReferenceMatchingPipelineBoundary labeling)
    (d : ZMod 19) (hd : d ≠ 0) :
    (labeling.data.toAFiberRotationEquivariance.matchingRotationPerm
      d 0 hd).supportᶜ.card = 2 := by
  exact le_antisymm
    (referenceMatching.toReferenceFiberMatchingExceptionSetTwo
      |>.referenceMatchingSupportCompl_card_le_two d hd)
    (boundary.reference_matching_supportCompl_card_ge_two
      referenceMatching.criterion referenceMatching.midpointSupportCardTwo d hd)

/-- Exact two fixed coordinates in every A-fiber, obtained from the reference
fiber equality and rotation invariance. -/
theorem matching_supportCompl_card_eq_two
    (boundary : MidpointExceptionDisjointAFixingSupportBoundary labeling)
    (referenceMatching : ReferenceMatchingPipelineBoundary labeling)
    (d : ZMod 19) (hd : d ≠ 0) (i : ZMod 19) :
    (labeling.data.toAFiberRotationEquivariance.matchingRotationPerm
      d i hd).supportᶜ.card = 2 := by
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
              |>.matchingRotationPerm_support_compl_card_eq_shift d 0 i hd).symm
    _ = 2 :=
        boundary.reference_matching_supportCompl_card_eq_two
          referenceMatching d hd

/-- Convenience constructor for the existing local support-complement lower
bound, using the bundled reference-matching pipeline for the midpoint
criterion and two-point midpoint support fields. -/
noncomputable def toAllFibersSupportComplementAtLeastTwoBoundary_of_referenceMatching
    (boundary : MidpointExceptionDisjointAFixingSupportBoundary labeling)
    (referenceMatching : ReferenceMatchingPipelineBoundary labeling) :
    AllFibersSupportComplementAtLeastTwoBoundary labeling :=
  boundary.toAllFibersSupportComplementAtLeastTwoBoundary
    referenceMatching.criterion referenceMatching.midpointSupportCardTwo

/-- Feed the disjointness boundary into the full reference matching cardinality
pipeline. -/
noncomputable def toReferenceMatchingCardinalityPipelineBoundary
    (boundary : MidpointExceptionDisjointAFixingSupportBoundary labeling)
    (referenceMatching : ReferenceMatchingPipelineBoundary labeling) :
    ReferenceMatchingCardinalityPipelineBoundary labeling :=
  AllFibersSupportComplementAtLeastTwoBoundary.toReferenceMatchingCardinalityPipelineBoundary
    referenceMatching
    (boundary.toAllFibersSupportComplementAtLeastTwoBoundary_of_referenceMatching
      referenceMatching)

end MidpointExceptionDisjointAFixingSupportBoundary

end BranchOrbitABCReflectionLabeling

end

end Moore57
