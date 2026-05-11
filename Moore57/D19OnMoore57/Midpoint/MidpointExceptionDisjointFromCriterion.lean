import Moore57.D19OnMoore57.Midpoint.MidpointExceptionDoublingGeometryFromBridge
import Moore57.D19OnMoore57.BranchOrbit.BranchOrbitABCExceptionEquationInvariantBoundary
import Moore57.D19OnMoore57.BranchOrbit.BranchOrbitABCExceptionDisjointBoundary
import Moore57.D19OnMoore57.BranchOrbit.BranchOrbitABCMatchingTargetReflectionReduced
import Moore57.D19OnMoore57.BranchOrbit.BranchOrbitABCExceptionIntersectionInvariantDecomp
import Moore57.D19OnMoore57.BranchOrbit.BranchOrbitABCExceptionCardOneBoundary
import Moore57.D19OnMoore57.BranchOrbit.BranchOrbitABCExceptionCardTwoBoundary
import Moore57.D19OnMoore57.BranchOrbit.BranchOrbitABCExceptionCaseBoundary
import Moore57.Foundations.ZMod19.Lemmas

/-!
# `MidpointExceptionDisjointAFixingSupportBoundary` modulo the e=2 base witness

This file assembles the natural-language Lemma 6.3 chain into Lean:
1. The chain step `S_m ∩ E ⊆ S_{2m} ∩ E` (proved in
   `MidpointExceptionDoublingGeometryFromBridge`).
2. The (ℤ/19)\* cycling via `2` being a generator (`two_pow_eighteen_zmod19`).
3. The e=1 closure: `S_m ∩ E` is invariant under the A-fixing reflection.
4. From an e=2 base witness, the case boundary and the disjointness boundary.

The remaining input is the e=2 base witness — the natural-language
17-common-neighbor / μ=1 contradiction.  This is the only essential
mathematical content left to supply for Lemma 6.3.
-/

namespace Moore57

open Finset

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

local instance instMidpointExceptionDisjointPFintype
    {h : D19ActsOnMoore57 V Γ}
    (labeling : BranchOrbitABCReflectionLabeling h) :
    Fintype labeling.data.toAFiberCoordinates.P :=
  labeling.data.toAFiberCoordinates.P_fintype

local instance instMidpointExceptionDisjointDecidableEq
    (α : Type*) : DecidableEq α :=
  Classical.decEq α

namespace BranchOrbitABCReflectionLabeling

variable {h : D19ActsOnMoore57 V Γ}

/-- Helper: `midpointExceptionAFixingSupportIntersection` is invariant under
substituting equal indices. -/
private theorem midpointExceptionAFixingSupportIntersection_index_subst
    (labeling : BranchOrbitABCReflectionLabeling h)
    {d d' : ZMod 19} (hdd' : d = d') (hd : d ≠ 0) (hd' : d' ≠ 0) :
    labeling.midpointExceptionAFixingSupportIntersection d hd =
      labeling.midpointExceptionAFixingSupportIntersection d' hd' := by
  subst hdd'
  rfl

/-- Single-step set equality `S_d ∩ E = S_{2d} ∩ E`, derived from the chain
inclusion plus card equality. -/
theorem midpointExceptionAFixingSupportIntersection_eq_double_of_criterion
    (labeling : BranchOrbitABCReflectionLabeling h)
    (criterion : MidpointReflectionCriterionBoundary labeling)
    (d : ZMod 19) (hd : d ≠ 0) :
    labeling.midpointExceptionAFixingSupportIntersection d hd =
      labeling.midpointExceptionAFixingSupportIntersection
        ((2 : ZMod 19) * d) (two_mul_ne_zero_zmod19 hd) := by
  let boundary :=
    midpointExceptionDoublingBoundary_of_criterion labeling criterion
  apply Finset.eq_of_subset_of_card_le
  · exact boundary.double_subset d hd
  · rw [boundary.card_eq (two_mul_ne_zero_zmod19 hd) hd]

/-- Iterated `n`-step set equality. -/
theorem midpointExceptionAFixingSupportIntersection_eq_two_pow_of_criterion
    (labeling : BranchOrbitABCReflectionLabeling h)
    (criterion : MidpointReflectionCriterionBoundary labeling)
    (n : ℕ) {d : ZMod 19} (hd : d ≠ 0) :
    labeling.midpointExceptionAFixingSupportIntersection d hd =
      labeling.midpointExceptionAFixingSupportIntersection
        (((2 : ZMod 19) ^ n) * d) (two_pow_mul_ne_zero_zmod19 hd n) := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      have hcurrent : ((2 : ZMod 19) ^ n) * d ≠ 0 :=
        two_pow_mul_ne_zero_zmod19 hd n
      have hstep :=
        labeling.midpointExceptionAFixingSupportIntersection_eq_double_of_criterion
          criterion (((2 : ZMod 19) ^ n) * d) hcurrent
      have hidx :
          (2 : ZMod 19) * (((2 : ZMod 19) ^ n) * d) =
            ((2 : ZMod 19) ^ (n + 1)) * d := by
        rw [← mul_assoc, pow_succ]
        ring
      rw [ih, hstep]
      exact labeling.midpointExceptionAFixingSupportIntersection_index_subst
        hidx _ _

/-- Sign-flip set equality `S_d ∩ E = S_{-d} ∩ E` via `2^9 = -1` in
`(ℤ/19)`. -/
theorem midpointExceptionAFixingSupportIntersection_eq_neg_of_criterion
    (labeling : BranchOrbitABCReflectionLabeling h)
    (criterion : MidpointReflectionCriterionBoundary labeling)
    {d : ZMod 19} (hd : d ≠ 0) :
    labeling.midpointExceptionAFixingSupportIntersection d hd =
      labeling.midpointExceptionAFixingSupportIntersection (-d)
        (neg_ne_zero.mpr hd) := by
  have hpow :=
    labeling.midpointExceptionAFixingSupportIntersection_eq_two_pow_of_criterion
      criterion 9 hd
  have hidx :
      ((2 : ZMod 19) ^ 9) * d = -d := by
    rw [two_pow_nine_mul_zmod19]
  rw [hpow]
  exact labeling.midpointExceptionAFixingSupportIntersection_index_subst
    hidx _ _

/-- The chain + sign symmetry + θ-permutes-E give that the intersection
`S_(d/2) ∩ E` is invariant under the A-fixing coordinate reflection. -/
def midpointExceptionAFixingSupportIntersectionInvariantBoundary_of_criterion
    (labeling : BranchOrbitABCReflectionLabeling h)
    (criterion : MidpointReflectionCriterionBoundary labeling) :
    MidpointExceptionAFixingSupportIntersectionInvariantBoundary labeling where
  aFiberReflection_mem_intersection d hd p hp := by
    classical
    rcases (labeling.mem_midpointExceptionAFixingSupportIntersection
        (midpointOf d) (midpointOf_ne_zero hd) p).1 hp with
      ⟨hpException, hpSupport⟩
    -- θ p ∈ aFiberReflectionSupport (θ permutes its support).
    have hθpSupport :
        labeling.aFiberReflectionCoordPerm p ∈
          labeling.aFiberReflectionSupport :=
      labeling.aFiberReflectionCoordPerm_mem_support_of_mem hpSupport
    -- θ maps midpointExceptionSet (midpointOf d) to midpointExceptionSet (midpointOf (-d)).
    have hθpExceptionNeg :=
      (labeling.midpointExceptionSetAFixingNegInvariantBoundary criterion)
        |>.aFiberReflection_mem_midpointExceptionSet_neg d hd p hpException
    -- Intersection at midpointOf d = intersection at midpointOf (-d) (via chain).
    have hchain :
        labeling.midpointExceptionAFixingSupportIntersection
            (midpointOf d) (midpointOf_ne_zero hd) =
          labeling.midpointExceptionAFixingSupportIntersection
            (midpointOf (-d)) (midpointOf_ne_zero (neg_ne_zero.mpr hd)) := by
      have hmid_neg : -(midpointOf d) = midpointOf (-d) := by
        dsimp [midpointOf]
        ring
      have hneg :=
        labeling.midpointExceptionAFixingSupportIntersection_eq_neg_of_criterion
          criterion (midpointOf_ne_zero hd)
      rw [hneg]
      exact labeling.midpointExceptionAFixingSupportIntersection_index_subst
        hmid_neg _ _
    -- θp ∈ intersection at midpointOf (-d) and via hchain it's also at midpointOf d.
    have hθpInter :
        labeling.aFiberReflectionCoordPerm p ∈
          labeling.midpointExceptionAFixingSupportIntersection
            (midpointOf (-d)) (midpointOf_ne_zero (neg_ne_zero.mpr hd)) :=
      (labeling.mem_midpointExceptionAFixingSupportIntersection
        (midpointOf (-d)) (midpointOf_ne_zero (neg_ne_zero.mpr hd))
        (labeling.aFiberReflectionCoordPerm p)).2
        ⟨hθpExceptionNeg, hθpSupport⟩
    rw [← hchain] at hθpInter
    exact hθpInter

/-- Singleton-fixedness boundary (e=1 case) from criterion alone. -/
def midpointExceptionAFixingSupportSingletonFixedBoundary_of_criterion
    (labeling : BranchOrbitABCReflectionLabeling h)
    (criterion : MidpointReflectionCriterionBoundary labeling) :
    MidpointExceptionAFixingSupportSingletonFixedBoundary labeling :=
  (labeling.midpointExceptionAFixingSupportIntersectionInvariantBoundary_of_criterion
    criterion).toMidpointExceptionAFixingSupportSingletonFixedBoundary

/-- `no_card_one` field (e=1 case excluded) from criterion alone. -/
theorem no_card_one_of_criterion
    (labeling : BranchOrbitABCReflectionLabeling h)
    (criterion : MidpointReflectionCriterionBoundary labeling)
    (d : ZMod 19) (hd : d ≠ 0) :
    (labeling.midpointExceptionAFixingSupportIntersection
      (midpointOf d) (midpointOf_ne_zero hd)).card ≠ 1 :=
  (labeling.midpointExceptionAFixingSupportIntersectionInvariantBoundary_of_criterion
    criterion).no_card_one d hd

/-- Final assembly: criterion + supportCard + e=2 base witness give
`MidpointExceptionDisjointAFixingSupportBoundary` (Lemma 6.3).

The e=2 base witness is the only remaining mathematical input — the
natural-language 17-common-neighbor / μ=1 contradiction.  By the doubling
chain, exclusion at one base index propagates to all `d`. -/
def midpointExceptionDisjointAFixingSupportBoundary_of_criterion_and_e2
    (labeling : BranchOrbitABCReflectionLabeling h)
    (criterion : MidpointReflectionCriterionBoundary labeling)
    (supportCard : AFixingReflectionFixedNeighborCardBoundary labeling)
    {baseTwo : ZMod 19} (hbaseTwo : baseTwo ≠ 0)
    (hne_two :
      (labeling.midpointExceptionAFixingSupportIntersection
        baseTwo hbaseTwo).card ≠ 2) :
    MidpointExceptionDisjointAFixingSupportBoundary labeling := by
  let doubling :=
    midpointExceptionDoublingBoundary_of_criterion labeling criterion
  let caseBoundary : MidpointExceptionAFixingSupportCaseBoundary labeling := {
    support_card_boundary := supportCard,
    no_card_one := fun d hd =>
      labeling.no_card_one_of_criterion criterion d hd,
    no_card_two :=
      doubling.no_card_two_of_card_ne_two hbaseTwo hne_two }
  exact caseBoundary.toMidpointExceptionDisjointAFixingSupportBoundary

end BranchOrbitABCReflectionLabeling

end

end Moore57
