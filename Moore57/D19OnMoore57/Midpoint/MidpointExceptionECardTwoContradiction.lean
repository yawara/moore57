import Moore57.D19OnMoore57.Midpoint.MidpointExceptionDisjointFromCriterion
import Moore57.D19OnMoore57.BranchOrbit.BranchOrbitABCCardTwoAllOffsetsCommonNeighborBoundary
import Moore57.D19OnMoore57.BranchOrbit.BranchOrbitABCExceptionAllSupportBoundary
import Moore57.D19OnMoore57.BranchOrbit.BranchOrbitABCCardTwoCommonNeighborBoundary

/-!
# e=2 base witness via the all-offsets two-common-neighbor contradiction

This file closes the natural-language Lemma 6.3 e=2 case: if for some `d ≠ 0`
the intersection `S_(midpointOf d) ∩ E` has cardinality `2`, then by the
chain `S_h ∩ E = S_{2h} ∩ E`, the same holds at every nonzero offset.  All
support points then satisfy the endpoint adjacency at every offset, which by
the already-proved
`AFixingReflectionFixedNeighborCardBoundary.two_commonNeighbors_of_all_offsets_endpoint_adj`
yields two distinct common neighbors of a non-adjacent pair — contradicting
Moore57's `μ = 1`.

This eliminates the only remaining mathematical input for
`MidpointExceptionDisjointAFixingSupportBoundary`, completing the
natural-language Lemma 6.3 in Lean from `MidpointReflectionCriterionBoundary`
plus `AFixingReflectionFixedNeighborCardBoundary`.
-/

namespace Moore57

open Finset

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

local instance instMidpointExceptionECardTwoContradictionPFintype
    {h : D19ActsOnMoore57 V Γ}
    (labeling : BranchOrbitABCReflectionLabeling h) :
    Fintype labeling.data.toAFiberCoordinates.P :=
  labeling.data.toAFiberCoordinates.P_fintype

local instance instMidpointExceptionECardTwoContradictionDecidableEq
    (α : Type*) : DecidableEq α :=
  Classical.decEq α

namespace BranchOrbitABCReflectionLabeling

variable {h : D19ActsOnMoore57 V Γ}

/-- If the intersection at one nonzero index `d` has cardinality `2`, then by
the doubling chain it has cardinality `2` at every nonzero index, so the
A-fixing reflection support is contained in every midpoint exception set. -/
theorem aFiberReflectionSupport_subset_midpointExceptionSet_of_card_eq_two
    (labeling : BranchOrbitABCReflectionLabeling h)
    (criterion : MidpointReflectionCriterionBoundary labeling)
    (supportCard : AFixingReflectionFixedNeighborCardBoundary labeling)
    {baseD : ZMod 19} (hbaseD : baseD ≠ 0)
    (hcard :
      (labeling.midpointExceptionAFixingSupportIntersection
        baseD hbaseD).card = 2)
    (d : ZMod 19) (hd : d ≠ 0) :
    labeling.aFiberReflectionSupport ⊆
      labeling.midpointExceptionSet (midpointOf d) (midpointOf_ne_zero hd) := by
  classical
  let doubling :=
    midpointExceptionDoublingBoundary_of_criterion labeling criterion
  have hcard_d :
      (labeling.midpointExceptionAFixingSupportIntersection
        (midpointOf d) (midpointOf_ne_zero hd)).card = 2 := by
    rw [doubling.card_eq (midpointOf_ne_zero hd) hbaseD]
    exact hcard
  have hcardE :
      labeling.aFiberReflectionSupport.card = 2 :=
    supportCard.aFiberReflectionSupport_card_two
  have hsubsetE :
      labeling.midpointExceptionAFixingSupportIntersection
        (midpointOf d) (midpointOf_ne_zero hd) ⊆
        labeling.aFiberReflectionSupport := by
    intro x hx
    exact (labeling.mem_midpointExceptionAFixingSupportIntersection
      (midpointOf d) (midpointOf_ne_zero hd) x).1 hx |>.2
  have heq :
      labeling.midpointExceptionAFixingSupportIntersection
        (midpointOf d) (midpointOf_ne_zero hd) =
        labeling.aFiberReflectionSupport :=
    Finset.eq_of_subset_of_card_le hsubsetE (by rw [hcard_d, hcardE])
  intro x hxE
  have hxinter :
      x ∈ labeling.midpointExceptionAFixingSupportIntersection
        (midpointOf d) (midpointOf_ne_zero hd) := by
    rw [heq]; exact hxE
  exact (labeling.mem_midpointExceptionAFixingSupportIntersection
    (midpointOf d) (midpointOf_ne_zero hd) x).1 hxinter |>.1

/-- e=2 contradiction: if the intersection has cardinality `2` at one
nonzero index, we derive False using the all-offsets two-common-neighbor
construction. -/
theorem false_of_card_two
    (labeling : BranchOrbitABCReflectionLabeling h)
    (criterion : MidpointReflectionCriterionBoundary labeling)
    (supportCard : AFixingReflectionFixedNeighborCardBoundary labeling)
    {baseD : ZMod 19} (hbaseD : baseD ≠ 0)
    (hcard :
      (labeling.midpointExceptionAFixingSupportIntersection
        baseD hbaseD).card = 2) :
    False := by
  classical
  -- The support is contained in every midpoint exception set.
  have hsubset_all :=
    labeling.aFiberReflectionSupport_subset_midpointExceptionSet_of_card_eq_two
      criterion supportCard hbaseD hcard
  -- This gives endpoint adjacency for every support point at every nonzero
  -- offset.
  have hall :
      ∀ d : ZMod 19, ∀ _hd : d ≠ 0,
        ∀ p : labeling.data.toAFiberCoordinates.P,
          p ∈ labeling.aFiberReflectionSupport →
            Γ.Adj
              (((labeling.data.toAFiberCoordinates.coord 0 p :
                {x : V // x ∈
                  branchFiber Γ labeling.data.toAFiberCoordinates.u
                    (labeling.data.toAFiberCoordinates.a 0)}) : V))
              (((labeling.data.toAFiberCoordinates.coord
                  (0 + (midpointOf d + midpointOf d))
                  (labeling.midpointReflectionCoordPerm (midpointOf d) p) :
                {x : V // x ∈
                  branchFiber Γ labeling.data.toAFiberCoordinates.u
                    (labeling.data.toAFiberCoordinates.a
                      (0 + (midpointOf d + midpointOf d)))}) : V)) := by
    intro d hd p hp
    exact
      labeling.midpointEndpointAdj_of_mem_aFiberReflectionSupport_of_subset_midpointExceptionSet
        criterion (hsubset_all d hd) hp
  -- Apply the all-offsets 2-common-neighbor construction.
  rcases
    supportCard.two_commonNeighbors_of_all_offsets_endpoint_adj hall with
    ⟨x, y, z, w, hxy, hnadj, hzw, hxz, hyz, hxw, hyw⟩
  -- Apply Moore57 μ=1.
  exact
    h.isMoore.no_two_commonNeighbors_of_not_adj
      hxy hnadj hzw hxz hyz hxw hyw

/-- The e=2 base witness: the intersection has cardinality `≠ 2` at any
nonzero index (e.g. `1`). -/
theorem midpointExceptionAFixingSupportIntersection_card_ne_two
    (labeling : BranchOrbitABCReflectionLabeling h)
    (criterion : MidpointReflectionCriterionBoundary labeling)
    (supportCard : AFixingReflectionFixedNeighborCardBoundary labeling) :
    (labeling.midpointExceptionAFixingSupportIntersection
      (1 : ZMod 19) (by decide)).card ≠ 2 := by
  intro hcard
  exact labeling.false_of_card_two criterion supportCard
    (by decide : (1 : ZMod 19) ≠ 0) hcard

/-- Final assembly: criterion + supportCard give
`MidpointExceptionDisjointAFixingSupportBoundary` (Lemma 6.3) with NO extra
inputs. -/
def midpointExceptionDisjointAFixingSupportBoundary_of_criterion_supportCard
    (labeling : BranchOrbitABCReflectionLabeling h)
    (criterion : MidpointReflectionCriterionBoundary labeling)
    (supportCard : AFixingReflectionFixedNeighborCardBoundary labeling) :
    MidpointExceptionDisjointAFixingSupportBoundary labeling :=
  labeling.midpointExceptionDisjointAFixingSupportBoundary_of_criterion_and_e2
    criterion supportCard (by decide : (1 : ZMod 19) ≠ 0)
    (labeling.midpointExceptionAFixingSupportIntersection_card_ne_two
      criterion supportCard)

end BranchOrbitABCReflectionLabeling

end

end Moore57
