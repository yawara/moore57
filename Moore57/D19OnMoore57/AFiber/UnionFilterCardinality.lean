import Moore57.Moore57Graph.AFiber.FiberUnionCardinality
import Moore57.D19OnMoore57.AFiber.ContributionCardinalityCriteria

/-!
# Filtered cardinality of selected A-fiber unions

This file decomposes filtered cardinalities over selected `AFiberCoordinates`
fiber unions.  The fibers are already known to be pairwise disjoint, so the
filtered union cardinality is the sum of the filtered fiber cardinalities.
-/

namespace Moore57

open Finset

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

namespace AFiberCoordinates

/-- Filtering a selected union of pairwise-disjoint A-fibers decomposes as the
sum of the filtered fiber cardinalities. -/
theorem fiberUnion_filter_card_eq_sum
    (A : AFiberCoordinates Γ) (hΓ : IsMoore57 Γ)
    (indices : Finset (ZMod 19)) (p : V → Prop) [DecidablePred p] :
    ((A.fiberUnion indices).filter p).card =
      ∑ i ∈ indices, ((A.fiber i).filter p).card := by
  classical
  have hfilter_disj :
      (indices : Set (ZMod 19)).PairwiseDisjoint
        fun i => (A.fiber i).filter p := by
    exact (A.fiberUnion_pairwiseDisjoint hΓ indices).mono
      (fun i => Finset.filter_subset p (A.fiber i))
  calc
    ((A.fiberUnion indices).filter p).card =
        (indices.biUnion fun i => (A.fiber i).filter p).card := by
      rw [fiberUnion, Finset.filter_biUnion]
    _ = ∑ i ∈ indices, ((A.fiber i).filter p).card := by
      rw [Finset.card_biUnion hfilter_disj]

end AFiberCoordinates

/-- The concrete A-fiber contribution cardinality over a selected union of
A-fibers decomposes as the sum over selected indices. -/
theorem fixedAFiberAFiberCard_fiberUnion_eq_sum
    (h : D19ActsOnMoore57 V Γ) (coords : AFiberCoordinates Γ)
    (indices : Finset (ZMod 19)) (d : ZMod 19) :
    fixedAFiberAFiberCard h (coords.fiberUnion indices) d =
      ∑ i ∈ indices,
        ((coords.fiber i).filter fun y => Γ.Adj y (h.rotation d y)).card := by
  classical
  simpa [fixedAFiberAFiberCard] using
    (coords.fiberUnion_filter_card_eq_sum h.isMoore indices
      (fun y => Γ.Adj y (h.rotation d y)))

end Moore57
