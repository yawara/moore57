import Moore57.OrbitContributionSum
import Moore57.D19ActionTraceBridge

/-!
# Adjacent-moved partition sums

Generic finite-partition bookkeeping for decomposing a filtered vertex count,
plus the specialization to `adjacentMovedCount Γ (h.rotation d)`.
-/

namespace Moore57

open Finset

/-- If pairwise-disjoint pieces and a residual finset cover the whole finite
type, then the cardinality of a filtered `univ` is the sum of the filtered
cardinalities over the pieces plus the filtered residual cardinality. -/
theorem Finset.card_filter_univ_eq_sum_filter_card_add_residual
    {α ι : Type*} [Fintype α] [DecidableEq α]
    (s : Finset ι) (pieces : ι → Finset α) (residual : Finset α)
    (p : α → Prop) [DecidablePred p]
    (hdisj : (s : Set ι).PairwiseDisjoint pieces)
    (hresidual : ∀ i, i ∈ s → Disjoint (pieces i) residual)
    (hcover : s.biUnion pieces ∪ residual = (Finset.univ : Finset α)) :
    ((Finset.univ : Finset α).filter p).card =
      (∑ i ∈ s, ((pieces i).filter p).card) + (residual.filter p).card := by
  classical
  have hfilter_disj : (s : Set ι).PairwiseDisjoint (fun i => (pieces i).filter p) := by
    exact hdisj.mono (fun i => Finset.filter_subset p (pieces i))
  have hUnionResidual : Disjoint (s.biUnion pieces) residual := by
    rw [Finset.disjoint_left]
    intro a ha hb
    rcases Finset.mem_biUnion.mp ha with ⟨i, hi, hai⟩
    exact (Finset.disjoint_left.mp (hresidual i hi)) hai hb
  have hFilterUnionResidual : Disjoint ((s.biUnion pieces).filter p) (residual.filter p) := by
    exact Disjoint.mono (Finset.filter_subset p (s.biUnion pieces))
      (Finset.filter_subset p residual) hUnionResidual
  calc
    ((Finset.univ : Finset α).filter p).card =
        (((s.biUnion pieces) ∪ residual).filter p).card := by
      rw [hcover]
    _ = (((s.biUnion pieces).filter p) ∪ (residual.filter p)).card := by
      rw [Finset.filter_union]
    _ = ((s.biUnion pieces).filter p).card + (residual.filter p).card := by
      rw [Finset.card_union_of_disjoint hFilterUnionResidual]
    _ = (∑ i ∈ s, ((pieces i).filter p).card) + (residual.filter p).card := by
      rw [Finset.filter_biUnion]
      rw [Finset.card_biUnion hfilter_disj]

/-- Residual-free form of
`Finset.card_filter_univ_eq_sum_filter_card_add_residual`. -/
theorem Finset.card_filter_univ_eq_sum_filter_card
    {α ι : Type*} [Fintype α] [DecidableEq α]
    (s : Finset ι) (pieces : ι → Finset α) (p : α → Prop) [DecidablePred p]
    (hdisj : (s : Set ι).PairwiseDisjoint pieces)
    (hcover : s.biUnion pieces = (Finset.univ : Finset α)) :
    ((Finset.univ : Finset α).filter p).card =
      ∑ i ∈ s, ((pieces i).filter p).card := by
  classical
  have hfilter_disj : (s : Set ι).PairwiseDisjoint (fun i => (pieces i).filter p) := by
    exact hdisj.mono (fun i => Finset.filter_subset p (pieces i))
  calc
    ((Finset.univ : Finset α).filter p).card = ((s.biUnion pieces).filter p).card := by
      rw [hcover]
    _ = (s.biUnion (fun i => (pieces i).filter p)).card := by
      rw [Finset.filter_biUnion]
    _ = ∑ i ∈ s, ((pieces i).filter p).card := by
      rw [Finset.card_biUnion hfilter_disj]

namespace D19ActsOnMoore57

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- Decompose `adjacentMovedCount Γ (h.rotation d)` over a finite partition of
vertices, allowing one residual finset. -/
theorem adjacentMovedCount_eq_sum_filter_card_add_residual
    (h : D19ActsOnMoore57 V Γ) (d : ZMod 19) {ι : Type*} [Fintype ι]
    (pieces : ι → Finset V) (residual : Finset V)
    (hdisj : ((Finset.univ : Finset ι) : Set ι).PairwiseDisjoint pieces)
    (hresidual : ∀ i : ι, Disjoint (pieces i) residual)
    (hcover : (Finset.univ : Finset ι).biUnion pieces ∪ residual =
      (Finset.univ : Finset V)) :
    adjacentMovedCount Γ (h.rotation d) =
      (∑ i : ι, ((pieces i).filter fun y => Γ.Adj y (h.rotation d y)).card) +
        (residual.filter fun y => Γ.Adj y (h.rotation d y)).card := by
  classical
  simpa [adjacentMovedCount] using
    (Finset.card_filter_univ_eq_sum_filter_card_add_residual
      (s := (Finset.univ : Finset ι))
      (pieces := pieces)
      (residual := residual)
      (p := fun y => Γ.Adj y (h.rotation d y))
      hdisj
      (fun i _hi => hresidual i)
      hcover)

/-- A reusable finite partition package for decomposing
`adjacentMovedCount Γ (h.rotation d)`. The residual field can be `∅` for a pure
partition indexed by `ι`. -/
structure AdjacentMovedPartition (h : D19ActsOnMoore57 V Γ) (d : ZMod 19)
    (ι : Type*) [Fintype ι] where
  pieces : ι → Finset V
  residual : Finset V
  pairwise_disjoint : ((Finset.univ : Finset ι) : Set ι).PairwiseDisjoint pieces
  residual_disjoint : ∀ i : ι, Disjoint (pieces i) residual
  cover : (Finset.univ : Finset ι).biUnion pieces ∪ residual = (Finset.univ : Finset V)

/-- The partition package gives the adjacent-moved count as a sum over the
filtered pieces plus the filtered residual. -/
theorem AdjacentMovedPartition.adjacentMovedCount_eq_sum_filter_card
    (h : D19ActsOnMoore57 V Γ) (d : ZMod 19) {ι : Type*} [Fintype ι]
    (P : AdjacentMovedPartition h d ι) :
    adjacentMovedCount Γ (h.rotation d) =
      (∑ i : ι, ((P.pieces i).filter fun y => Γ.Adj y (h.rotation d y)).card) +
        (P.residual.filter fun y => Γ.Adj y (h.rotation d y)).card := by
  classical
  exact h.adjacentMovedCount_eq_sum_filter_card_add_residual d P.pieces P.residual
    P.pairwise_disjoint P.residual_disjoint P.cover

end D19ActsOnMoore57

end Moore57
