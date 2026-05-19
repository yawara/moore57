import Moore57.Moore57Graph.Moore57Definition

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Mačaj–Širáň 2010, §3 — Equitable partitions (definition)

> Let Γ be a Moore (57, 2)-graph and let `S = {S₁, S₂, …, Sₖ}` be a
> partition of `V(Γ)`. We say that `S` is an **equitable partition** of Γ
> if there exist integers `b_{ij}` such that each vertex from `Sᵢ` has
> exactly `b_{ij}` neighbours in `Sⱼ`. The matrix `B = (b_{ij}) ∈ ℕ^{k×k}`
> is the **adjacency matrix** of `S`.
-/

namespace Moore57.Papers.MacajSiran2010.S3

variable {V : Type*} [Fintype V] [DecidableEq V]
  {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- An indexed family of finite sets is an **equitable partition** of Γ if the
cells partition `V` and the number of neighbours of any vertex in cell `i`
lying in cell `j` depends only on `(i, j)`. -/
structure EquitablePartition (Γ : SimpleGraph V) [DecidableRel Γ.Adj]
    (ι : Type*) [Fintype ι] where
  /-- The `i`-th cell `Sᵢ`. -/
  cell : ι → Finset V
  /-- Distinct cells are disjoint. -/
  pairwise_disjoint : ((Finset.univ : Finset ι) : Set ι).PairwiseDisjoint cell
  /-- The cells cover the vertex set. -/
  covers : (Finset.univ : Finset ι).biUnion cell = Finset.univ
  /-- The adjacency matrix `B = (b_{ij})`. -/
  adjMatrix : ι → ι → ℕ
  /-- The defining condition: vertices in cell `i` have `b_{ij}` neighbours
  in cell `j`. -/
  equitable :
    ∀ i j v, v ∈ cell i →
      ((cell j).filter (fun w => Γ.Adj v w)).card = adjMatrix i j

namespace EquitablePartition

variable {ι : Type*} [Fintype ι] (P : EquitablePartition Γ ι)

/-- Size of the `i`-th cell: `sᵢ = |Sᵢ|`. -/
def cellSize (i : ι) : ℕ := (P.cell i).card

/-- The sum `s₁ + ⋯ + sₖ = |V|`. -/
theorem sum_cellSize_eq_card_V :
    ∑ i : ι, P.cellSize i = Fintype.card V := by
  classical
  unfold cellSize
  rw [← Finset.card_biUnion P.pairwise_disjoint, P.covers, Finset.card_univ]

/-- **Row-sum property.** For a Moore57 graph (every vertex has degree 57), each
row of the adjacency matrix `B` sums to 57: `∑_j b_{ij} = 57` for any `i` with
a nonempty cell. -/
theorem row_sum_eq_57 (hΓ : IsMoore57 Γ)
    (i : ι) {v : V} (hv : v ∈ P.cell i) :
    ∑ j : ι, P.adjMatrix i j = 57 := by
  classical
  -- Each vertex in cell i has exactly 57 neighbours total.
  have hdeg : (Γ.neighborFinset v).card = 57 := by
    have := hΓ.regular v
    simpa [SimpleGraph.IsRegularOfDegree] using this
  -- The neighbours partition by which cell they lie in.
  have hpartition :
      (Finset.univ : Finset ι).biUnion
        (fun j => (P.cell j).filter (fun w => Γ.Adj v w)) =
        Γ.neighborFinset v := by
    ext w
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_filter,
      SimpleGraph.mem_neighborFinset]
    refine ⟨fun ⟨_, hw, hadj⟩ => hadj, fun hadj => ?_⟩
    have hw_univ : w ∈ (Finset.univ : Finset ι).biUnion P.cell := by
      rw [P.covers]; exact Finset.mem_univ _
    rcases Finset.mem_biUnion.mp hw_univ with ⟨j, _, hwj⟩
    exact ⟨j, hwj, hadj⟩
  have hdisjoint :
      ((Finset.univ : Finset ι) : Set ι).PairwiseDisjoint
        (fun j => (P.cell j).filter (fun w => Γ.Adj v w)) := by
    intro i _ j _ hij
    have := P.pairwise_disjoint (Finset.mem_coe.mpr (Finset.mem_univ i))
      (Finset.mem_coe.mpr (Finset.mem_univ j)) hij
    exact this.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _)
  calc ∑ j : ι, P.adjMatrix i j
      = ∑ j : ι, ((P.cell j).filter (fun w => Γ.Adj v w)).card := by
        refine Finset.sum_congr rfl (fun j _ => (P.equitable i j v hv).symm)
    _ = ((Finset.univ : Finset ι).biUnion
          (fun j => (P.cell j).filter (fun w => Γ.Adj v w))).card := by
        rw [Finset.card_biUnion hdisjoint]
    _ = (Γ.neighborFinset v).card := by rw [hpartition]
    _ = 57 := hdeg

end EquitablePartition

end Moore57.Papers.MacajSiran2010.S3
