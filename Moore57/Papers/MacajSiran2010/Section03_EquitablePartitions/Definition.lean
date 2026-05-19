import Moore57.Moore57Graph.Moore57Definition

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Mačaj–Širáň 2010, §3 — Equitable partitions (definition) [skeleton]

> Let Γ be a Moore (57, 2)-graph and let `S = {S₁, S₂, …, Sₖ}` be a
> partition of `V(Γ)`. We say that `S` is an **equitable partition** of Γ
> if there exist integers `b_{ij}` such that each vertex from `Sᵢ` has
> exactly `b_{ij}` neighbours in `Sⱼ`. The matrix `B = (b_{ij}) ∈ ℤ^{k×k}`
> is the **adjacency matrix** of `S`.
-/

namespace Moore57.Papers.MacajSiran2010.S3

variable {V : Type*} [Fintype V] [DecidableEq V]
  {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

open scoped Classical in
/-- An indexed family of finite sets is an **equitable partition** of Γ if
the cells partition `V` and the number of neighbours of any vertex in cell
`i` lying in cell `j` depends only on `(i, j)`. [skeleton] -/
structure EquitablePartition (Γ : SimpleGraph V) (ι : Type*) [Fintype ι] where
  cell : ι → Finset V
  partition_disjoint : ∀ i j, i ≠ j → Disjoint (cell i) (cell j)
  partition_covers : (Finset.univ : Finset ι).biUnion cell = Finset.univ
  adjMatrix : ι → ι → ℤ
  equitable :
    ∀ i j v, v ∈ cell i →
      ((cell j).filter (fun w => Γ.Adj v w)).card = (adjMatrix i j).toNat

end Moore57.Papers.MacajSiran2010.S3
