import Moore57.Foundations.GroupAction.SubgroupFixed
import Moore57.Foundations.GraphTheory.StrongZeroOne
import Moore57.Moore57Graph.Aut.CommonNeighbor
import Moore57.Moore57Graph.Aut.InducedSubgraph
import Mathlib.Algebra.Group.Subgroup.Basic

/-!
# Subgroup-level fixed induced subgraph (Mathlib native)

For a subgroup `G : Subgroup (Equiv.Perm V)` whose elements are all graph
automorphisms of a Moore57 graph `Γ`, the induced subgraph on
`MulAction.fixedPoints G V` inherits the strong `(λ=0, μ=1)` property.

This is the subgroup version of `autFixedInducedGraph_isStrongZeroOne`
(which only handles a single `σ`).  It formalises Aschbacher 1971
Lemma 1.2 in its full subgroup generality.

## Design

* Set: `MulAction.fixedPoints G V` (Mathlib native).
* Induced subgraph: `Γ.induce (MulAction.fixedPoints G V)` (Mathlib native).
* Hypothesis `G ⊆ Aut(Γ)`: `∀ σ ∈ G, ∀ v w, Γ.Adj v w ↔ Γ.Adj (σ v) (σ w)`.
-/

namespace Moore57

open MulAction

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- Induced subgraph on the vertices fixed by a subgroup `G ≤ Equiv.Perm V`. -/
abbrev subgroupFixedInducedGraph
    (Γ : SimpleGraph V) (G : Subgroup (Equiv.Perm V)) :
    SimpleGraph (MulAction.fixedPoints G V) :=
  Γ.induce (MulAction.fixedPoints G V)

instance subgroupFixedInducedGraph_decidableRel
    (G : Subgroup (Equiv.Perm V)) :
    DecidableRel (subgroupFixedInducedGraph Γ G).Adj := fun _ _ =>
  inferInstanceAs (Decidable (Γ.Adj _ _))

omit [Fintype V] [DecidableEq V] [DecidableRel Γ.Adj] in
@[simp] theorem subgroupFixedInducedGraph_adj
    (G : Subgroup (Equiv.Perm V))
    {x y : MulAction.fixedPoints G V} :
    (subgroupFixedInducedGraph Γ G).Adj x y ↔ Γ.Adj (x : V) (y : V) := by
  rfl

/-- **Adjacent G-fixed vertices have 0 common neighbours in the induced
subgraph.** -/
theorem subgroupFixedInducedGraph_commonNeighbors_card_of_adj
    (hΓ : IsMoore57 Γ) (G : Subgroup (Equiv.Perm V)) [Fintype G]
    {x y : MulAction.fixedPoints G V}
    (hxy : (subgroupFixedInducedGraph Γ G).Adj x y) :
    Fintype.card ((subgroupFixedInducedGraph Γ G).commonNeighbors x y) = 0 := by
  classical
  refine Fintype.card_eq_zero_iff.mpr ⟨fun z => ?_⟩
  have hz : (z : MulAction.fixedPoints G V) ∈
      (subgroupFixedInducedGraph Γ G).commonNeighbors x y := z.property
  have hz_ambient : (z : V) ∈ Γ.commonNeighbors (x : V) (y : V) := by
    rw [SimpleGraph.mem_commonNeighbors] at hz ⊢
    exact hz
  have hcard : Fintype.card (Γ.commonNeighbors (x : V) (y : V)) = 0 :=
    hΓ.of_adj (x : V) (y : V) hxy
  have hpos : 0 < Fintype.card (Γ.commonNeighbors (x : V) (y : V)) := by
    rw [Fintype.card_pos_iff]
    exact ⟨⟨(z : V), hz_ambient⟩⟩
  omega

/-- **Non-adjacent distinct G-fixed vertices have a G-fixed common
neighbour.**

Given `x, y ∈ Fix(G)` distinct, non-adjacent, with `z ∈ N(x) ∩ N(y)`,
conclude `z ∈ Fix(G)`.  Proof: apply `aut_fixed_commonNeighbor_of_not_adj`
σ-by-σ for each σ ∈ G. -/
theorem aut_fixed_commonNeighbor_of_not_adj_subgroup
    (hΓ : IsMoore57 Γ) (G : Subgroup (Equiv.Perm V))
    (hG : ∀ σ ∈ G, ∀ v w : V, Γ.Adj v w ↔ Γ.Adj (σ v) (σ w))
    {x y z : V}
    (hx : x ∈ MulAction.fixedPoints G V) (hy : y ∈ MulAction.fixedPoints G V)
    (hxy : x ≠ y) (hnadj : ¬ Γ.Adj x y)
    (hz : Γ.Adj x z ∧ Γ.Adj y z) :
    z ∈ MulAction.fixedPoints G V := by
  rw [(mem_mulAction_fixedPoints_iff_forall_mem (G := G) z)]
  intro σ hσ
  -- For each σ ∈ G, single-σ result gives σ z = z.
  apply aut_fixed_commonNeighbor_of_not_adj hΓ (σ : V → V) (hG σ hσ)
  · exact ((mem_mulAction_fixedPoints_iff_forall_mem (G := G) x).mp hx) σ hσ
  · exact ((mem_mulAction_fixedPoints_iff_forall_mem (G := G) y).mp hy) σ hσ
  · exact hxy
  · exact hnadj
  · exact hz

/-- **Distinct non-adjacent G-fixed vertices have exactly one common
neighbour in the induced subgraph.** -/
theorem subgroupFixedInducedGraph_commonNeighbors_card_of_not_adj
    (hΓ : IsMoore57 Γ) (G : Subgroup (Equiv.Perm V)) [Fintype G]
    (hG : ∀ σ ∈ G, ∀ v w : V, Γ.Adj v w ↔ Γ.Adj (σ v) (σ w))
    {x y : MulAction.fixedPoints G V}
    (hxy_ne : x ≠ y) (hnadj : ¬ (subgroupFixedInducedGraph Γ G).Adj x y) :
    Fintype.card ((subgroupFixedInducedGraph Γ G).commonNeighbors x y) = 1 := by
  classical
  have hxy_ne_ambient : (x : V) ≠ (y : V) := fun hval => hxy_ne (Subtype.ext hval)
  have hnadj_ambient : ¬ Γ.Adj (x : V) (y : V) := by
    simpa [subgroupFixedInducedGraph] using hnadj
  have hcard : Fintype.card (Γ.commonNeighbors (x : V) (y : V)) = 1 :=
    hΓ.of_not_adj hxy_ne_ambient hnadj_ambient
  rcases Fintype.card_eq_one_iff.mp hcard with ⟨z, hz_unique⟩
  have hz_mem : (z : V) ∈ Γ.commonNeighbors (x : V) (y : V) := z.property
  have hz_adj : Γ.Adj (x : V) (z : V) ∧ Γ.Adj (y : V) (z : V) := by
    rw [SimpleGraph.mem_commonNeighbors] at hz_mem
    exact hz_mem
  -- z is also G-fixed by the subgroup version of the helper.
  have hx_fixed : (x : V) ∈ MulAction.fixedPoints G V := x.property
  have hy_fixed : (y : V) ∈ MulAction.fixedPoints G V := y.property
  have hzFixed : (z : V) ∈ MulAction.fixedPoints G V :=
    aut_fixed_commonNeighbor_of_not_adj_subgroup hΓ G hG
      hx_fixed hy_fixed hxy_ne_ambient hnadj_ambient hz_adj
  let zFixed : MulAction.fixedPoints G V := ⟨(z : V), hzFixed⟩
  have zFixed_mem :
      zFixed ∈ (subgroupFixedInducedGraph Γ G).commonNeighbors x y := by
    rw [SimpleGraph.mem_commonNeighbors]
    exact hz_adj
  refine Fintype.card_eq_one_iff.mpr ⟨⟨zFixed, zFixed_mem⟩, ?_⟩
  intro w
  apply Subtype.ext
  apply Subtype.ext
  have hw_mem_fixed :
      (w : MulAction.fixedPoints G V) ∈
        (subgroupFixedInducedGraph Γ G).commonNeighbors x y := w.property
  have hw_mem : (w : V) ∈ Γ.commonNeighbors (x : V) (y : V) := by
    rw [SimpleGraph.mem_commonNeighbors] at hw_mem_fixed ⊢
    exact hw_mem_fixed
  have hw_eq_z : (w : V) = (z : V) :=
    congrArg Subtype.val (hz_unique ⟨(w : V), hw_mem⟩)
  exact hw_eq_z

/-- **Subgroup version of Aschbacher Lemma 1.2.**

For a subgroup `G ≤ Equiv.Perm V` whose elements are all graph
automorphisms of a Moore57 graph `Γ`, the induced subgraph on
`MulAction.fixedPoints G V` is strong `(λ=0, μ=1)`. -/
theorem subgroupFixedInducedGraph_isStrongZeroOne
    (hΓ : IsMoore57 Γ) (G : Subgroup (Equiv.Perm V)) [Fintype G]
    (hG : ∀ σ ∈ G, ∀ v w : V, Γ.Adj v w ↔ Γ.Adj (σ v) (σ w)) :
    IsStrongZeroOne (subgroupFixedInducedGraph Γ G) where
  of_adj := by
    intro x y hxy
    exact subgroupFixedInducedGraph_commonNeighbors_card_of_adj hΓ G hxy
  of_not_adj := by
    intro x y hxy_ne hxy_not
    exact subgroupFixedInducedGraph_commonNeighbors_card_of_not_adj hΓ G hG
      hxy_ne hxy_not

end Moore57
