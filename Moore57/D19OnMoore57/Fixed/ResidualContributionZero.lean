import Moore57.D19OnMoore57.Rotation.OneMovingResidualProperties
import Moore57.D19OnMoore57.AFiber.ContributionCardinalityCriteria
import Moore57.D19OnMoore57.Rotation.FixedCardinality

/-!
# Zero contribution from the rotation-one fixed residual side

The canonical fixed residual side is contained in the fixed set of
`h.rotation 1`.  Since all nontrivial rotation fixed sets coincide in the
order-19 rotation subgroup, every such vertex is also fixed by `h.rotation d`
for `d ≠ 0`.  Hence an adjacent moved edge there would be a loop.
-/

namespace Moore57

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- A vertex in the rotation-one fixed residual part is not adjacent to its
image under any nontrivial rotation. -/
theorem rotationOneFixedResidualPart_not_adjacent_rotation
    (h : D19ActsOnMoore57 V Γ) (input : OrbitBaseSelectionInput h)
    {k d : ZMod 19} (hd : d ≠ 0) {y : V}
    (hy : y ∈ rotationOneFixedResidualPart h input k) :
    ¬ Γ.Adj y (h.rotation d y) := by
  intro hadj
  have hyFixedOne : y ∈ fixedVertexSet (h.rotation 1) :=
    (mem_rotationOneFixedResidualPart_iff.mp hy).1
  have hfixedSets :
      fixedVertexSet (h.rotation 1) = fixedVertexSet (h.rotation d) :=
    h.fixedVertexSet_rotation_eq_of_nonzero (by decide) hd
  have hyFixedD : y ∈ fixedVertexSet (h.rotation d) := by
    simpa [hfixedSets] using hyFixedOne
  have hyRot : h.rotation d y = y := mem_fixedVertexSet.mp hyFixedD
  rw [hyRot] at hadj
  exact SimpleGraph.irrefl Γ hadj

/-- The adjacent-rotation filtered cardinality of the canonical fixed residual
side is zero for every nontrivial rotation. -/
theorem rotationOneFixedResidualPart_filter_adjacent_rotation_card_eq_zero
    (h : D19ActsOnMoore57 V Γ) (input : OrbitBaseSelectionInput h)
    (k d : ZMod 19) (hd : d ≠ 0) :
    ((rotationOneFixedResidualPart h input k).filter fun y =>
      Γ.Adj y (h.rotation d y)).card = 0 := by
  rw [Finset.card_eq_zero]
  ext y
  constructor
  · intro hy
    rcases Finset.mem_filter.mp hy with ⟨hyPart, hyAdj⟩
    exact False.elim
      (rotationOneFixedResidualPart_not_adjacent_rotation
        h input hd hyPart hyAdj)
  · intro hy
    simp at hy

/-- The named fixed-side A-fiber contribution cardinality is zero for every
nontrivial rotation. -/
theorem fixedAFiberFixedCard_eq_zero
    (h : D19ActsOnMoore57 V Γ) (input : OrbitBaseSelectionInput h)
    (k d : ZMod 19) (hd : d ≠ 0) :
    fixedAFiberFixedCard h input k d = 0 := by
  simpa [fixedAFiberFixedCard] using
    rotationOneFixedResidualPart_filter_adjacent_rotation_card_eq_zero
      h input k d hd

end Moore57
