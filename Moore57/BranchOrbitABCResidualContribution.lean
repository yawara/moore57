import Moore57.BranchOrbitABCResidualSplit
import Moore57.CenterNeighborContributionZero
import Moore57.AFiberCardinalityBoundary
import Moore57.AdjacentMovedReflectionCompactSplit

/-!
# Residual contribution for the B/C selected split

The canonical B-fiber selected residual is `centerNeighborPart ∪ A_fibers`.
The first summand contributes zero to the adjacent-moved count, and an
`AFiberCardinality38Boundary` supplies the `38` contribution from the A-side.
This packages the result in the generic compact split-residual witness.
-/

namespace Moore57

open Finset

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

namespace BranchOrbitABCFromCenter

variable {h : D19ActsOnMoore57 V Γ}

/-- The zero part `{u} ∪ N(u)` is disjoint from the A-side all-fiber union. -/
theorem zeroPart_disjoint_toAFiberCoordinates_allFibers
    (data : BranchOrbitABCFromCenter h) :
    Disjoint (centerNeighborPart Γ data.u) data.toAFiberCoordinates.allFibers := by
  rw [← data.aSideLeaf_eq_allFibers]
  exact h.centerNeighborPart_disjoint_branchOrbitLeaf
    data.u_fixed data.a0_adj

/-- The center-neighbor residual piece plus the A-side all-fiber piece has
constant adjacent-moved contribution `38`. -/
theorem zeroPart_union_allFibers_residual_contribution
    (data : BranchOrbitABCFromCenter h)
    (boundary :
      AFiberCardinality38Boundary h data.toAFiberCoordinates
        (Finset.univ : Finset (ZMod 19))) :
    ∀ d : ZMod 19, ∀ _hd : d ≠ 0,
      ((centerNeighborPart Γ data.u).filter fun y =>
          Γ.Adj y (h.rotation d y)).card +
        (data.toAFiberCoordinates.allFibers.filter fun y =>
          Γ.Adj y (h.rotation d y)).card =
        38 := by
  intro d hd
  have hzero :
      ((centerNeighborPart Γ data.u).filter fun y =>
          Γ.Adj y (h.rotation d y)).card = 0 :=
    h.centerNeighborPart_filter_adjacent_rotation_card_eq_zero
      data.u_fixed d
  have ha :
      (data.toAFiberCoordinates.allFibers.filter fun y =>
          Γ.Adj y (h.rotation d y)).card = 38 := by
    simpa [AFiberCoordinates.allFibers, fixedAFiberAFiberCard] using
      boundary.card_eq_thirtyEight d hd
  simp [hzero, ha]

/-- Package the natural-language Section 7 residual split as the generic
compact split-residual witness for the canonical B-fiber selected input. -/
noncomputable def toComplementResidualSplit38WitnessFromBFibers
    (data : BranchOrbitABCFromCenter h)
    (boundary :
      AFiberCardinality38Boundary h data.toAFiberCoordinates
        (Finset.univ : Finset (ZMod 19)))
    {k : ZMod 19}
    (href : h.smul (DihedralGroup.sr k) data.b0 = data.c0)
    (cross_disjoint :
      ∀ q r : Fin 56,
        Disjoint
          (h.rotationOrbitFinset
            (data.toOrbitBaseSelectionInputFromBFibers.base q))
          (h.rotationOrbitFinset
            (h.smul (DihedralGroup.sr k)
              (data.toOrbitBaseSelectionInputFromBFibers.base r)))) :
    AdjacentMovedReflectionComplementResidualSplit38Witness h
      data.toOrbitBaseSelectionInputFromBFibers where
  k := k
  cross_disjoint := cross_disjoint
  fixedPart := centerNeighborPart Γ data.u
  aPart := data.toAFiberCoordinates.allFibers
  parts_disjoint := data.zeroPart_disjoint_toAFiberCoordinates_allFibers
  residual_eq :=
    data.reflectionCopyResidual_toOrbitBaseSelectionInputFromBFibers_eq_zeroPart_union_aFibers
      href
  residual_contribution :=
    data.zeroPart_union_allFibers_residual_contribution boundary

end BranchOrbitABCFromCenter

end

end Moore57
