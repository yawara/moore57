import Moore57.BranchOrbitABCSupportPairBoundary

/-!
# Vertex separation for a two-point A-fixing reflection support

The card-two support API gives distinct coordinates.  This file records the
corresponding distinctness of their reference-fiber vertices.
-/

namespace Moore57

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

namespace BranchOrbitABCReflectionLabeling

variable {h : D19ActsOnMoore57 V Γ}

namespace AFixingReflectionFixedNeighborCardBoundary

variable {labeling : BranchOrbitABCReflectionLabeling h}

/-- Distinct reference coordinates have distinct reference-fiber vertices. -/
theorem reference_coord_ne_of_ne
    (_supportCard : AFixingReflectionFixedNeighborCardBoundary labeling)
    {p q : labeling.data.toAFiberCoordinates.P}
    (hpq : p ≠ q) :
    (((labeling.data.toAFiberCoordinates.coord 0 p :
      {x : V // x ∈
        branchFiber Γ labeling.data.toAFiberCoordinates.u
          (labeling.data.toAFiberCoordinates.a 0)}) : V)) ≠
    (((labeling.data.toAFiberCoordinates.coord 0 q :
      {x : V // x ∈
        branchFiber Γ labeling.data.toAFiberCoordinates.u
          (labeling.data.toAFiberCoordinates.a 0)}) : V)) := by
  intro hcoord
  have hsub :
      (labeling.data.toAFiberCoordinates.coord 0 p :
        {x : V // x ∈
          branchFiber Γ labeling.data.toAFiberCoordinates.u
            (labeling.data.toAFiberCoordinates.a 0)}) =
      (labeling.data.toAFiberCoordinates.coord 0 q :
        {x : V // x ∈
          branchFiber Γ labeling.data.toAFiberCoordinates.u
            (labeling.data.toAFiberCoordinates.a 0)}) := by
    exact Subtype.ext hcoord
  exact hpq ((labeling.data.toAFiberCoordinates.coord 0).injective hsub)

/-- A chosen support point and its A-fiber reflection mate are distinct as
reference-fiber vertices. -/
theorem reference_coord_ne_reflection_of_mem
    (supportCard : AFixingReflectionFixedNeighborCardBoundary labeling)
    {p : labeling.data.toAFiberCoordinates.P}
    (hp : p ∈ labeling.aFiberReflectionSupport) :
    (((labeling.data.toAFiberCoordinates.coord 0 p :
      {x : V // x ∈
        branchFiber Γ labeling.data.toAFiberCoordinates.u
          (labeling.data.toAFiberCoordinates.a 0)}) : V)) ≠
    (((labeling.data.toAFiberCoordinates.coord 0
        (labeling.aFiberReflectionCoordPerm p) :
      {x : V // x ∈
        branchFiber Γ labeling.data.toAFiberCoordinates.u
          (labeling.data.toAFiberCoordinates.a 0)}) : V)) := by
  exact supportCard.reference_coord_ne_of_ne
    (by
      intro hp_eq
      exact supportCard.aFiberReflectionCoordPerm_ne_of_mem hp hp_eq.symm)

/-- Any support point different from a chosen support point has a different
reference-fiber vertex. -/
theorem reference_coord_ne_of_mem_of_ne
    (supportCard : AFixingReflectionFixedNeighborCardBoundary labeling)
    {p q : labeling.data.toAFiberCoordinates.P}
    (_hp : p ∈ labeling.aFiberReflectionSupport)
    (_hq : q ∈ labeling.aFiberReflectionSupport)
    (hpq : p ≠ q) :
    (((labeling.data.toAFiberCoordinates.coord 0 p :
      {x : V // x ∈
        branchFiber Γ labeling.data.toAFiberCoordinates.u
          (labeling.data.toAFiberCoordinates.a 0)}) : V)) ≠
    (((labeling.data.toAFiberCoordinates.coord 0 q :
      {x : V // x ∈
        branchFiber Γ labeling.data.toAFiberCoordinates.u
          (labeling.data.toAFiberCoordinates.a 0)}) : V)) :=
  supportCard.reference_coord_ne_of_ne hpq

end AFixingReflectionFixedNeighborCardBoundary

end BranchOrbitABCReflectionLabeling

end

end Moore57
