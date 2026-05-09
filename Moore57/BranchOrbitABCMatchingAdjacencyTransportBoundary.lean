import Moore57.BranchOrbitABCEquationInvariantCoordinateBoundary

/-!
# Endpoint matching via adjacency transport

This file isolates the endpoint matching/reflection boundary at the adjacency
level.  The main boundary says that a matched endpoint edge, after applying
the A-fixing reflection on the source coordinate, lands on the expected
rotated target vertex.  The conversion back to the existing coordinate
matching equality is formal through `AFiberCoordinates.matchingEquiv_eq_of_adj`.
-/

namespace Moore57

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

namespace BranchOrbitABCReflectionLabeling

variable {h : D19ActsOnMoore57 V Γ}

/-- Endpoint matching after the A-fixing reflection, stated only as adjacency
between the reflected source coordinate and the expected rotated target
coordinate. -/
structure EndpointMatchingAFixingAdjacencyTransportBoundary
    (labeling : BranchOrbitABCReflectionLabeling h) : Prop where
  aFiberReflection_matching_adj_rotation :
    ∀ d : ZMod 19, ∀ hd : d ≠ 0,
      ∀ p : labeling.data.toAFiberCoordinates.P,
        AFiberCoordinates.matchingEquiv h.isMoore
            labeling.data.toAFiberCoordinates 0 (0 + d)
            (index_ne_add_of_ne_zero hd) p =
          labeling.data.toAFiberRotationEquivariance.coordPerm d 0
            (labeling.aFiberReflectionCoordPerm p) →
        Γ.Adj
          (((labeling.data.toAFiberCoordinates.coord 0
              (labeling.aFiberReflectionCoordPerm p) :
            {x : V // x ∈
              branchFiber Γ labeling.data.toAFiberCoordinates.u
                (labeling.data.toAFiberCoordinates.a 0)}) : V))
          (((labeling.data.toAFiberCoordinates.coord (0 + d)
              (labeling.data.toAFiberRotationEquivariance.coordPerm d 0 p) :
            {x : V // x ∈
              branchFiber Γ labeling.data.toAFiberCoordinates.u
                (labeling.data.toAFiberCoordinates.a (0 + d))}) : V))

namespace EndpointMatchingAFixingAdjacencyTransportBoundary

variable {labeling : BranchOrbitABCReflectionLabeling h}

/-- The adjacency-transport endpoint boundary implies the existing endpoint
matching equality boundary. -/
def toEndpointMatchingAFixingCoordinateBoundary
    (boundary : EndpointMatchingAFixingAdjacencyTransportBoundary labeling) :
    EndpointMatchingAFixingCoordinateBoundary labeling where
  aFiberReflection_matching_eq_rotation := by
    intro d hd p hp
    exact
      AFiberCoordinates.matchingEquiv_eq_of_adj h.isMoore
        labeling.data.toAFiberCoordinates (index_ne_add_of_ne_zero hd)
        (boundary.aFiberReflection_matching_adj_rotation d hd p hp)

/-- Direct connector from adjacency transport to the midpoint-equation-set
invariance boundary already used downstream. -/
def toMidpointEquationSetAFixingInvariantBoundary
    (boundary : EndpointMatchingAFixingAdjacencyTransportBoundary labeling) :
    MidpointEquationSetAFixingInvariantBoundary labeling :=
  boundary.toEndpointMatchingAFixingCoordinateBoundary
    |>.toMidpointEquationSetAFixingInvariantBoundary

end EndpointMatchingAFixingAdjacencyTransportBoundary

/-- Smaller vertex-level boundary: after reflecting the original matched
target endpoint, the resulting vertex is the expected rotated endpoint for
the unreflected coordinate.  This is intentionally separated from adjacency
transport because this target-identification is the geometric content. -/
structure EndpointMatchingAFixingTargetReflectionBoundary
    (labeling : BranchOrbitABCReflectionLabeling h) : Prop where
  aFiberReflection_target_vertex_eq :
    ∀ d : ZMod 19, ∀ hd : d ≠ 0,
      ∀ p : labeling.data.toAFiberCoordinates.P,
        AFiberCoordinates.matchingEquiv h.isMoore
            labeling.data.toAFiberCoordinates 0 (0 + d)
            (index_ne_add_of_ne_zero hd) p =
          labeling.data.toAFiberRotationEquivariance.coordPerm d 0
            (labeling.aFiberReflectionCoordPerm p) →
        h.smul (DihedralGroup.sr labeling.aFixingReflectionIndex)
          (((labeling.data.toAFiberCoordinates.coord (0 + d)
              (labeling.data.toAFiberRotationEquivariance.coordPerm d 0
                (labeling.aFiberReflectionCoordPerm p)) :
            {x : V // x ∈
              branchFiber Γ labeling.data.toAFiberCoordinates.u
                (labeling.data.toAFiberCoordinates.a (0 + d))}) : V)) =
          (((labeling.data.toAFiberCoordinates.coord (0 + d)
              (labeling.data.toAFiberRotationEquivariance.coordPerm d 0 p) :
            {x : V // x ∈
              branchFiber Γ labeling.data.toAFiberCoordinates.u
                (labeling.data.toAFiberCoordinates.a (0 + d))}) : V))

namespace EndpointMatchingAFixingTargetReflectionBoundary

variable {labeling : BranchOrbitABCReflectionLabeling h}

/-- A target-vertex reflection boundary gives adjacency transport: convert the
input matching equality to adjacency, apply reflection adjacency preservation,
then identify the reflected source and target coordinates. -/
def toEndpointMatchingAFixingAdjacencyTransportBoundary
    (boundary : EndpointMatchingAFixingTargetReflectionBoundary labeling) :
    EndpointMatchingAFixingAdjacencyTransportBoundary labeling where
  aFiberReflection_matching_adj_rotation := by
    intro d hd p hp
    let coords := labeling.data.toAFiberCoordinates
    let target :=
      labeling.data.toAFiberRotationEquivariance.coordPerm d 0
        (labeling.aFiberReflectionCoordPerm p)
    have hadj :
        Γ.Adj
          (((coords.coord 0 p :
            {x : V // x ∈ branchFiber Γ coords.u (coords.a 0)}) : V))
          (((coords.coord (0 + d) target :
            {x : V // x ∈ branchFiber Γ coords.u (coords.a (0 + d))}) : V)) :=
      (AFiberCoordinates.adj_iff_matchingEquiv_eq h.isMoore
        coords (index_ne_add_of_ne_zero hd) p target).2 hp
    have hadj_reflected :
        Γ.Adj
          (h.smul (DihedralGroup.sr labeling.aFixingReflectionIndex)
            (((coords.coord 0 p :
              {x : V // x ∈ branchFiber Γ coords.u (coords.a 0)}) : V)))
          (h.smul (DihedralGroup.sr labeling.aFixingReflectionIndex)
            (((coords.coord (0 + d) target :
              {x : V // x ∈ branchFiber Γ coords.u (coords.a (0 + d))}) :
              V))) :=
      (h.smul_adj (DihedralGroup.sr labeling.aFixingReflectionIndex)
        (((coords.coord 0 p :
          {x : V // x ∈ branchFiber Γ coords.u (coords.a 0)}) : V))
        (((coords.coord (0 + d) target :
          {x : V // x ∈ branchFiber Γ coords.u (coords.a (0 + d))}) : V))).mp hadj
    have hsource :
        h.smul (DihedralGroup.sr labeling.aFixingReflectionIndex)
            (((coords.coord 0 p :
              {x : V // x ∈ branchFiber Γ coords.u (coords.a 0)}) : V)) =
          (((coords.coord 0 (labeling.aFiberReflectionCoordPerm p) :
            {x : V // x ∈ branchFiber Γ coords.u (coords.a 0)}) : V)) := by
      simpa [coords] using (labeling.coord_aFiberReflectionCoordPerm_apply_val p).symm
    have htarget :
        h.smul (DihedralGroup.sr labeling.aFixingReflectionIndex)
          (((coords.coord (0 + d) target :
            {x : V // x ∈ branchFiber Γ coords.u (coords.a (0 + d))}) : V)) =
          (((coords.coord (0 + d)
              (labeling.data.toAFiberRotationEquivariance.coordPerm d 0 p) :
            {x : V // x ∈ branchFiber Γ coords.u (coords.a (0 + d))}) : V)) := by
      simpa [coords, target] using
        boundary.aFiberReflection_target_vertex_eq d hd p hp
    rw [hsource, htarget] at hadj_reflected
    simpa [coords] using hadj_reflected

/-- Direct connector from the target-vertex boundary to the existing endpoint
matching equality boundary. -/
def toEndpointMatchingAFixingCoordinateBoundary
    (boundary : EndpointMatchingAFixingTargetReflectionBoundary labeling) :
    EndpointMatchingAFixingCoordinateBoundary labeling :=
  boundary.toEndpointMatchingAFixingAdjacencyTransportBoundary
    |>.toEndpointMatchingAFixingCoordinateBoundary

end EndpointMatchingAFixingTargetReflectionBoundary

/-- The sign-correct endpoint obtained by reflecting a rotated A-reflected
target.  Reflection sends the rotation offset `d` to `-d`; this records the
formal coordinate statement that follows from the existing coordinate APIs. -/
theorem aFiberReflection_rotationCoordPerm_aFiberReflectionCoordPerm_vertex_eq
    (labeling : BranchOrbitABCReflectionLabeling h)
    (d : ZMod 19) (p : labeling.data.toAFiberCoordinates.P) :
    h.smul (DihedralGroup.sr labeling.aFixingReflectionIndex)
        (((labeling.data.toAFiberCoordinates.coord (0 + d)
            (labeling.data.toAFiberRotationEquivariance.coordPerm d 0
              (labeling.aFiberReflectionCoordPerm p)) :
          {x : V // x ∈
            branchFiber Γ labeling.data.toAFiberCoordinates.u
              (labeling.data.toAFiberCoordinates.a (0 + d))}) : V)) =
      (((labeling.data.toAFiberCoordinates.coord (0 + (-d))
          (labeling.data.toAFiberRotationEquivariance.coordPerm (-d) 0 p) :
        {x : V // x ∈
          branchFiber Γ labeling.data.toAFiberCoordinates.u
            (labeling.data.toAFiberCoordinates.a (0 + (-d)))}) : V)) := by
  let coords := labeling.data.toAFiberCoordinates
  have htarget :
      (((coords.coord (0 + d)
          (labeling.data.toAFiberRotationEquivariance.coordPerm d 0
            (labeling.aFiberReflectionCoordPerm p)) :
        {x : V // x ∈ branchFiber Γ coords.u (coords.a (0 + d))}) : V)) =
        h.rotation d
          (((coords.coord 0 (labeling.aFiberReflectionCoordPerm p) :
            {x : V // x ∈ branchFiber Γ coords.u (coords.a 0)}) : V)) := by
    simpa [coords] using
      AFiberRotationEquivariance.coord_coordPerm_apply_val
        (rot := labeling.data.toAFiberRotationEquivariance)
        (d := d) (i := 0)
        (p := labeling.aFiberReflectionCoordPerm p)
  have hsource_reflect :
      h.smul (DihedralGroup.sr labeling.aFixingReflectionIndex)
          (((coords.coord 0 (labeling.aFiberReflectionCoordPerm p) :
            {x : V // x ∈ branchFiber Γ coords.u (coords.a 0)}) : V)) =
        (((coords.coord 0 p :
          {x : V // x ∈ branchFiber Γ coords.u (coords.a 0)}) : V)) := by
    have hcoord :
        (((coords.coord 0 (labeling.aFiberReflectionCoordPerm p) :
          {x : V // x ∈ branchFiber Γ coords.u (coords.a 0)}) : V)) =
          h.smul (DihedralGroup.sr labeling.aFixingReflectionIndex)
            (((coords.coord 0 p :
              {x : V // x ∈ branchFiber Γ coords.u (coords.a 0)}) : V)) := by
      simpa [coords] using labeling.coord_aFiberReflectionCoordPerm_apply_val p
    rw [hcoord]
    exact h.reflection_smul_reflection_smul labeling.aFixingReflectionIndex
      (((coords.coord 0 p :
        {x : V // x ∈ branchFiber Γ coords.u (coords.a 0)}) : V))
  have hneg_target :
      (((coords.coord (0 + (-d))
          (labeling.data.toAFiberRotationEquivariance.coordPerm (-d) 0 p) :
        {x : V // x ∈ branchFiber Γ coords.u (coords.a (0 + (-d)))}) : V)) =
        h.rotation (-d)
          (((coords.coord 0 p :
            {x : V // x ∈ branchFiber Γ coords.u (coords.a 0)}) : V)) := by
    simpa [coords] using
      AFiberRotationEquivariance.coord_coordPerm_apply_val
        (rot := labeling.data.toAFiberRotationEquivariance)
        (d := -d) (i := 0) (p := p)
  calc
    h.smul (DihedralGroup.sr labeling.aFixingReflectionIndex)
        (((coords.coord (0 + d)
            (labeling.data.toAFiberRotationEquivariance.coordPerm d 0
              (labeling.aFiberReflectionCoordPerm p)) :
          {x : V // x ∈ branchFiber Γ coords.u (coords.a (0 + d))}) : V))
        = h.smul (DihedralGroup.sr labeling.aFixingReflectionIndex)
            (h.rotation d
              (((coords.coord 0 (labeling.aFiberReflectionCoordPerm p) :
                {x : V // x ∈ branchFiber Γ coords.u (coords.a 0)}) : V))) := by
              rw [htarget]
    _ = h.rotation (-d)
        (h.smul (DihedralGroup.sr labeling.aFixingReflectionIndex)
          (((coords.coord 0 (labeling.aFiberReflectionCoordPerm p) :
            {x : V // x ∈ branchFiber Γ coords.u (coords.a 0)}) : V))) := by
          rw [h.reflection_smul_rotation]
    _ = h.rotation (-d)
        (((coords.coord 0 p :
          {x : V // x ∈ branchFiber Γ coords.u (coords.a 0)}) : V)) := by
          rw [hsource_reflect]
    _ = (((coords.coord (0 + (-d))
          (labeling.data.toAFiberRotationEquivariance.coordPerm (-d) 0 p) :
        {x : V // x ∈ branchFiber Γ coords.u (coords.a (0 + (-d)))}) : V)) :=
          hneg_target.symm

end BranchOrbitABCReflectionLabeling

end

end Moore57
