import Moore57.BranchOrbitABCMatchingAdjacencyTransportBoundary
import Moore57.AFiberMatchingPerm

/-!
# Endpoint target reflection reduced to target sign compatibility

The existing target-reflection calculation sends the target endpoint at offset
`d` to the rotated target endpoint at offset `-d`.  This file isolates the
remaining sign step: identify that `-d` target endpoint with the desired `d`
target endpoint under the endpoint matching premise.  The rest of the endpoint
matching compatibility then follows from the existing transport pipeline.
-/

namespace Moore57

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

namespace BranchOrbitABCReflectionLabeling

variable {h : D19ActsOnMoore57 V Γ}

/-- Reduced target-sign boundary for endpoint matching under the A-fixing
reflection.

The formal reflection calculation already identifies the reflected target at
offset `d` with the coordinate target at offset `-d`.  This boundary is exactly
the remaining compatibility needed to return to the endpoint target at offset
`d`. -/
structure EndpointMatchingAFixingTargetSignBoundary
    (labeling : BranchOrbitABCReflectionLabeling h) : Prop where
  aFiberReflection_target_sign_vertex_eq :
    ∀ d : ZMod 19, ∀ hd : d ≠ 0,
      ∀ p : labeling.data.toAFiberCoordinates.P,
        AFiberCoordinates.matchingEquiv h.isMoore
            labeling.data.toAFiberCoordinates 0 (0 + d)
            (index_ne_add_of_ne_zero hd) p =
          labeling.data.toAFiberRotationEquivariance.coordPerm d 0
            (labeling.aFiberReflectionCoordPerm p) →
        (((labeling.data.toAFiberCoordinates.coord (0 + (-d))
            (labeling.data.toAFiberRotationEquivariance.coordPerm (-d) 0 p) :
          {x : V // x ∈
            branchFiber Γ labeling.data.toAFiberCoordinates.u
              (labeling.data.toAFiberCoordinates.a (0 + (-d)))}) : V)) =
          (((labeling.data.toAFiberCoordinates.coord (0 + d)
              (labeling.data.toAFiberRotationEquivariance.coordPerm d 0 p) :
            {x : V // x ∈
              branchFiber Γ labeling.data.toAFiberCoordinates.u
                (labeling.data.toAFiberCoordinates.a (0 + d))}) : V))

/-- Diagnostic no-premise form of endpoint target-sign compatibility.  Since
the target-sign equality identifies vertices in the distinct `d` and `-d`
A-side fibers, the usable proof route is to show that the matching premise is
impossible. -/
structure EndpointMatchingAFixingNoPositiveTargetBoundary
    (labeling : BranchOrbitABCReflectionLabeling h) : Prop where
  no_positive_target_matching :
    ∀ d : ZMod 19, ∀ hd : d ≠ 0,
      ∀ p : labeling.data.toAFiberCoordinates.P,
        ¬ AFiberCoordinates.matchingEquiv h.isMoore
            labeling.data.toAFiberCoordinates 0 (0 + d)
            (index_ne_add_of_ne_zero hd) p =
          labeling.data.toAFiberRotationEquivariance.coordPerm d 0
            (labeling.aFiberReflectionCoordPerm p)

namespace EndpointMatchingAFixingNoPositiveTargetBoundary

variable {labeling : BranchOrbitABCReflectionLabeling h}

/-- If the positive target-matching premise never occurs, the target-sign
boundary follows vacuously. -/
def toEndpointMatchingAFixingTargetSignBoundary
    (boundary : EndpointMatchingAFixingNoPositiveTargetBoundary labeling) :
    EndpointMatchingAFixingTargetSignBoundary labeling where
  aFiberReflection_target_sign_vertex_eq := by
    intro d hd p hp
    exact False.elim
      (boundary.no_positive_target_matching d hd p hp)

end EndpointMatchingAFixingNoPositiveTargetBoundary

/-- Correct non-circular endpoint transport under the A-fixing reflection.
Reflecting a positive-offset endpoint matching equation produces the
negative-offset equation; it does not identify the `d` and `-d` endpoint
targets. -/
structure EndpointMatchingAFixingNegativeOffsetBoundary
    (labeling : BranchOrbitABCReflectionLabeling h) : Prop where
  aFiberReflection_matching_eq_rotation_neg :
    ∀ d : ZMod 19, ∀ hd : d ≠ 0,
      ∀ p : labeling.data.toAFiberCoordinates.P,
        AFiberCoordinates.matchingEquiv h.isMoore
            labeling.data.toAFiberCoordinates 0 (0 + d)
            (index_ne_add_of_ne_zero hd) p =
          labeling.data.toAFiberRotationEquivariance.coordPerm d 0
            (labeling.aFiberReflectionCoordPerm p) →
        AFiberCoordinates.matchingEquiv h.isMoore
            labeling.data.toAFiberCoordinates 0 (0 + (-d))
            (index_ne_add_of_ne_zero (neg_ne_zero.mpr hd))
            (labeling.aFiberReflectionCoordPerm p) =
          labeling.data.toAFiberRotationEquivariance.coordPerm (-d) 0 p

/-- The negative-offset transport boundary follows directly from adjacency
transport and the formal A-fixing reflection calculation. -/
def endpointMatchingAFixingNegativeOffsetBoundary
    (labeling : BranchOrbitABCReflectionLabeling h) :
    EndpointMatchingAFixingNegativeOffsetBoundary labeling where
  aFiberReflection_matching_eq_rotation_neg := by
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
          {x : V // x ∈ branchFiber Γ coords.u (coords.a (0 + d))}) : V))).mp
        hadj
    have hsource :
        h.smul (DihedralGroup.sr labeling.aFixingReflectionIndex)
            (((coords.coord 0 p :
              {x : V // x ∈ branchFiber Γ coords.u (coords.a 0)}) : V)) =
          (((coords.coord 0 (labeling.aFiberReflectionCoordPerm p) :
            {x : V // x ∈ branchFiber Γ coords.u (coords.a 0)}) : V)) := by
      simpa [coords] using
        (labeling.coord_aFiberReflectionCoordPerm_apply_val p).symm
    have htarget :
        h.smul (DihedralGroup.sr labeling.aFixingReflectionIndex)
            (((coords.coord (0 + d) target :
              {x : V // x ∈ branchFiber Γ coords.u (coords.a (0 + d))}) :
              V)) =
          (((coords.coord (0 + (-d))
              (labeling.data.toAFiberRotationEquivariance.coordPerm (-d) 0 p) :
            {x : V // x ∈ branchFiber Γ coords.u (coords.a (0 + (-d)))}) :
            V)) := by
      simpa [coords, target] using
        labeling.aFiberReflection_rotationCoordPerm_aFiberReflectionCoordPerm_vertex_eq
          d p
    rw [hsource, htarget] at hadj_reflected
    exact
      AFiberCoordinates.matchingEquiv_eq_of_adj h.isMoore
        coords (index_ne_add_of_ne_zero (neg_ne_zero.mpr hd))
        (by simpa [coords] using hadj_reflected)

namespace EndpointMatchingAFixingTargetSignBoundary

variable {labeling : BranchOrbitABCReflectionLabeling h}

/-- The reduced sign boundary upgrades the proven `d ↦ -d` reflected-target
identity to the existing exact target-reflection boundary at offset `d`. -/
def toEndpointMatchingAFixingTargetReflectionBoundary
    (boundary : EndpointMatchingAFixingTargetSignBoundary labeling) :
    EndpointMatchingAFixingTargetReflectionBoundary labeling where
  aFiberReflection_target_vertex_eq := by
    intro d hd p hp
    calc
      h.smul (DihedralGroup.sr labeling.aFixingReflectionIndex)
          (((labeling.data.toAFiberCoordinates.coord (0 + d)
              (labeling.data.toAFiberRotationEquivariance.coordPerm d 0
                (labeling.aFiberReflectionCoordPerm p)) :
            {x : V // x ∈
              branchFiber Γ labeling.data.toAFiberCoordinates.u
                (labeling.data.toAFiberCoordinates.a (0 + d))}) : V))
          =
        (((labeling.data.toAFiberCoordinates.coord (0 + (-d))
            (labeling.data.toAFiberRotationEquivariance.coordPerm (-d) 0 p) :
          {x : V // x ∈
            branchFiber Γ labeling.data.toAFiberCoordinates.u
              (labeling.data.toAFiberCoordinates.a (0 + (-d)))}) : V)) := by
          exact
            aFiberReflection_rotationCoordPerm_aFiberReflectionCoordPerm_vertex_eq
              labeling d p
      _ =
        (((labeling.data.toAFiberCoordinates.coord (0 + d)
            (labeling.data.toAFiberRotationEquivariance.coordPerm d 0 p) :
          {x : V // x ∈
            branchFiber Γ labeling.data.toAFiberCoordinates.u
              (labeling.data.toAFiberCoordinates.a (0 + d))}) : V)) :=
          boundary.aFiberReflection_target_sign_vertex_eq d hd p hp

/-- The reduced sign boundary gives adjacency transport for endpoint matching. -/
def toEndpointMatchingAFixingAdjacencyTransportBoundary
    (boundary : EndpointMatchingAFixingTargetSignBoundary labeling) :
    EndpointMatchingAFixingAdjacencyTransportBoundary labeling :=
  boundary.toEndpointMatchingAFixingTargetReflectionBoundary
    |>.toEndpointMatchingAFixingAdjacencyTransportBoundary

/-- The reduced sign boundary gives the endpoint matching coordinate boundary
used by the reduced coordinate witness package. -/
def toEndpointMatchingAFixingCoordinateBoundary
    (boundary : EndpointMatchingAFixingTargetSignBoundary labeling) :
    EndpointMatchingAFixingCoordinateBoundary labeling :=
  boundary.toEndpointMatchingAFixingTargetReflectionBoundary
    |>.toEndpointMatchingAFixingCoordinateBoundary

/-- Direct connector from target sign compatibility to midpoint-equation-set
invariance. -/
def toMidpointEquationSetAFixingInvariantBoundary
    (boundary : EndpointMatchingAFixingTargetSignBoundary labeling) :
    MidpointEquationSetAFixingInvariantBoundary labeling :=
  boundary.toEndpointMatchingAFixingCoordinateBoundary
    |>.toMidpointEquationSetAFixingInvariantBoundary

/-- The two endpoint targets that `EndpointMatchingAFixingTargetSignBoundary`
would identify live in different A-side branch fibers when `d ≠ 0`. -/
theorem target_sign_vertices_ne
    (d : ZMod 19) (hd : d ≠ 0)
    (p : labeling.data.toAFiberCoordinates.P) :
    (((labeling.data.toAFiberCoordinates.coord (0 + (-d))
        (labeling.data.toAFiberRotationEquivariance.coordPerm (-d) 0 p) :
      {x : V // x ∈
        branchFiber Γ labeling.data.toAFiberCoordinates.u
          (labeling.data.toAFiberCoordinates.a (0 + (-d)))}) : V)) ≠
      (((labeling.data.toAFiberCoordinates.coord (0 + d)
          (labeling.data.toAFiberRotationEquivariance.coordPerm d 0 p) :
        {x : V // x ∈
          branchFiber Γ labeling.data.toAFiberCoordinates.u
            (labeling.data.toAFiberCoordinates.a (0 + d))}) : V)) := by
  exact
    AFiberCoordinates.coord_ne_of_index_ne h.isMoore
      labeling.data.toAFiberCoordinates
      (by simpa using neg_ne_self_zmod19 hd) _ _

/-- Consequently, the target-sign boundary can only apply vacuously: its
matching premise is impossible at every nonzero offset. -/
theorem no_target_sign_matching_premise
    (boundary : EndpointMatchingAFixingTargetSignBoundary labeling)
    (d : ZMod 19) (hd : d ≠ 0)
    (p : labeling.data.toAFiberCoordinates.P) :
    ¬ AFiberCoordinates.matchingEquiv h.isMoore
        labeling.data.toAFiberCoordinates 0 (0 + d)
        (index_ne_add_of_ne_zero hd) p =
      labeling.data.toAFiberRotationEquivariance.coordPerm d 0
        (labeling.aFiberReflectionCoordPerm p) := by
  intro hp
  exact target_sign_vertices_ne (labeling := labeling) d hd p
    (boundary.aFiberReflection_target_sign_vertex_eq d hd p hp)

/-- The target-sign boundary is equivalent to the diagnostic no-premise form. -/
def toEndpointMatchingAFixingNoPositiveTargetBoundary
    (boundary : EndpointMatchingAFixingTargetSignBoundary labeling) :
    EndpointMatchingAFixingNoPositiveTargetBoundary labeling where
  no_positive_target_matching :=
    boundary.no_target_sign_matching_premise

end EndpointMatchingAFixingTargetSignBoundary

/-- Constructor form of the reduced target-sign boundary. -/
def endpointMatchingAFixingCoordinateBoundary_of_targetSign
    (labeling : BranchOrbitABCReflectionLabeling h)
    (aFiberReflection_target_sign_vertex_eq :
      ∀ d : ZMod 19, ∀ hd : d ≠ 0,
        ∀ p : labeling.data.toAFiberCoordinates.P,
          AFiberCoordinates.matchingEquiv h.isMoore
              labeling.data.toAFiberCoordinates 0 (0 + d)
              (index_ne_add_of_ne_zero hd) p =
            labeling.data.toAFiberRotationEquivariance.coordPerm d 0
              (labeling.aFiberReflectionCoordPerm p) →
          (((labeling.data.toAFiberCoordinates.coord (0 + (-d))
              (labeling.data.toAFiberRotationEquivariance.coordPerm (-d) 0 p) :
            {x : V // x ∈
              branchFiber Γ labeling.data.toAFiberCoordinates.u
                (labeling.data.toAFiberCoordinates.a (0 + (-d)))}) : V)) =
            (((labeling.data.toAFiberCoordinates.coord (0 + d)
                (labeling.data.toAFiberRotationEquivariance.coordPerm d 0 p) :
              {x : V // x ∈
                branchFiber Γ labeling.data.toAFiberCoordinates.u
                  (labeling.data.toAFiberCoordinates.a (0 + d))}) : V))) :
    EndpointMatchingAFixingCoordinateBoundary labeling :=
  (EndpointMatchingAFixingTargetSignBoundary.mk
      aFiberReflection_target_sign_vertex_eq)
    |>.toEndpointMatchingAFixingCoordinateBoundary

end BranchOrbitABCReflectionLabeling

end

end Moore57
