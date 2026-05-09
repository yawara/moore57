import Moore57.BranchOrbitABCMatchingAdjacencyTransportBoundary

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
