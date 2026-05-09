import Moore57.BranchOrbitABCEndpointCommonNeighborBasic
import Moore57.BranchOrbitABCMatchingTargetReflectionReduced

/-!
# Endpoint sign adjacency boundary

This file records the formal part of the remaining endpoint common-neighbor
adjacency.  Reflecting the original endpoint edge gives adjacency to the
A-fixing-reflected reference coordinate.  The only leftover endpoint-sign
input is the ability to replace that reflected reference coordinate by the
original reference coordinate.
-/

namespace Moore57

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

namespace BranchOrbitABCReflectionLabeling

variable {h : D19ActsOnMoore57 V Γ}

private theorem neg_ne_zero_of_ne_zero_zmod19 {d : ZMod 19} (hd : d ≠ 0) :
    -d ≠ 0 := by
  exact neg_ne_zero.mpr hd

/-- Reflecting the endpoint-adjacency hypothesis gives the desired reflected
endpoint adjacent to the reflected reference coordinate.  This is the part
that follows formally from adjacency preservation and the existing endpoint
reflection lemmas. -/
theorem aFixing_reflected_endpoint_adj_reflected_reference_of_endpoint_adj
    (labeling : BranchOrbitABCReflectionLabeling h)
    (d : ZMod 19) (p : labeling.data.toAFiberCoordinates.P)
    (hadj :
      Γ.Adj
        (labeling.endpointCommonNeighborReferenceVertex p)
        (labeling.endpointCommonNeighborReflectedEndpointVertex d p)) :
    Γ.Adj
      (labeling.endpointCommonNeighborAFixingReflectedEndpointVertex d p)
      (labeling.endpointCommonNeighborReferenceVertex
        (labeling.aFiberReflectionCoordPerm p)) := by
  have hadjReflected :
      Γ.Adj
        (h.smul (DihedralGroup.sr labeling.aFixingReflectionIndex)
          (labeling.endpointCommonNeighborReferenceVertex p))
        (h.smul (DihedralGroup.sr labeling.aFixingReflectionIndex)
          (labeling.endpointCommonNeighborReflectedEndpointVertex d p)) :=
    (h.smul_adj (DihedralGroup.sr labeling.aFixingReflectionIndex)
      (labeling.endpointCommonNeighborReferenceVertex p)
      (labeling.endpointCommonNeighborReflectedEndpointVertex d p)).mp hadj
  have hreference :
      h.smul (DihedralGroup.sr labeling.aFixingReflectionIndex)
          (labeling.endpointCommonNeighborReferenceVertex p) =
        labeling.endpointCommonNeighborReferenceVertex
          (labeling.aFiberReflectionCoordPerm p) := by
    simpa [endpointCommonNeighborReferenceVertex] using
      (labeling.coord_aFiberReflectionCoordPerm_apply_val p).symm
  have hendpoint :
      h.smul (DihedralGroup.sr labeling.aFixingReflectionIndex)
          (labeling.endpointCommonNeighborReflectedEndpointVertex d p) =
        labeling.endpointCommonNeighborAFixingReflectedEndpointVertex d p :=
    labeling.aFixingReflection_endpointCommonNeighborReflectedEndpointVertex d p
  rw [hreference, hendpoint] at hadjReflected
  exact hadjReflected.symm

/-- The original endpoint adjacency gives exactly the positive-sign target
matching premise used by `EndpointMatchingAFixingTargetSignBoundary`. -/
theorem endpoint_targetSign_hyp_of_endpoint_adj
    (labeling : BranchOrbitABCReflectionLabeling h)
    (d : ZMod 19) (hd : d ≠ 0)
    (p : labeling.data.toAFiberCoordinates.P)
    (hadj :
      Γ.Adj
        (labeling.endpointCommonNeighborReferenceVertex p)
        (labeling.endpointCommonNeighborReflectedEndpointVertex d p)) :
    AFiberCoordinates.matchingEquiv h.isMoore
        labeling.data.toAFiberCoordinates 0 (0 + d)
        (index_ne_add_of_ne_zero hd) p =
      labeling.data.toAFiberRotationEquivariance.coordPerm d 0
        (labeling.aFiberReflectionCoordPerm p) := by
  let coords := labeling.data.toAFiberCoordinates
  have hdd : midpointOf d + midpointOf d = d := midpointOf_add_self d
  have hendpoint :
      labeling.endpointCommonNeighborReflectedEndpointVertex d p =
        (((coords.coord (0 + d)
            (labeling.data.toAFiberRotationEquivariance.coordPerm d 0
              (labeling.aFiberReflectionCoordPerm p)) :
          {x : V // x ∈ branchFiber Γ coords.u (coords.a (0 + d))}) : V)) := by
    have hidx : (0 + (midpointOf d + midpointOf d) : ZMod 19) = 0 + d := by
      simp [hdd]
    have hperm :
        labeling.midpointReflectionCoordPerm (midpointOf d) p =
          labeling.data.toAFiberRotationEquivariance.coordPerm d 0
            (labeling.aFiberReflectionCoordPerm p) := by
      simpa [hdd] using
        labeling.midpointReflectionCoordPerm_eq_rotationCoordPerm_aFiberReflectionCoordPerm
          (midpointOf d) p
    rw [endpointCommonNeighborReflectedEndpointVertex, hperm, hidx]
  exact
    (AFiberCoordinates.adj_iff_matchingEquiv_eq h.isMoore coords
      (index_ne_add_of_ne_zero hd) p
      (labeling.data.toAFiberRotationEquivariance.coordPerm d 0
        (labeling.aFiberReflectionCoordPerm p))).1
      (by
        simpa [endpointCommonNeighborReferenceVertex, coords, hendpoint] using
          hadj)

/-- Under the target-sign boundary, endpoint adjacency identifies the
A-fixing-reflected endpoint with the sign-correct positive target endpoint.
This is a target-identification reduction; it does not by itself change the
reference coordinate back from `aFiberReflectionCoordPerm p` to `p`. -/
theorem endpointCommonNeighborAFixingReflectedEndpointVertex_eq_target_of_endpoint_adj
    (labeling : BranchOrbitABCReflectionLabeling h)
    (targetSign : EndpointMatchingAFixingTargetSignBoundary labeling)
    (d : ZMod 19) (hd : d ≠ 0)
    (p : labeling.data.toAFiberCoordinates.P)
    (hadj :
      Γ.Adj
        (labeling.endpointCommonNeighborReferenceVertex p)
        (labeling.endpointCommonNeighborReflectedEndpointVertex d p)) :
    labeling.endpointCommonNeighborAFixingReflectedEndpointVertex d p =
      (((labeling.data.toAFiberCoordinates.coord (0 + d)
          (labeling.data.toAFiberRotationEquivariance.coordPerm d 0 p) :
        {x : V // x ∈
          branchFiber Γ labeling.data.toAFiberCoordinates.u
            (labeling.data.toAFiberCoordinates.a (0 + d))}) : V)) := by
  simpa [endpointCommonNeighborAFixingReflectedEndpointVertex] using
    targetSign.aFiberReflection_target_sign_vertex_eq d hd p
      (labeling.endpoint_targetSign_hyp_of_endpoint_adj d hd p hadj)

/-- Remaining endpoint-sign adjacency boundary.  The reflected edge supplies
adjacency to the reflected reference coordinate; this boundary is exactly the
extra input needed to retarget that adjacency to the original reference
coordinate. -/
structure EndpointSignAdjacencyBoundary
    (labeling : BranchOrbitABCReflectionLabeling h) : Prop where
  endpoint_adj_reference_of_reflected_reference_adj :
    ∀ d : ZMod 19, ∀ _hd : d ≠ 0,
      ∀ p : labeling.data.toAFiberCoordinates.P,
        p ∈ labeling.aFiberReflectionSupport →
          Γ.Adj
            (labeling.endpointCommonNeighborAFixingReflectedEndpointVertex d p)
            (labeling.endpointCommonNeighborReferenceVertex
              (labeling.aFiberReflectionCoordPerm p)) →
          Γ.Adj
            (labeling.endpointCommonNeighborAFixingReflectedEndpointVertex d p)
            (labeling.endpointCommonNeighborReferenceVertex p)

namespace EndpointSignAdjacencyBoundary

variable {labeling : BranchOrbitABCReflectionLabeling h}

/-- The endpoint-sign adjacency boundary supplies the remaining adjacency
expected by the existing basic endpoint common-neighbor boundary. -/
def toMidpointExceptionEndpointAdjCommonNeighborBasicBoundary
    (boundary : EndpointSignAdjacencyBoundary labeling) :
    MidpointExceptionEndpointAdjCommonNeighborBasicBoundary labeling where
  aFixing_reflected_endpoint_adj_reference_of_endpoint_adj := by
    intro d hd p hp hadj
    exact
      boundary.endpoint_adj_reference_of_reflected_reference_adj d hd p hp
        (labeling.aFixing_reflected_endpoint_adj_reflected_reference_of_endpoint_adj
          d p hadj)

/-- Direct connector to the fixedness boundary already used downstream. -/
def toMidpointExceptionEndpointAdjForcesAFixingFixedBoundary
    (boundary : EndpointSignAdjacencyBoundary labeling) :
    MidpointExceptionEndpointAdjForcesAFixingFixedBoundary labeling :=
  boundary.toMidpointExceptionEndpointAdjCommonNeighborBasicBoundary
    |>.toMidpointExceptionEndpointAdjForcesAFixingFixedBoundary

end EndpointSignAdjacencyBoundary

/-- Matching-equation version of `EndpointSignAdjacencyBoundary`.  It asks
only for the sign/endpoint matching step that changes the source coordinate in
the `0` A-fiber from the reflected coordinate back to the original coordinate,
with the same negative-sign endpoint target. -/
structure EndpointSignMatchingBoundary
    (labeling : BranchOrbitABCReflectionLabeling h) : Prop where
  endpoint_neg_matching_of_reflected_reference_neg_matching :
    ∀ d : ZMod 19, ∀ hd : d ≠ 0,
      ∀ p : labeling.data.toAFiberCoordinates.P,
        p ∈ labeling.aFiberReflectionSupport →
          AFiberCoordinates.matchingEquiv h.isMoore
              labeling.data.toAFiberCoordinates 0 (0 + (-d))
              (index_ne_add_of_ne_zero
                (neg_ne_zero_of_ne_zero_zmod19 hd))
              (labeling.aFiberReflectionCoordPerm p) =
            labeling.data.toAFiberRotationEquivariance.coordPerm (-d) 0 p →
          AFiberCoordinates.matchingEquiv h.isMoore
              labeling.data.toAFiberCoordinates 0 (0 + (-d))
              (index_ne_add_of_ne_zero
                (neg_ne_zero_of_ne_zero_zmod19 hd)) p =
            labeling.data.toAFiberRotationEquivariance.coordPerm (-d) 0 p

namespace EndpointSignMatchingBoundary

variable {labeling : BranchOrbitABCReflectionLabeling h}

/-- Convert the matching-equation sign boundary to the adjacency sign
boundary by the A-fiber matching adjacency equivalence. -/
def toEndpointSignAdjacencyBoundary
    (boundary : EndpointSignMatchingBoundary labeling) :
    EndpointSignAdjacencyBoundary labeling where
  endpoint_adj_reference_of_reflected_reference_adj := by
    intro d hd p hp hadjReflectedReference
    let coords := labeling.data.toAFiberCoordinates
    let hneg : -d ≠ 0 := neg_ne_zero_of_ne_zero_zmod19 hd
    have hmatchReflectedReference :
        AFiberCoordinates.matchingEquiv h.isMoore coords 0 (0 + (-d))
            (index_ne_add_of_ne_zero hneg)
            (labeling.aFiberReflectionCoordPerm p) =
          labeling.data.toAFiberRotationEquivariance.coordPerm (-d) 0 p := by
      exact
        (AFiberCoordinates.adj_iff_matchingEquiv_eq h.isMoore coords
          (index_ne_add_of_ne_zero hneg)
          (labeling.aFiberReflectionCoordPerm p)
          (labeling.data.toAFiberRotationEquivariance.coordPerm (-d) 0 p)).1
          (by
            simpa [endpointCommonNeighborReferenceVertex,
              endpointCommonNeighborAFixingReflectedEndpointVertex, coords] using
              hadjReflectedReference.symm)
    have hmatch :
        AFiberCoordinates.matchingEquiv h.isMoore coords 0 (0 + (-d))
            (index_ne_add_of_ne_zero hneg) p =
          labeling.data.toAFiberRotationEquivariance.coordPerm (-d) 0 p :=
      boundary.endpoint_neg_matching_of_reflected_reference_neg_matching
        d hd p hp hmatchReflectedReference
    have hadj :
        Γ.Adj
          (labeling.endpointCommonNeighborReferenceVertex p)
          (labeling.endpointCommonNeighborAFixingReflectedEndpointVertex d p) :=
      (AFiberCoordinates.adj_iff_matchingEquiv_eq h.isMoore coords
        (index_ne_add_of_ne_zero hneg) p
        (labeling.data.toAFiberRotationEquivariance.coordPerm (-d) 0 p)).2
        hmatch
    exact hadj.symm

/-- Direct connector from negative-sign endpoint matching to the existing
basic endpoint common-neighbor boundary. -/
def toMidpointExceptionEndpointAdjCommonNeighborBasicBoundary
    (boundary : EndpointSignMatchingBoundary labeling) :
    MidpointExceptionEndpointAdjCommonNeighborBasicBoundary labeling :=
  boundary.toEndpointSignAdjacencyBoundary
    |>.toMidpointExceptionEndpointAdjCommonNeighborBasicBoundary

/-- Direct connector from negative-sign endpoint matching to the downstream
fixedness boundary. -/
def toMidpointExceptionEndpointAdjForcesAFixingFixedBoundary
    (boundary : EndpointSignMatchingBoundary labeling) :
    MidpointExceptionEndpointAdjForcesAFixingFixedBoundary labeling :=
  boundary.toEndpointSignAdjacencyBoundary
    |>.toMidpointExceptionEndpointAdjForcesAFixingFixedBoundary

end EndpointSignMatchingBoundary

end BranchOrbitABCReflectionLabeling

end

end Moore57
