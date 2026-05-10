import Moore57.BranchOrbitABCEndpointPairedFinalBoundary

/-!
# Endpoint-paired target diagnostic connector

The endpoint-paired path needs a separate target equality
`R (A p) = R p` to rejoin the older endpoint-sign adjacency path.  This file
records the diagnostic/vacuous way to supply that equality: if the reflected
reference negative matching premise is assumed never to occur on the moving
support, then the adjacency premise of `EndpointSignPairedTargetEqualityBoundary`
is impossible, so the target equality follows by contradiction.

This is deliberately not a non-vacuous target-equality theorem from paired
symmetry.
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

namespace EndpointSignNoReflectedReferenceNegMatchingBoundary

variable {labeling : BranchOrbitABCReflectionLabeling h}

/-- Diagnostic/vacuous target equality for the endpoint-paired path.

The adjacency premise is converted to the reflected-reference negative matching
premise for `A p`; this contradicts
`EndpointSignNoReflectedReferenceNegMatchingBoundary`, so the vertex equality is
supplied by `False.elim`. -/
def toVacuousEndpointSignPairedTargetEqualityBoundary
    (boundary : EndpointSignNoReflectedReferenceNegMatchingBoundary labeling) :
    EndpointSignPairedTargetEqualityBoundary labeling where
  endpoint_paired_target_eq_original_of_reflected_reference_adj := by
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
    exact False.elim
      (boundary.no_reflected_reference_neg_matching
        d hd p hp hmatchReflectedReference)

/-- Report-wrapper form of the diagnostic/vacuous target equality. -/
def toVacuousBranchOrbitABCEndpointPairedRemainingTargetEqualityBoundary
    (boundary : EndpointSignNoReflectedReferenceNegMatchingBoundary labeling) :
    BranchOrbitABCEndpointPairedRemainingTargetEqualityBoundary labeling where
  remainingEndpointTargetEquality :=
    boundary.toVacuousEndpointSignPairedTargetEqualityBoundary

end EndpointSignNoReflectedReferenceNegMatchingBoundary

end BranchOrbitABCReflectionLabeling

namespace BranchOrbitABCEndpointSignAdjacencyIssueBoundary

variable {h : D19ActsOnMoore57 V Γ}
variable {labeling : BranchOrbitABCReflectionLabeling h}

/-- The current endpoint sign-adjacency diagnostic can supply the paired
remaining target equality only vacuously, by ruling out the adjacency premise
after it is converted to reflected-reference negative matching. -/
def toVacuousEndpointPairedRemainingTargetEqualityBoundary
    (boundary : BranchOrbitABCEndpointSignAdjacencyIssueBoundary labeling) :
    BranchOrbitABCEndpointPairedRemainingTargetEqualityBoundary labeling :=
  boundary.noReflectedReferenceNegMatching
    |>.toVacuousBranchOrbitABCEndpointPairedRemainingTargetEqualityBoundary

end BranchOrbitABCEndpointSignAdjacencyIssueBoundary

end

end Moore57
