import Moore57.BranchOrbitABCEndpointSignMatchingSymmetry

/-!
# Endpoint paired-symmetry boundary

The endpoint matching implication in `EndpointSignMatchingBoundary` asks the
paired A-fixing symmetry to keep the same negative endpoint target `R p`.
The coordinate reflection actually produces the paired target `R (A p)`.

This file records that corrected target explicitly.  The resulting boundary
supersedes the too-strong matching boundary as the formal output of paired
symmetry: it proves adjacency to the `R (A p)` endpoint.  A conversion back to
`EndpointSignAdjacencyBoundary` is available only after adding the separate
same-target equality identifying `R (A p)` with `R p`.
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

/-- The endpoint produced by the corrected paired symmetry.

Unlike `endpointCommonNeighborAFixingReflectedEndpointVertex d p`, whose
negative endpoint target is `R p`, this vertex uses the paired target
`R (A p)`.  This is the target supplied by
`EndpointSignNegativeMatchingPairBoundary`, and is the reason the paired path
does not by itself prove the older `EndpointSignMatchingBoundary`. -/
def endpointCommonNeighborAFixingPairedReflectedEndpointVertex
    (labeling : BranchOrbitABCReflectionLabeling h)
    (d : ZMod 19) (p : labeling.data.toAFiberCoordinates.P) : V :=
  ((labeling.data.toAFiberCoordinates.coord (0 + (-d))
      (labeling.data.toAFiberRotationEquivariance.coordPerm (-d) 0
        (labeling.aFiberReflectionCoordPerm p)) :
    {x : V // x ∈
      branchFiber Γ labeling.data.toAFiberCoordinates.u
        (labeling.data.toAFiberCoordinates.a (0 + (-d)))}) : V)

/-- The paired endpoint is the old A-fixing reflected endpoint with the
source coordinate replaced by `A p`. -/
theorem endpointCommonNeighborAFixingPairedReflectedEndpointVertex_eq
    (labeling : BranchOrbitABCReflectionLabeling h)
    (d : ZMod 19) (p : labeling.data.toAFiberCoordinates.P) :
    labeling.endpointCommonNeighborAFixingPairedReflectedEndpointVertex d p =
      labeling.endpointCommonNeighborAFixingReflectedEndpointVertex d
        (labeling.aFiberReflectionCoordPerm p) := by
  rfl

/-- Corrected endpoint-sign adjacency boundary supplied by paired symmetry.

Its conclusion is deliberately about the `R (A p)` endpoint.  This is the
valid paired replacement for the too-strong
`EndpointSignMatchingBoundary`, whose conclusion keeps the target `R p`. -/
structure EndpointSignPairedAdjacencyBoundary
    (labeling : BranchOrbitABCReflectionLabeling h) : Prop where
  endpoint_adj_paired_reference_of_reflected_reference_adj :
    ∀ d : ZMod 19, ∀ _hd : d ≠ 0,
      ∀ p : labeling.data.toAFiberCoordinates.P,
        p ∈ labeling.aFiberReflectionSupport →
          Γ.Adj
            (labeling.endpointCommonNeighborAFixingReflectedEndpointVertex d p)
            (labeling.endpointCommonNeighborReferenceVertex
              (labeling.aFiberReflectionCoordPerm p)) →
          Γ.Adj
            (labeling.endpointCommonNeighborAFixingPairedReflectedEndpointVertex
              d p)
            (labeling.endpointCommonNeighborReferenceVertex p)

namespace EndpointSignNegativeMatchingPairBoundary

variable {labeling : BranchOrbitABCReflectionLabeling h}

/-- Paired negative-endpoint matching gives the corrected paired adjacency:
from adjacency of `R p` to the reflected reference coordinate, it derives
adjacency of `R (A p)` to the original reference coordinate. -/
def toEndpointSignPairedAdjacencyBoundary
    (paired : EndpointSignNegativeMatchingPairBoundary labeling) :
    EndpointSignPairedAdjacencyBoundary labeling where
  endpoint_adj_paired_reference_of_reflected_reference_adj := by
    intro d hd p _hp hadjReflectedReference
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
          labeling.data.toAFiberRotationEquivariance.coordPerm (-d) 0
            (labeling.aFiberReflectionCoordPerm p) :=
      paired.endpoint_neg_matching_pair d hd p hmatchReflectedReference
    have hadj :
        Γ.Adj
          (labeling.endpointCommonNeighborReferenceVertex p)
          (labeling.endpointCommonNeighborAFixingPairedReflectedEndpointVertex
            d p) :=
      (AFiberCoordinates.adj_iff_matchingEquiv_eq h.isMoore coords
        (index_ne_add_of_ne_zero hneg) p
        (labeling.data.toAFiberRotationEquivariance.coordPerm (-d) 0
          (labeling.aFiberReflectionCoordPerm p))).2
        hmatch
    exact hadj.symm

end EndpointSignNegativeMatchingPairBoundary

namespace EndpointMatchingAFixingCoordinateBoundary

variable {labeling : BranchOrbitABCReflectionLabeling h}

/-- Coordinate same-offset label exchange supplies the corrected paired
endpoint adjacency boundary. -/
def toEndpointSignPairedAdjacencyBoundary
    (boundary : EndpointMatchingAFixingCoordinateBoundary labeling) :
    EndpointSignPairedAdjacencyBoundary labeling :=
  boundary.toEndpointSignNegativeMatchingPairBoundary
    |>.toEndpointSignPairedAdjacencyBoundary

end EndpointMatchingAFixingCoordinateBoundary

namespace EndpointSignNoReflectedReferenceNegMatchingBoundary

variable {labeling : BranchOrbitABCReflectionLabeling h}

/-- If the reflected-reference negative matching premise never occurs on the
moving support, the corrected paired adjacency boundary follows vacuously. -/
def toEndpointSignPairedAdjacencyBoundary
    (boundary : EndpointSignNoReflectedReferenceNegMatchingBoundary labeling) :
    EndpointSignPairedAdjacencyBoundary labeling where
  endpoint_adj_paired_reference_of_reflected_reference_adj := by
    intro d hd p hpSupport hadjReflectedReference
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
      (boundary.no_reflected_reference_neg_matching d hd p hpSupport
        hmatchReflectedReference)

end EndpointSignNoReflectedReferenceNegMatchingBoundary

namespace EndpointMatchingAFixingNoPositiveTargetBoundary

variable {labeling : BranchOrbitABCReflectionLabeling h}

/-- The no-positive-target diagnostic proves the corrected paired adjacency by
first ruling out the reflected-reference negative matching premise. -/
def toEndpointSignPairedAdjacencyBoundary
    (boundary : EndpointMatchingAFixingNoPositiveTargetBoundary labeling) :
    EndpointSignPairedAdjacencyBoundary labeling :=
  boundary.toEndpointSignNoReflectedReferenceNegMatchingBoundary
    |>.toEndpointSignPairedAdjacencyBoundary

end EndpointMatchingAFixingNoPositiveTargetBoundary

namespace EndpointMatchingAFixingTargetSignBoundary

variable {labeling : BranchOrbitABCReflectionLabeling h}

/-- Target-sign compatibility, equivalently its no-premise form, gives the
corrected paired adjacency boundary. -/
def toEndpointSignPairedAdjacencyBoundary
    (boundary : EndpointMatchingAFixingTargetSignBoundary labeling) :
    EndpointSignPairedAdjacencyBoundary labeling :=
  boundary.toEndpointMatchingAFixingNoPositiveTargetBoundary
    |>.toEndpointSignPairedAdjacencyBoundary

end EndpointMatchingAFixingTargetSignBoundary

namespace MidpointExceptionAFixingSupportEndpointPointwiseNonadjBoundary

variable {labeling : BranchOrbitABCReflectionLabeling h}

/-- Pointwise endpoint non-adjacency on the A-fixing support gives the corrected
paired endpoint adjacency boundary, because it makes the reflected-reference
premise impossible. -/
def toEndpointSignPairedAdjacencyBoundary
    (boundary :
      MidpointExceptionAFixingSupportEndpointPointwiseNonadjBoundary labeling) :
    EndpointSignPairedAdjacencyBoundary labeling :=
  boundary.toEndpointSignNoReflectedReferenceNegMatchingBoundary
    |>.toEndpointSignPairedAdjacencyBoundary

end MidpointExceptionAFixingSupportEndpointPointwiseNonadjBoundary

namespace EndpointSignPairedAdjacencyBoundary

variable {labeling : BranchOrbitABCReflectionLabeling h}

/-- The corrected paired adjacency form is enough to recover the corrected
negative-endpoint label exchange.

On the moving support this is exactly adjacency/matching conversion.  Away
from the support the A-fixing reflection fixes `p`, so the paired conclusion is
just the premise rewritten by `A p = p`. -/
def toEndpointSignNegativeMatchingPairBoundary
    (boundary : EndpointSignPairedAdjacencyBoundary labeling) :
    EndpointSignNegativeMatchingPairBoundary labeling where
  endpoint_neg_matching_pair := by
    intro d hd p hreflected
    by_cases hpSupport : p ∈ labeling.aFiberReflectionSupport
    · let coords := labeling.data.toAFiberCoordinates
      let hneg : -d ≠ 0 := neg_ne_zero_of_ne_zero_zmod19 hd
      have hadjSource :
          Γ.Adj
            (labeling.endpointCommonNeighborReferenceVertex
              (labeling.aFiberReflectionCoordPerm p))
            (labeling.endpointCommonNeighborAFixingReflectedEndpointVertex
              d p) :=
        (AFiberCoordinates.adj_iff_matchingEquiv_eq h.isMoore coords
          (index_ne_add_of_ne_zero hneg)
          (labeling.aFiberReflectionCoordPerm p)
          (labeling.data.toAFiberRotationEquivariance.coordPerm (-d) 0 p)).2
          hreflected
      have hadjReflectedReference :
          Γ.Adj
            (labeling.endpointCommonNeighborAFixingReflectedEndpointVertex
              d p)
            (labeling.endpointCommonNeighborReferenceVertex
              (labeling.aFiberReflectionCoordPerm p)) :=
        hadjSource.symm
      have hpairedAdj :
          Γ.Adj
            (labeling.endpointCommonNeighborAFixingPairedReflectedEndpointVertex
              d p)
            (labeling.endpointCommonNeighborReferenceVertex p) :=
        boundary.endpoint_adj_paired_reference_of_reflected_reference_adj
          d hd p hpSupport hadjReflectedReference
      exact
        (AFiberCoordinates.adj_iff_matchingEquiv_eq h.isMoore coords
          (index_ne_add_of_ne_zero hneg) p
          (labeling.data.toAFiberRotationEquivariance.coordPerm (-d) 0
            (labeling.aFiberReflectionCoordPerm p))).1
          hpairedAdj.symm
    · have hfixed : labeling.aFiberReflectionCoordPerm p = p := by
        by_contra hmove
        exact hpSupport ((labeling.mem_aFiberReflectionSupport p).2 hmove)
      simpa [hfixed] using hreflected

/-- Paired adjacency therefore rules out the paired-singleton obstruction by
first converting to corrected negative-endpoint label exchange. -/
def toMidpointExceptionAFixingSupportNoPairedSingletonBoundary
    (boundary : EndpointSignPairedAdjacencyBoundary labeling)
    (criterion : MidpointReflectionCriterionBoundary labeling) :
    MidpointExceptionAFixingSupportNoPairedSingletonBoundary labeling :=
  boundary.toEndpointSignNegativeMatchingPairBoundary
    |>.toMidpointExceptionAFixingSupportNoPairedSingletonBoundary criterion

end EndpointSignPairedAdjacencyBoundary

/-- Corrected basic endpoint common-neighbor input with the paired `R (A p)`
target.

This is the part that follows from paired symmetry and the reflected endpoint
edge.  It intentionally does not claim the old reflected endpoint `R p` is
also adjacent to the original reference coordinate. -/
structure MidpointExceptionEndpointPairedAdjCommonNeighborBasicBoundary
    (labeling : BranchOrbitABCReflectionLabeling h) : Prop where
  aFixing_paired_reflected_endpoint_adj_reference_of_endpoint_adj :
    ∀ d : ZMod 19, ∀ _hd : d ≠ 0,
      ∀ p : labeling.data.toAFiberCoordinates.P,
        p ∈ labeling.aFiberReflectionSupport →
          Γ.Adj
            (labeling.endpointCommonNeighborReferenceVertex p)
            (labeling.endpointCommonNeighborReflectedEndpointVertex d p) →
          Γ.Adj
            (labeling.endpointCommonNeighborAFixingPairedReflectedEndpointVertex
              d p)
            (labeling.endpointCommonNeighborReferenceVertex p)

namespace EndpointSignPairedAdjacencyBoundary

variable {labeling : BranchOrbitABCReflectionLabeling h}

/-- The corrected paired adjacency boundary gives the corrected endpoint
common-neighbor basic boundary by reflecting the original endpoint edge. -/
def toMidpointExceptionEndpointPairedAdjCommonNeighborBasicBoundary
    (boundary : EndpointSignPairedAdjacencyBoundary labeling) :
    MidpointExceptionEndpointPairedAdjCommonNeighborBasicBoundary labeling where
  aFixing_paired_reflected_endpoint_adj_reference_of_endpoint_adj := by
    intro d hd p hp hadj
    exact
      boundary.endpoint_adj_paired_reference_of_reflected_reference_adj d hd p hp
        (labeling.aFixing_reflected_endpoint_adj_reflected_reference_of_endpoint_adj
          d p hadj)

end EndpointSignPairedAdjacencyBoundary

/-- Extra target equality needed to recover the older endpoint-sign adjacency
boundary from the corrected paired one.

This is the missing `R (A p) = R p` input.  It is kept separate because paired
symmetry alone proves the `R (A p)` target, while the old
`EndpointSignMatchingBoundary` effectively assumes this identification on the
moving support. -/
structure EndpointSignPairedTargetEqualityBoundary
    (labeling : BranchOrbitABCReflectionLabeling h) : Prop where
  endpoint_paired_target_eq_original_of_reflected_reference_adj :
    ∀ d : ZMod 19, ∀ _hd : d ≠ 0,
      ∀ p : labeling.data.toAFiberCoordinates.P,
        p ∈ labeling.aFiberReflectionSupport →
          Γ.Adj
            (labeling.endpointCommonNeighborAFixingReflectedEndpointVertex d p)
            (labeling.endpointCommonNeighborReferenceVertex
              (labeling.aFiberReflectionCoordPerm p)) →
          labeling.endpointCommonNeighborAFixingPairedReflectedEndpointVertex
              d p =
            labeling.endpointCommonNeighborAFixingReflectedEndpointVertex d p

namespace EndpointSignPairedAdjacencyBoundary

variable {labeling : BranchOrbitABCReflectionLabeling h}

/-- The corrected paired adjacency converts to the older
`EndpointSignAdjacencyBoundary` exactly when the paired endpoint target
`R (A p)` is separately identified with the old target `R p`. -/
def toEndpointSignAdjacencyBoundary
    (boundary : EndpointSignPairedAdjacencyBoundary labeling)
    (targetEq : EndpointSignPairedTargetEqualityBoundary labeling) :
    EndpointSignAdjacencyBoundary labeling where
  endpoint_adj_reference_of_reflected_reference_adj := by
    intro d hd p hp hadjReflectedReference
    have hpaired :
        Γ.Adj
          (labeling.endpointCommonNeighborAFixingPairedReflectedEndpointVertex
            d p)
          (labeling.endpointCommonNeighborReferenceVertex p) :=
      boundary.endpoint_adj_paired_reference_of_reflected_reference_adj
        d hd p hp hadjReflectedReference
    have htarget :
        labeling.endpointCommonNeighborAFixingPairedReflectedEndpointVertex d p =
          labeling.endpointCommonNeighborAFixingReflectedEndpointVertex d p :=
      targetEq.endpoint_paired_target_eq_original_of_reflected_reference_adj
        d hd p hp hadjReflectedReference
    simpa [htarget] using hpaired

end EndpointSignPairedAdjacencyBoundary

namespace EndpointSignPairedTargetEqualityBoundary

variable {labeling : BranchOrbitABCReflectionLabeling h}

/-- With the explicit target equality, the corrected paired common-neighbor
basic boundary recovers the existing basic boundary. -/
def toMidpointExceptionEndpointAdjCommonNeighborBasicBoundary
    (pairedBasic :
      MidpointExceptionEndpointPairedAdjCommonNeighborBasicBoundary labeling)
    (targetEq : EndpointSignPairedTargetEqualityBoundary labeling) :
    MidpointExceptionEndpointAdjCommonNeighborBasicBoundary labeling where
  aFixing_reflected_endpoint_adj_reference_of_endpoint_adj := by
    intro d hd p hp hadj
    have hreflectedReference :
        Γ.Adj
          (labeling.endpointCommonNeighborAFixingReflectedEndpointVertex d p)
          (labeling.endpointCommonNeighborReferenceVertex
            (labeling.aFiberReflectionCoordPerm p)) :=
      labeling.aFixing_reflected_endpoint_adj_reflected_reference_of_endpoint_adj
        d p hadj
    have hpaired :
        Γ.Adj
          (labeling.endpointCommonNeighborAFixingPairedReflectedEndpointVertex
            d p)
          (labeling.endpointCommonNeighborReferenceVertex p) :=
      pairedBasic.aFixing_paired_reflected_endpoint_adj_reference_of_endpoint_adj
        d hd p hp hadj
    have htarget :
        labeling.endpointCommonNeighborAFixingPairedReflectedEndpointVertex d p =
          labeling.endpointCommonNeighborAFixingReflectedEndpointVertex d p :=
      targetEq.endpoint_paired_target_eq_original_of_reflected_reference_adj
        d hd p hp hreflectedReference
    simpa [htarget] using hpaired

end EndpointSignPairedTargetEqualityBoundary

namespace EndpointSignNegativeMatchingPairBoundary

variable {labeling : BranchOrbitABCReflectionLabeling h}

/-- Coordinate same-target data from
`EndpointSignNegativeMatchingPairBoundary.SameNegativeEndpointTargetBoundary`
gives the vertex-level target equality used above. -/
def SameNegativeEndpointTargetBoundary.toEndpointSignPairedTargetEqualityBoundary
    {paired : EndpointSignNegativeMatchingPairBoundary labeling}
    (sameTarget : SameNegativeEndpointTargetBoundary paired) :
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
    have htargetCoord :
        labeling.data.toAFiberRotationEquivariance.coordPerm (-d) 0
            (labeling.aFiberReflectionCoordPerm p) =
          labeling.data.toAFiberRotationEquivariance.coordPerm (-d) 0 p :=
      sameTarget.same_negative_endpoint_target_of_reflected_reference_neg_matching
        d hd p hp hmatchReflectedReference
    exact congrArg
      (fun q =>
        (((coords.coord (0 + (-d)) q :
          {x : V // x ∈ branchFiber Γ coords.u (coords.a (0 + (-d)))}) : V)))
      htargetCoord

/-- Paired symmetry plus the separate same-target equality recovers the old
endpoint-sign adjacency boundary.  Without that equality, the provable target
is only `R (A p)`. -/
def toEndpointSignAdjacencyBoundary
    (paired : EndpointSignNegativeMatchingPairBoundary labeling)
    (sameTarget : SameNegativeEndpointTargetBoundary paired) :
    EndpointSignAdjacencyBoundary labeling :=
  paired.toEndpointSignPairedAdjacencyBoundary
    |>.toEndpointSignAdjacencyBoundary
      sameTarget.toEndpointSignPairedTargetEqualityBoundary

/-- Paired symmetry alone reaches the corrected common-neighbor basic boundary
with target `R (A p)`. -/
def toMidpointExceptionEndpointPairedAdjCommonNeighborBasicBoundary
    (paired : EndpointSignNegativeMatchingPairBoundary labeling) :
    MidpointExceptionEndpointPairedAdjCommonNeighborBasicBoundary labeling :=
  paired.toEndpointSignPairedAdjacencyBoundary
    |>.toMidpointExceptionEndpointPairedAdjCommonNeighborBasicBoundary

end EndpointSignNegativeMatchingPairBoundary

end BranchOrbitABCReflectionLabeling

end

end Moore57
