import Moore57.BranchOrbitABCEndpointSignAdjacencyBoundary
import Moore57.AFiberMatchingPermSymmetry

/-!
# Endpoint sign matching symmetry diagnostics

The A-fixing coordinate reflection transports the endpoint matching equation by
reflecting both the source coordinate and the rotated target.  This file records
the corrected paired statement and isolates why the existing
`EndpointSignMatchingBoundary` is stronger: on the moving support, if its
premise and conclusion both hold, injectivity of the matching permutation forces
the supposedly moved coordinate to be fixed.
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

/-- Corrected negative-endpoint matching symmetry: the A-fixing reflection
transfers the equation for `A p` with target `R p` to the equation for `p` with
the reflected target `R (A p)`.

This is the symmetry statement supplied by the existing involution/coordinatized
matching boundary.  It intentionally does not claim that `R (A p) = R p`. -/
structure EndpointSignNegativeMatchingPairBoundary
    (labeling : BranchOrbitABCReflectionLabeling h) : Prop where
  endpoint_neg_matching_pair :
    ∀ d : ZMod 19, ∀ hd : d ≠ 0,
      ∀ p : labeling.data.toAFiberCoordinates.P,
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
          labeling.data.toAFiberRotationEquivariance.coordPerm (-d) 0
            (labeling.aFiberReflectionCoordPerm p)

namespace EndpointMatchingAFixingCoordinateBoundary

variable {labeling : BranchOrbitABCReflectionLabeling h}

/-- The existing endpoint matching/reflection coordinate boundary proves the
correct paired negative-endpoint symmetry by applying it to `A p` and using
that the A-fixing coordinate reflection is involutive. -/
def toEndpointSignNegativeMatchingPairBoundary
    (boundary : EndpointMatchingAFixingCoordinateBoundary labeling) :
    EndpointSignNegativeMatchingPairBoundary labeling where
  endpoint_neg_matching_pair := by
    intro d hd p hp
    let hneg : -d ≠ 0 := neg_ne_zero_of_ne_zero_zmod19 hd
    have hAA :
        labeling.aFiberReflectionCoordPerm
            (labeling.aFiberReflectionCoordPerm p) = p :=
      labeling.aFiberReflectionCoordPerm_involutive p
    have hp_for_boundary :
        AFiberCoordinates.matchingEquiv h.isMoore
            labeling.data.toAFiberCoordinates 0 (0 + (-d))
            (index_ne_add_of_ne_zero hneg)
            (labeling.aFiberReflectionCoordPerm p) =
          labeling.data.toAFiberRotationEquivariance.coordPerm (-d) 0
            (labeling.aFiberReflectionCoordPerm
              (labeling.aFiberReflectionCoordPerm p)) := by
      simpa [hAA] using hp
    have hpair :=
      boundary.aFiberReflection_matching_eq_rotation (-d) hneg
        (labeling.aFiberReflectionCoordPerm p) hp_for_boundary
    simpa [hAA] using hpair

end EndpointMatchingAFixingCoordinateBoundary

namespace EndpointSignNegativeMatchingPairBoundary

variable {labeling : BranchOrbitABCReflectionLabeling h}

/-- The exact extra target identification needed to turn the corrected paired
statement into the stronger `EndpointSignMatchingBoundary`.  On the moving
support this target identification is itself a very strong condition, because
the rotation coordinate permutation is injective. -/
structure SameNegativeEndpointTargetBoundary
    (paired : EndpointSignNegativeMatchingPairBoundary labeling) : Prop where
  same_negative_endpoint_target_of_reflected_reference_neg_matching :
    ∀ d : ZMod 19, ∀ hd : d ≠ 0,
      ∀ p : labeling.data.toAFiberCoordinates.P,
        p ∈ labeling.aFiberReflectionSupport →
          AFiberCoordinates.matchingEquiv h.isMoore
              labeling.data.toAFiberCoordinates 0 (0 + (-d))
              (index_ne_add_of_ne_zero
                (neg_ne_zero_of_ne_zero_zmod19 hd))
              (labeling.aFiberReflectionCoordPerm p) =
            labeling.data.toAFiberRotationEquivariance.coordPerm (-d) 0 p →
          labeling.data.toAFiberRotationEquivariance.coordPerm (-d) 0
              (labeling.aFiberReflectionCoordPerm p) =
            labeling.data.toAFiberRotationEquivariance.coordPerm (-d) 0 p

/-- The paired symmetry plus the missing same-target identification gives the
existing endpoint-sign matching boundary. -/
def toEndpointSignMatchingBoundary
    (paired : EndpointSignNegativeMatchingPairBoundary labeling)
    (sameTarget : SameNegativeEndpointTargetBoundary paired) :
    EndpointSignMatchingBoundary labeling where
  endpoint_neg_matching_of_reflected_reference_neg_matching := by
    intro d hd p hpSupport hreflected
    have hpair :=
      paired.endpoint_neg_matching_pair d hd p hreflected
    have htarget :=
      sameTarget.same_negative_endpoint_target_of_reflected_reference_neg_matching
        d hd p hpSupport hreflected
    exact hpair.trans htarget

end EndpointSignNegativeMatchingPairBoundary

/-- Diagnostic boundary equivalent to making the existing endpoint-sign
matching implication true vacuously on the A-fixing moving support. -/
structure EndpointSignNoReflectedReferenceNegMatchingBoundary
    (labeling : BranchOrbitABCReflectionLabeling h) : Prop where
  no_reflected_reference_neg_matching :
    ∀ d : ZMod 19, ∀ hd : d ≠ 0,
      ∀ p : labeling.data.toAFiberCoordinates.P,
        p ∈ labeling.aFiberReflectionSupport →
          ¬
            AFiberCoordinates.matchingEquiv h.isMoore
                labeling.data.toAFiberCoordinates 0 (0 + (-d))
                (index_ne_add_of_ne_zero
                  (neg_ne_zero_of_ne_zero_zmod19 hd))
                (labeling.aFiberReflectionCoordPerm p) =
              labeling.data.toAFiberRotationEquivariance.coordPerm (-d) 0 p

namespace EndpointSignNoReflectedReferenceNegMatchingBoundary

variable {labeling : BranchOrbitABCReflectionLabeling h}

/-- If the reflected-reference negative matching premise never occurs on the
moving support, the existing endpoint-sign boundary follows vacuously. -/
def toEndpointSignMatchingBoundary
    (boundary : EndpointSignNoReflectedReferenceNegMatchingBoundary labeling) :
    EndpointSignMatchingBoundary labeling where
  endpoint_neg_matching_of_reflected_reference_neg_matching := by
    intro d hd p hpSupport hreflected
    exact False.elim
      (boundary.no_reflected_reference_neg_matching d hd p hpSupport hreflected)

end EndpointSignNoReflectedReferenceNegMatchingBoundary

namespace EndpointSignMatchingBoundary

variable {labeling : BranchOrbitABCReflectionLabeling h}

/-- The existing endpoint-sign matching boundary forces the reflected-reference
negative matching premise to be false on the moving support.  Indeed, the
premise and the boundary conclusion give the same matching image for `A p` and
`p`; injectivity of the matching equivalence then contradicts support
membership. -/
def toEndpointSignNoReflectedReferenceNegMatchingBoundary
    (boundary : EndpointSignMatchingBoundary labeling) :
    EndpointSignNoReflectedReferenceNegMatchingBoundary labeling where
  no_reflected_reference_neg_matching := by
    intro d hd p hpSupport hreflected
    let hneg : -d ≠ 0 := neg_ne_zero_of_ne_zero_zmod19 hd
    let M :=
      AFiberCoordinates.matchingEquiv h.isMoore
        labeling.data.toAFiberCoordinates 0 (0 + (-d))
        (index_ne_add_of_ne_zero hneg)
    have horiginal :
        M p =
          labeling.data.toAFiberRotationEquivariance.coordPerm (-d) 0 p :=
      boundary.endpoint_neg_matching_of_reflected_reference_neg_matching
        d hd p hpSupport hreflected
    have hsame_image :
        M (labeling.aFiberReflectionCoordPerm p) = M p := by
      exact hreflected.trans horiginal.symm
    have hfixed : labeling.aFiberReflectionCoordPerm p = p :=
      M.injective hsame_image
    have hmoved : labeling.aFiberReflectionCoordPerm p ≠ p :=
      (labeling.mem_aFiberReflectionSupport p).1 hpSupport
    exact hmoved hfixed

end EndpointSignMatchingBoundary

end BranchOrbitABCReflectionLabeling

end

end Moore57
