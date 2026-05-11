import Moore57.BranchOrbitABCEndpointSignAdjacencyBoundary
import Moore57.BranchOrbitABCExceptionEndpointPointwiseBoundary
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

/-- The corrected negative-endpoint label exchange rules out the remaining
paired-singleton obstruction.

If `S_(d/2) ∩ E = {p}` and `S_((-d)/2) ∩ E = {A p}`, the `-d` singleton gives
the reflected-reference negative matching equation for `A p`.  The paired
label exchange then puts `p` in the same `-d` intersection, contradicting
`p ∈ E`, which says `A p ≠ p`. -/
def toMidpointExceptionAFixingSupportNoPairedSingletonBoundary
    (paired : EndpointSignNegativeMatchingPairBoundary labeling)
    (criterion : MidpointReflectionCriterionBoundary labeling) :
    MidpointExceptionAFixingSupportNoPairedSingletonBoundary labeling where
  not_paired_singleton := by
    intro d hd p hpSupport hpairedSingleton
    rcases hpairedSingleton with ⟨_hp_singleton, hneg_singleton⟩
    let hneg : -d ≠ 0 := neg_ne_zero_of_ne_zero_zmod19 hd
    have htheta_inter :
        labeling.aFiberReflectionCoordPerm p ∈
          labeling.midpointExceptionAFixingSupportIntersection
            (midpointOf (-d)) (midpointOf_ne_zero hneg) := by
      simp [hneg_singleton]
    have htheta_exception :
        labeling.aFiberReflectionCoordPerm p ∈
          labeling.midpointExceptionSet
            (midpointOf (-d)) (midpointOf_ne_zero hneg) :=
      (labeling.mem_midpointExceptionAFixingSupportIntersection
        (midpointOf (-d)) (midpointOf_ne_zero hneg)
        (labeling.aFiberReflectionCoordPerm p)).1 htheta_inter |>.1
    have htheta_equation :
        labeling.aFiberReflectionCoordPerm p ∈
          labeling.midpointEquationSet
            (midpointOf (-d)) (midpointOf_ne_zero hneg) :=
      (criterion.midpoint_equation_iff_exception
        (midpointOf (-d)) (midpointOf_ne_zero hneg)
        (labeling.aFiberReflectionCoordPerm p)).2 htheta_exception
    have hnegdd : midpointOf (-d) + midpointOf (-d) = -d :=
      midpointOf_add_self (-d)
    have htheta_match_mid :
        AFiberCoordinates.matchingEquiv h.isMoore
            labeling.data.toAFiberCoordinates 0
            (0 + (midpointOf (-d) + midpointOf (-d)))
            (index_ne_add_of_ne_zero
              (add_self_ne_zero_zmod19 (midpointOf_ne_zero hneg)))
            (labeling.aFiberReflectionCoordPerm p) =
          labeling.midpointReflectionCoordPerm (midpointOf (-d))
            (labeling.aFiberReflectionCoordPerm p) :=
      (labeling.mem_midpointEquationSet
        (midpointOf (-d)) (midpointOf_ne_zero hneg)
        (labeling.aFiberReflectionCoordPerm p)).1 htheta_equation
    have htheta_rhs :
        labeling.midpointReflectionCoordPerm (midpointOf (-d))
            (labeling.aFiberReflectionCoordPerm p) =
          labeling.data.toAFiberRotationEquivariance.coordPerm (-d) 0 p := by
      simpa [hnegdd] using
        labeling.midpointReflectionCoordPerm_aFiberReflectionCoordPerm_eq_rotationCoordPerm
          (midpointOf (-d)) p
    have hreflected :
        AFiberCoordinates.matchingEquiv h.isMoore
            labeling.data.toAFiberCoordinates 0 (0 + (-d))
            (index_ne_add_of_ne_zero hneg)
            (labeling.aFiberReflectionCoordPerm p) =
          labeling.data.toAFiberRotationEquivariance.coordPerm (-d) 0 p := by
      simpa [hnegdd, htheta_rhs, hneg] using htheta_match_mid
    have hp_match :
        AFiberCoordinates.matchingEquiv h.isMoore
            labeling.data.toAFiberCoordinates 0 (0 + (-d))
            (index_ne_add_of_ne_zero hneg) p =
          labeling.data.toAFiberRotationEquivariance.coordPerm (-d) 0
            (labeling.aFiberReflectionCoordPerm p) :=
      paired.endpoint_neg_matching_pair d hd p hreflected
    have hp_rhs :
        labeling.midpointReflectionCoordPerm (midpointOf (-d)) p =
          labeling.data.toAFiberRotationEquivariance.coordPerm (-d) 0
            (labeling.aFiberReflectionCoordPerm p) := by
      simpa [hnegdd] using
        labeling.midpointReflectionCoordPerm_eq_rotationCoordPerm_aFiberReflectionCoordPerm
          (midpointOf (-d)) p
    have hp_equation :
        p ∈ labeling.midpointEquationSet
          (midpointOf (-d)) (midpointOf_ne_zero hneg) := by
      rw [labeling.mem_midpointEquationSet]
      simpa [hnegdd, hp_rhs, hneg] using hp_match
    have hp_exception :
        p ∈ labeling.midpointExceptionSet
          (midpointOf (-d)) (midpointOf_ne_zero hneg) :=
      (criterion.midpoint_equation_iff_exception
        (midpointOf (-d)) (midpointOf_ne_zero hneg) p).1 hp_equation
    have hp_inter :
        p ∈ labeling.midpointExceptionAFixingSupportIntersection
          (midpointOf (-d)) (midpointOf_ne_zero hneg) :=
      (labeling.mem_midpointExceptionAFixingSupportIntersection
        (midpointOf (-d)) (midpointOf_ne_zero hneg) p).2
        ⟨hp_exception, hpSupport⟩
    have hp_eq_theta : p = labeling.aFiberReflectionCoordPerm p := by
      simpa [hneg_singleton, hneg] using hp_inter
    have hp_moved : labeling.aFiberReflectionCoordPerm p ≠ p :=
      (labeling.mem_aFiberReflectionSupport p).1 hpSupport
    exact hp_moved hp_eq_theta.symm

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

/-- If the reflected-reference negative matching premise never occurs, endpoint
adjacency would force A-fixing fixedness and hence is pointwise impossible on
the A-fixing moving support. -/
def toMidpointExceptionAFixingSupportEndpointPointwiseNonadjBoundary
    (boundary : EndpointSignNoReflectedReferenceNegMatchingBoundary labeling) :
    MidpointExceptionAFixingSupportEndpointPointwiseNonadjBoundary labeling :=
  boundary.toEndpointSignMatchingBoundary
    |>.toMidpointExceptionEndpointAdjForcesAFixingFixedBoundary
    |>.toMidpointExceptionAFixingSupportEndpointPointwiseNonadjBoundary

end EndpointSignNoReflectedReferenceNegMatchingBoundary

namespace EndpointMatchingAFixingNoPositiveTargetBoundary

variable {labeling : BranchOrbitABCReflectionLabeling h}

/-- The no-positive-target diagnostic also rules out the reflected-reference
negative matching premise.

Indeed, applying the already-proved negative-offset transport at `-d` to the
reflected coordinate sends
`M_(-d) (A p) = R_(-d) p` back to the positive target equation
`M_d p = R_d (A p)`. -/
def toEndpointSignNoReflectedReferenceNegMatchingBoundary
    (boundary : EndpointMatchingAFixingNoPositiveTargetBoundary labeling) :
    EndpointSignNoReflectedReferenceNegMatchingBoundary labeling where
  no_reflected_reference_neg_matching := by
    intro d hd p _hpSupport hreflected
    let hneg : -d ≠ 0 := neg_ne_zero_of_ne_zero_zmod19 hd
    have hAA :
        labeling.aFiberReflectionCoordPerm
            (labeling.aFiberReflectionCoordPerm p) = p :=
      labeling.aFiberReflectionCoordPerm_involutive p
    have hreflected_for_transport :
        AFiberCoordinates.matchingEquiv h.isMoore
            labeling.data.toAFiberCoordinates 0 (0 + (-d))
            (index_ne_add_of_ne_zero hneg)
            (labeling.aFiberReflectionCoordPerm p) =
          labeling.data.toAFiberRotationEquivariance.coordPerm (-d) 0
            (labeling.aFiberReflectionCoordPerm
              (labeling.aFiberReflectionCoordPerm p)) := by
      simpa [hAA] using hreflected
    have hpositive :=
      labeling.endpointMatchingAFixingNegativeOffsetBoundary
        |>.aFiberReflection_matching_eq_rotation_neg (-d) hneg
          (labeling.aFiberReflectionCoordPerm p) hreflected_for_transport
    exact boundary.no_positive_target_matching d hd p (by
      simpa [hAA] using hpositive)

end EndpointMatchingAFixingNoPositiveTargetBoundary

namespace MidpointExceptionAFixingSupportEndpointPointwiseNonadjBoundary

variable {labeling : BranchOrbitABCReflectionLabeling h}

/-- Pointwise endpoint non-adjacency on the A-fixing support rules out the
reflected-reference negative matching premise.

The reflected negative premise transports back, at offset `-d`, to the positive
endpoint equation `M_d p = R_d (A p)`, which is exactly the endpoint adjacency
forbidden by the pointwise boundary. -/
def toEndpointSignNoReflectedReferenceNegMatchingBoundary
    (boundary :
      MidpointExceptionAFixingSupportEndpointPointwiseNonadjBoundary labeling) :
    EndpointSignNoReflectedReferenceNegMatchingBoundary labeling where
  no_reflected_reference_neg_matching := by
    intro d hd p hpSupport hreflected
    let coords := labeling.data.toAFiberCoordinates
    let hneg : -d ≠ 0 := neg_ne_zero_of_ne_zero_zmod19 hd
    have hAA :
        labeling.aFiberReflectionCoordPerm
            (labeling.aFiberReflectionCoordPerm p) = p :=
      labeling.aFiberReflectionCoordPerm_involutive p
    have hreflected_for_transport :
        AFiberCoordinates.matchingEquiv h.isMoore
            labeling.data.toAFiberCoordinates 0 (0 + (-d))
            (index_ne_add_of_ne_zero hneg)
            (labeling.aFiberReflectionCoordPerm p) =
          labeling.data.toAFiberRotationEquivariance.coordPerm (-d) 0
            (labeling.aFiberReflectionCoordPerm
              (labeling.aFiberReflectionCoordPerm p)) := by
      simpa [hAA] using hreflected
    have hpositive :
        AFiberCoordinates.matchingEquiv h.isMoore
            labeling.data.toAFiberCoordinates 0 (0 + d)
            (index_ne_add_of_ne_zero hd) p =
          labeling.data.toAFiberRotationEquivariance.coordPerm d 0
            (labeling.aFiberReflectionCoordPerm p) := by
      have htransport :=
        labeling.endpointMatchingAFixingNegativeOffsetBoundary
          |>.aFiberReflection_matching_eq_rotation_neg (-d) hneg
            (labeling.aFiberReflectionCoordPerm p) hreflected_for_transport
      simpa [hAA] using htransport
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
    have hadjRaw :
        Γ.Adj
          (((coords.coord 0 p :
            {x : V // x ∈ branchFiber Γ coords.u (coords.a 0)}) : V))
          (((coords.coord (0 + d)
              (labeling.data.toAFiberRotationEquivariance.coordPerm d 0
                (labeling.aFiberReflectionCoordPerm p)) :
            {x : V // x ∈ branchFiber Γ coords.u (coords.a (0 + d))}) : V)) :=
      (AFiberCoordinates.adj_iff_matchingEquiv_eq h.isMoore coords
        (index_ne_add_of_ne_zero hd) p
        (labeling.data.toAFiberRotationEquivariance.coordPerm d 0
          (labeling.aFiberReflectionCoordPerm p))).2 hpositive
    have hadjPositive :
        Γ.Adj
          (labeling.endpointCommonNeighborReferenceVertex p)
          (labeling.endpointCommonNeighborReflectedEndpointVertex d p) := by
      simpa [endpointCommonNeighborReferenceVertex, coords, hendpoint] using
        hadjRaw
    exact boundary.endpoint_nonadj_of_mem_support d hd p hpSupport hadjPositive

end MidpointExceptionAFixingSupportEndpointPointwiseNonadjBoundary

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
