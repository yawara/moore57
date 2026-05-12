import Moore57.D19OnMoore57.BranchOrbit.ABCMatchingAdjacencyTransportBoundary
import Moore57.D19OnMoore57.BranchOrbit.ABCExceptionCardOneBoundary
import Moore57.Moore57Graph.AFiber.MatchingPerm

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

/-- Correct midpoint-equation transport under the A-fixing reflection.

The A-fixing reflection does not preserve the midpoint equation at the same
offset.  It sends the equation for endpoint offset `d` to the equation for
endpoint offset `-d`. -/
structure MidpointEquationSetAFixingNegInvariantBoundary
    (labeling : BranchOrbitABCReflectionLabeling h) : Prop where
  aFiberReflection_mem_midpointEquationSet_neg :
    ∀ d : ZMod 19, ∀ hd : d ≠ 0,
      ∀ p : labeling.data.toAFiberCoordinates.P,
        p ∈ labeling.midpointEquationSet
          (midpointOf d) (midpointOf_ne_zero hd) →
        labeling.aFiberReflectionCoordPerm p ∈
          labeling.midpointEquationSet
            (midpointOf (-d)) (midpointOf_ne_zero (neg_ne_zero.mpr hd))

/-- The proven endpoint negative-offset transport supplies the midpoint
equation-set negative-offset transport. -/
def midpointEquationSetAFixingNegInvariantBoundary
    (labeling : BranchOrbitABCReflectionLabeling h) :
    MidpointEquationSetAFixingNegInvariantBoundary labeling where
  aFiberReflection_mem_midpointEquationSet_neg := by
    intro d hd p hp
    rw [mem_midpointEquationSet] at hp ⊢
    have hdd : midpointOf d + midpointOf d = d := midpointOf_add_self d
    have hnegdd : midpointOf (-d) + midpointOf (-d) = -d :=
      midpointOf_add_self (-d)
    have hp_rotation :
        AFiberCoordinates.matchingEquiv h.isMoore
            labeling.data.toAFiberCoordinates 0 (0 + d)
            (index_ne_add_of_ne_zero hd) p =
          labeling.data.toAFiberRotationEquivariance.coordPerm d 0
            (labeling.aFiberReflectionCoordPerm p) := by
      simpa [hdd] using
        hp.trans
          (labeling.midpointReflectionCoordPerm_eq_rotationCoordPerm_aFiberReflectionCoordPerm
            (midpointOf d) p)
    have hmatching_neg :
        AFiberCoordinates.matchingEquiv h.isMoore
            labeling.data.toAFiberCoordinates 0 (0 + (-d))
            (index_ne_add_of_ne_zero (neg_ne_zero.mpr hd))
            (labeling.aFiberReflectionCoordPerm p) =
          labeling.data.toAFiberRotationEquivariance.coordPerm (-d) 0 p :=
      (labeling.endpointMatchingAFixingNegativeOffsetBoundary
        |>.aFiberReflection_matching_eq_rotation_neg d hd p hp_rotation)
    have hmid_neg :
        labeling.midpointReflectionCoordPerm (midpointOf (-d))
            (labeling.aFiberReflectionCoordPerm p) =
          labeling.data.toAFiberRotationEquivariance.coordPerm (-d) 0 p := by
      simpa [hnegdd] using
        labeling.midpointReflectionCoordPerm_aFiberReflectionCoordPerm_eq_rotationCoordPerm
          (midpointOf (-d)) p
    simpa [hnegdd, hmid_neg] using hmatching_neg

/-- Boundary input: the midpoint-exception set at offset `d` is transported
to the midpoint-exception set at offset `-d` by the A-fixing reflection. -/
structure MidpointExceptionSetAFixingNegInvariantBoundary
    (labeling : BranchOrbitABCReflectionLabeling h) : Prop where
  aFiberReflection_mem_midpointExceptionSet_neg :
    ∀ d : ZMod 19, ∀ hd : d ≠ 0,
      ∀ p : labeling.data.toAFiberCoordinates.P,
        p ∈ labeling.midpointExceptionSet
          (midpointOf d) (midpointOf_ne_zero hd) →
        labeling.aFiberReflectionCoordPerm p ∈
          labeling.midpointExceptionSet
            (midpointOf (-d)) (midpointOf_ne_zero (neg_ne_zero.mpr hd))

/-- Boundary input: the A-fixing reflection transports the
midpoint-exception/A-fixing-support intersection at offset `d` to the
intersection at offset `-d`. -/
structure MidpointExceptionAFixingSupportIntersectionNegInvariantBoundary
    (labeling : BranchOrbitABCReflectionLabeling h) : Prop where
  aFiberReflection_mem_intersection_neg :
    ∀ d : ZMod 19, ∀ hd : d ≠ 0,
      ∀ p : labeling.data.toAFiberCoordinates.P,
        p ∈ labeling.midpointExceptionAFixingSupportIntersection
          (midpointOf d) (midpointOf_ne_zero hd) →
        labeling.aFiberReflectionCoordPerm p ∈
          labeling.midpointExceptionAFixingSupportIntersection
            (midpointOf (-d)) (midpointOf_ne_zero (neg_ne_zero.mpr hd))

namespace MidpointExceptionSetAFixingNegInvariantBoundary

variable {labeling : BranchOrbitABCReflectionLabeling h}

/-- Negative-offset exception-set transport gives the corresponding transport
for the intersection with the A-fixing reflection support, since that support
is preserved by the same involution. -/
def toMidpointExceptionAFixingSupportIntersectionNegInvariantBoundary
    (boundary : MidpointExceptionSetAFixingNegInvariantBoundary labeling) :
    MidpointExceptionAFixingSupportIntersectionNegInvariantBoundary labeling where
  aFiberReflection_mem_intersection_neg := by
    intro d hd p hp
    rcases
      (labeling.mem_midpointExceptionAFixingSupportIntersection
        (midpointOf d) (midpointOf_ne_zero hd) p).1 hp with
      ⟨hpException, hpSupport⟩
    exact
      (labeling.mem_midpointExceptionAFixingSupportIntersection
        (midpointOf (-d)) (midpointOf_ne_zero (neg_ne_zero.mpr hd))
        (labeling.aFiberReflectionCoordPerm p)).2
        ⟨boundary.aFiberReflection_mem_midpointExceptionSet_neg d hd p
            hpException,
          labeling.aFiberReflectionCoordPerm_mem_support_of_mem hpSupport⟩

end MidpointExceptionSetAFixingNegInvariantBoundary

namespace MidpointExceptionAFixingSupportIntersectionNegInvariantBoundary

variable {labeling : BranchOrbitABCReflectionLabeling h}

/-- The `d ↦ -d` intersection transport is bijective, with inverse given by
the same A-fixing involution. -/
noncomputable def intersectionEquivNeg
    (boundary :
      MidpointExceptionAFixingSupportIntersectionNegInvariantBoundary labeling)
    (d : ZMod 19) (hd : d ≠ 0) :
    {p : labeling.data.toAFiberCoordinates.P //
      p ∈ labeling.midpointExceptionAFixingSupportIntersection
        (midpointOf d) (midpointOf_ne_zero hd)} ≃
    {q : labeling.data.toAFiberCoordinates.P //
      q ∈ labeling.midpointExceptionAFixingSupportIntersection
        (midpointOf (-d)) (midpointOf_ne_zero (neg_ne_zero.mpr hd))} where
  toFun p :=
    ⟨labeling.aFiberReflectionCoordPerm p,
      boundary.aFiberReflection_mem_intersection_neg d hd p p.property⟩
  invFun q :=
    ⟨labeling.aFiberReflectionCoordPerm q, by
      have hq :=
        boundary.aFiberReflection_mem_intersection_neg (-d)
          (neg_ne_zero.mpr hd) q q.property
      simpa using hq⟩
  left_inv := by
    intro p
    ext
    exact labeling.aFiberReflectionCoordPerm_involutive p.1
  right_inv := by
    intro q
    ext
    exact labeling.aFiberReflectionCoordPerm_involutive q.1

/-- The midpoint-exception/A-fixing-support intersections at endpoint offsets
`d` and `-d` have the same cardinality. -/
theorem card_eq_neg
    (boundary :
      MidpointExceptionAFixingSupportIntersectionNegInvariantBoundary labeling)
    (d : ZMod 19) (hd : d ≠ 0) :
    (labeling.midpointExceptionAFixingSupportIntersection
      (midpointOf d) (midpointOf_ne_zero hd)).card =
    (labeling.midpointExceptionAFixingSupportIntersection
      (midpointOf (-d)) (midpointOf_ne_zero (neg_ne_zero.mpr hd))).card := by
  classical
  letI := labeling.data.toAFiberCoordinates.P_fintype
  let e := boundary.intersectionEquivNeg d hd
  calc
    (labeling.midpointExceptionAFixingSupportIntersection
      (midpointOf d) (midpointOf_ne_zero hd)).card =
        Fintype.card {p : labeling.data.toAFiberCoordinates.P //
          p ∈ labeling.midpointExceptionAFixingSupportIntersection
            (midpointOf d) (midpointOf_ne_zero hd)} := by
          rw [Fintype.card_coe]
    _ = Fintype.card {q : labeling.data.toAFiberCoordinates.P //
          q ∈ labeling.midpointExceptionAFixingSupportIntersection
            (midpointOf (-d)) (midpointOf_ne_zero (neg_ne_zero.mpr hd))} :=
          Fintype.card_congr e
    _ =
        (labeling.midpointExceptionAFixingSupportIntersection
          (midpointOf (-d)) (midpointOf_ne_zero (neg_ne_zero.mpr hd))).card := by
          rw [Fintype.card_coe]

/-- A singleton at offset `d` transports to the reflected singleton at offset
`-d`.  Thus the remaining one-point obstruction is an alternating
`d`/`-d` paired singleton, not a same-offset invariance problem. -/
theorem singleton_neg_of_singleton
    (boundary :
      MidpointExceptionAFixingSupportIntersectionNegInvariantBoundary labeling)
    (d : ZMod 19) (hd : d ≠ 0)
    (p : labeling.data.toAFiberCoordinates.P)
    (hsingleton :
      labeling.midpointExceptionAFixingSupportIntersection
        (midpointOf d) (midpointOf_ne_zero hd) = {p}) :
    labeling.midpointExceptionAFixingSupportIntersection
        (midpointOf (-d)) (midpointOf_ne_zero (neg_ne_zero.mpr hd)) =
      {labeling.aFiberReflectionCoordPerm p} := by
  classical
  ext q
  constructor
  · intro hq
    have hpre :
        labeling.aFiberReflectionCoordPerm q ∈
          labeling.midpointExceptionAFixingSupportIntersection
            (midpointOf d) (midpointOf_ne_zero hd) := by
      have htransport :=
        boundary.aFiberReflection_mem_intersection_neg (-d)
          (neg_ne_zero.mpr hd) q hq
      simpa using htransport
    have hthetaq : labeling.aFiberReflectionCoordPerm q = p := by
      simpa [hsingleton] using hpre
    have happly :
        labeling.aFiberReflectionCoordPerm
            (labeling.aFiberReflectionCoordPerm q) =
          labeling.aFiberReflectionCoordPerm p := by
      simpa using congrArg labeling.aFiberReflectionCoordPerm hthetaq
    simpa [labeling.aFiberReflectionCoordPerm_involutive q] using happly
  · intro hq
    have hqeq : q = labeling.aFiberReflectionCoordPerm p := by
      simpa using hq
    have hp :
        p ∈ labeling.midpointExceptionAFixingSupportIntersection
          (midpointOf d) (midpointOf_ne_zero hd) := by
      simp [hsingleton]
    have htransport :=
      boundary.aFiberReflection_mem_intersection_neg d hd p hp
    simpa [hqeq] using htransport

end MidpointExceptionAFixingSupportIntersectionNegInvariantBoundary

/-- Boundary input excluding the only one-point pattern left by the
negative-offset transport: a singleton at offset `d` paired with the reflected
singleton at offset `-d`. -/
structure MidpointExceptionAFixingSupportNoPairedSingletonBoundary
    (labeling : BranchOrbitABCReflectionLabeling h) : Prop where
  not_paired_singleton :
    ∀ d : ZMod 19, ∀ hd : d ≠ 0,
      ∀ p : labeling.data.toAFiberCoordinates.P,
        p ∈ labeling.aFiberReflectionSupport →
          ¬ (labeling.midpointExceptionAFixingSupportIntersection
                (midpointOf d) (midpointOf_ne_zero hd) = {p} ∧
              labeling.midpointExceptionAFixingSupportIntersection
                (midpointOf (-d)) (midpointOf_ne_zero (neg_ne_zero.mpr hd)) =
                  {labeling.aFiberReflectionCoordPerm p})

namespace MidpointExceptionAFixingSupportNoPairedSingletonBoundary

variable {labeling : BranchOrbitABCReflectionLabeling h}

/-- Negative-offset transport reduces `no_card_one` to ruling out the paired
singleton pattern. -/
def toMidpointExceptionAFixingSupportNoCardOneBoundary
    (boundary :
      MidpointExceptionAFixingSupportNoPairedSingletonBoundary labeling)
    (transport :
      MidpointExceptionAFixingSupportIntersectionNegInvariantBoundary
        labeling) :
    MidpointExceptionAFixingSupportNoCardOneBoundary labeling where
  not_singleton_intersection := by
    intro d hd hsingleton
    rcases hsingleton with ⟨p, hp_singleton⟩
    have hp_inter :
        p ∈ labeling.midpointExceptionAFixingSupportIntersection
          (midpointOf d) (midpointOf_ne_zero hd) := by
      simp [hp_singleton]
    have hp_support : p ∈ labeling.aFiberReflectionSupport :=
      (labeling.mem_midpointExceptionAFixingSupportIntersection
        (midpointOf d) (midpointOf_ne_zero hd) p).1 hp_inter |>.2
    exact boundary.not_paired_singleton d hd p hp_support
      ⟨hp_singleton,
        transport.singleton_neg_of_singleton d hd p hp_singleton⟩

/-- Direct `no_card_one` consequence of excluding paired singletons. -/
theorem no_card_one
    (boundary :
      MidpointExceptionAFixingSupportNoPairedSingletonBoundary labeling)
    (transport :
      MidpointExceptionAFixingSupportIntersectionNegInvariantBoundary
        labeling)
    (d : ZMod 19) (hd : d ≠ 0) :
    (labeling.midpointExceptionAFixingSupportIntersection
      (midpointOf d) (midpointOf_ne_zero hd)).card ≠ 1 :=
  (boundary.toMidpointExceptionAFixingSupportNoCardOneBoundary transport)
    |>.no_card_one d hd

end MidpointExceptionAFixingSupportNoPairedSingletonBoundary

namespace MidpointEquationSetAFixingNegInvariantBoundary

variable {labeling : BranchOrbitABCReflectionLabeling h}

/-- Under the midpoint criterion, negative-offset equation transport gives
negative-offset exception transport. -/
def toMidpointExceptionSetAFixingNegInvariantBoundary
    (boundary : MidpointEquationSetAFixingNegInvariantBoundary labeling)
    (criterion : MidpointReflectionCriterionBoundary labeling) :
    MidpointExceptionSetAFixingNegInvariantBoundary labeling where
  aFiberReflection_mem_midpointExceptionSet_neg := by
    intro d hd p hp
    exact
      (criterion.midpoint_equation_iff_exception
        (midpointOf (-d)) (midpointOf_ne_zero (neg_ne_zero.mpr hd))
        (labeling.aFiberReflectionCoordPerm p)).1
        (boundary.aFiberReflection_mem_midpointEquationSet_neg d hd p
          ((criterion.midpoint_equation_iff_exception
            (midpointOf d) (midpointOf_ne_zero hd) p).2 hp))

end MidpointEquationSetAFixingNegInvariantBoundary

/-- The proven endpoint negative-offset transport and midpoint criterion
supply midpoint-exception negative-offset transport. -/
def midpointExceptionSetAFixingNegInvariantBoundary
    (labeling : BranchOrbitABCReflectionLabeling h)
    (criterion : MidpointReflectionCriterionBoundary labeling) :
    MidpointExceptionSetAFixingNegInvariantBoundary labeling :=
  labeling.midpointEquationSetAFixingNegInvariantBoundary
    |>.toMidpointExceptionSetAFixingNegInvariantBoundary criterion

/-- The proven endpoint negative-offset transport and midpoint criterion
also supply negative-offset transport for the midpoint-exception/A-fixing
support intersections. -/
def midpointExceptionAFixingSupportIntersectionNegInvariantBoundary
    (labeling : BranchOrbitABCReflectionLabeling h)
    (criterion : MidpointReflectionCriterionBoundary labeling) :
    MidpointExceptionAFixingSupportIntersectionNegInvariantBoundary labeling :=
  (labeling.midpointExceptionSetAFixingNegInvariantBoundary criterion)
    |>.toMidpointExceptionAFixingSupportIntersectionNegInvariantBoundary

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
