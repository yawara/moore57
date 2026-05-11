import Moore57.D19OnMoore57.BranchOrbit.BranchOrbitABCExceptionCaseBoundary
import Moore57.Foundations.ZMod19.DoublingOrbitBoundary

/-!
# Doubling propagation for midpoint exceptions meeting the A-fixing support

This file packages the natural-language step
`S_m ∩ E ⊆ S_{2m} ∩ E`: once the finite intersections grow under doubling,
their cardinalities are constant on all nonzero offsets in `ZMod 19`.
-/

namespace Moore57

open Finset

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

local instance instExceptionDoublingBoundaryPFintype
    {h : D19ActsOnMoore57 V Γ}
    (labeling : BranchOrbitABCReflectionLabeling h) :
    Fintype labeling.data.toAFiberCoordinates.P :=
  labeling.data.toAFiberCoordinates.P_fintype

local instance instExceptionDoublingBoundaryDecidableEq
    (α : Type*) : DecidableEq α :=
  Classical.decEq α

namespace BranchOrbitABCReflectionLabeling

variable {h : D19ActsOnMoore57 V Γ}

/-- Boundary form of the doubling inclusion for
`S_m ∩ E`, where `S_m` is the midpoint-exception set and `E` is the A-fixing
reflection support. -/
structure MidpointExceptionDoublingBoundary
    (labeling : BranchOrbitABCReflectionLabeling h) : Prop where
  double_subset :
    ∀ m : ZMod 19, ∀ hm : m ≠ 0,
      labeling.midpointExceptionAFixingSupportIntersection m hm ⊆
        labeling.midpointExceptionAFixingSupportIntersection
          ((2 : ZMod 19) * m) (two_mul_ne_zero_zmod19 hm)

namespace MidpointExceptionDoublingBoundary

variable {labeling : BranchOrbitABCReflectionLabeling h}

/-- The doubling inclusion forces all nonzero
`S_m ∩ E` cardinalities to be equal. -/
theorem card_eq
    (boundary : MidpointExceptionDoublingBoundary labeling)
    {d m : ZMod 19} (hd : d ≠ 0) (hm : m ≠ 0) :
    (labeling.midpointExceptionAFixingSupportIntersection d hd).card =
      (labeling.midpointExceptionAFixingSupportIntersection m hm).card := by
  classical
  let S : ZMod 19 → Finset labeling.data.toAFiberCoordinates.P := fun x =>
    if hx : x ≠ 0 then labeling.midpointExceptionSet x hx else ∅
  have hsubset :
      ∀ x : ZMod 19, x ≠ 0 →
        S x ∩ labeling.aFiberReflectionSupport ⊆
          S ((2 : ZMod 19) * x) ∩ labeling.aFiberReflectionSupport := by
    intro x hx p hp
    have hp' :
        p ∈ labeling.midpointExceptionAFixingSupportIntersection x hx := by
      simpa [S, hx, midpointExceptionAFixingSupportIntersection] using hp
    have hpdouble :
        p ∈ labeling.midpointExceptionAFixingSupportIntersection
          ((2 : ZMod 19) * x) (two_mul_ne_zero_zmod19 hx) :=
      boundary.double_subset x hx hp'
    simpa [S, two_mul_ne_zero_zmod19 hx,
      midpointExceptionAFixingSupportIntersection] using hpdouble
  have hcard :=
    zmod19_card_inter_values_eq_of_double_subset
      S labeling.aFiberReflectionSupport hsubset hd hm
  simpa [S, hd, hm, midpointExceptionAFixingSupportIntersection] using hcard

/-- One excluded nonzero cardinality propagates to every nonzero offset. -/
theorem card_ne_of_card_ne
    (boundary : MidpointExceptionDoublingBoundary labeling)
    {base : ZMod 19} (hbase : base ≠ 0) {n : ℕ}
    (hne : (labeling.midpointExceptionAFixingSupportIntersection
      base hbase).card ≠ n)
    (d : ZMod 19) (hd : d ≠ 0) :
    (labeling.midpointExceptionAFixingSupportIntersection d hd).card ≠ n := by
  intro hdn
  exact hne ((boundary.card_eq hbase hd).trans hdn)

/-- A single nonzero witness with cardinality not equal to `1` gives the
`no_card_one` field used by the case boundary. -/
theorem no_card_one_of_card_ne_one
    (boundary : MidpointExceptionDoublingBoundary labeling)
    {base : ZMod 19} (hbase : base ≠ 0)
    (hne_one :
      (labeling.midpointExceptionAFixingSupportIntersection
        base hbase).card ≠ 1) :
    ∀ d : ZMod 19, ∀ hd : d ≠ 0,
      (labeling.midpointExceptionAFixingSupportIntersection
        (midpointOf d) (midpointOf_ne_zero hd)).card ≠ 1 := by
  intro d hd
  exact
    boundary.card_ne_of_card_ne hbase hne_one
      (midpointOf d) (midpointOf_ne_zero hd)

/-- A single nonzero witness with cardinality not equal to `2` gives the
`no_card_two` field used by the case boundary. -/
theorem no_card_two_of_card_ne_two
    (boundary : MidpointExceptionDoublingBoundary labeling)
    {base : ZMod 19} (hbase : base ≠ 0)
    (hne_two :
      (labeling.midpointExceptionAFixingSupportIntersection
        base hbase).card ≠ 2) :
    ∀ d : ZMod 19, ∀ hd : d ≠ 0,
      (labeling.midpointExceptionAFixingSupportIntersection
        (midpointOf d) (midpointOf_ne_zero hd)).card ≠ 2 := by
  intro d hd
  exact
    boundary.card_ne_of_card_ne hbase hne_two
      (midpointOf d) (midpointOf_ne_zero hd)

/-- Constructor for the existing case boundary from a doubling inclusion and
one nonzero witness excluding each positive cardinality. -/
def toMidpointExceptionAFixingSupportCaseBoundary
    (boundary : MidpointExceptionDoublingBoundary labeling)
    (support_card_boundary : AFixingReflectionFixedNeighborCardBoundary labeling)
    {baseOne : ZMod 19} (hbaseOne : baseOne ≠ 0)
    (hne_one :
      (labeling.midpointExceptionAFixingSupportIntersection
        baseOne hbaseOne).card ≠ 1)
    {baseTwo : ZMod 19} (hbaseTwo : baseTwo ≠ 0)
    (hne_two :
      (labeling.midpointExceptionAFixingSupportIntersection
        baseTwo hbaseTwo).card ≠ 2) :
    MidpointExceptionAFixingSupportCaseBoundary labeling where
  support_card_boundary := support_card_boundary
  no_card_one := boundary.no_card_one_of_card_ne_one hbaseOne hne_one
  no_card_two := boundary.no_card_two_of_card_ne_two hbaseTwo hne_two

end MidpointExceptionDoublingBoundary

end BranchOrbitABCReflectionLabeling

end

end Moore57
