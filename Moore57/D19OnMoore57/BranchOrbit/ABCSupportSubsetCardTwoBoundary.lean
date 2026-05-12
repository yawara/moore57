import Moore57.D19OnMoore57.BranchOrbit.ABCExceptionCardTwoBoundary

/-!
# All-support midpoint exceptions as the card-two case

The natural-language proof treats the case `E ⊆ S_m` as the two-point case
for `S_m ∩ E`, because the A-fixing moving support `E` has cardinality two.
This file records that finite-set conversion explicitly.
-/

namespace Moore57

open Finset

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

local instance instSupportSubsetCardTwoBoundaryPFintype
    {h : D19ActsOnMoore57 V Γ}
    (labeling : BranchOrbitABCReflectionLabeling h) :
    Fintype labeling.data.toAFiberCoordinates.P :=
  labeling.data.toAFiberCoordinates.P_fintype

local instance instSupportSubsetCardTwoBoundaryDecidableEq
    (α : Type*) : DecidableEq α :=
  Classical.decEq α

namespace BranchOrbitABCReflectionLabeling

variable {h : D19ActsOnMoore57 V Γ}

/-- If all A-fixing support points lie in `S_m`, then `S_m ∩ E = E`. -/
theorem midpointExceptionAFixingSupportIntersection_eq_support_of_subset
    (labeling : BranchOrbitABCReflectionLabeling h)
    {m : ZMod 19} {hm : m ≠ 0}
    (hsubset :
      labeling.aFiberReflectionSupport ⊆ labeling.midpointExceptionSet m hm) :
    labeling.midpointExceptionAFixingSupportIntersection m hm =
      labeling.aFiberReflectionSupport := by
  classical
  ext p
  constructor
  · intro hp
    exact
      (labeling.mem_midpointExceptionAFixingSupportIntersection m hm p).1 hp |>.2
  · intro hp
    exact
      (labeling.mem_midpointExceptionAFixingSupportIntersection m hm p).2
        ⟨hsubset hp, hp⟩

/-- Cardinality form of
`midpointExceptionAFixingSupportIntersection_eq_support_of_subset`. -/
theorem midpointExceptionAFixingSupportIntersection_card_eq_support_card_of_subset
    (labeling : BranchOrbitABCReflectionLabeling h)
    {m : ZMod 19} {hm : m ≠ 0}
    (hsubset :
      labeling.aFiberReflectionSupport ⊆ labeling.midpointExceptionSet m hm) :
    (labeling.midpointExceptionAFixingSupportIntersection m hm).card =
      labeling.aFiberReflectionSupport.card := by
  rw [labeling.midpointExceptionAFixingSupportIntersection_eq_support_of_subset
    hsubset]

/-- With the A-fixing support-size boundary, `E ⊆ S_m` gives the card-two
case for `S_m ∩ E`. -/
theorem midpointExceptionAFixingSupportIntersection_card_two_of_subset
    (labeling : BranchOrbitABCReflectionLabeling h)
    (supportCard : AFixingReflectionFixedNeighborCardBoundary labeling)
    {m : ZMod 19} {hm : m ≠ 0}
    (hsubset :
      labeling.aFiberReflectionSupport ⊆ labeling.midpointExceptionSet m hm) :
    (labeling.midpointExceptionAFixingSupportIntersection m hm).card = 2 := by
  rw [labeling.midpointExceptionAFixingSupportIntersection_card_eq_support_card_of_subset
    hsubset]
  exact supportCard.aFiberReflectionSupport_card_two

/-- Boundary form of the all-support/card-two case, indexed by the same
offsets used in the endpoint argument. -/
structure MidpointExceptionAFixingSupportAllSubsetBoundary
    (labeling : BranchOrbitABCReflectionLabeling h) : Prop where
  all_support_subset_exception :
    ∀ d : ZMod 19, ∀ hd : d ≠ 0,
      labeling.aFiberReflectionSupport ⊆
        labeling.midpointExceptionSet (midpointOf d) (midpointOf_ne_zero hd)

namespace MidpointExceptionAFixingSupportAllSubsetBoundary

variable {labeling : BranchOrbitABCReflectionLabeling h}

/-- The all-support boundary is exactly the positive card-two branch once the
support has cardinality two. -/
theorem intersection_card_two
    (boundary :
      MidpointExceptionAFixingSupportAllSubsetBoundary labeling)
    (supportCard : AFixingReflectionFixedNeighborCardBoundary labeling)
    (d : ZMod 19) (hd : d ≠ 0) :
    (labeling.midpointExceptionAFixingSupportIntersection
      (midpointOf d) (midpointOf_ne_zero hd)).card = 2 := by
  exact
    labeling.midpointExceptionAFixingSupportIntersection_card_two_of_subset
      supportCard (boundary.all_support_subset_exception d hd)

/-- The all-support boundary is incompatible with the existing no-card-two
boundary. -/
theorem not_no_card_two
    (boundary :
      MidpointExceptionAFixingSupportAllSubsetBoundary labeling)
    (supportCard : AFixingReflectionFixedNeighborCardBoundary labeling)
    (noCardTwo :
      MidpointExceptionAFixingSupportNoCardTwoBoundary labeling) :
    False := by
  have hd : (1 : ZMod 19) ≠ 0 := by decide
  exact
    noCardTwo.no_card_two supportCard 1 hd
      (boundary.intersection_card_two supportCard 1 hd)

end MidpointExceptionAFixingSupportAllSubsetBoundary

end BranchOrbitABCReflectionLabeling

end

end Moore57
