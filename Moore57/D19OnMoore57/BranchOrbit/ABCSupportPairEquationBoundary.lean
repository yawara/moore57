import Moore57.D19OnMoore57.BranchOrbit.ABCSupportPairBoundary

/-!
# Midpoint equations on a two-point A-fixing reflection support

In the card-two support case, all-support midpoint matching equations are
equivalent to checking a chosen support point and its A-fiber reflection mate.
-/

namespace Moore57

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

namespace BranchOrbitABCReflectionLabeling

variable {h : D19ActsOnMoore57 V Γ}

namespace AFixingReflectionFixedNeighborCardBoundary

variable {labeling : BranchOrbitABCReflectionLabeling h}

/-- In the two-point support case, all-support midpoint matching equations are
exactly the equations for a chosen support point and its reflection mate. -/
theorem all_support_midpoint_equations_iff_pair_midpoint_equations_of_mem
    (supportCard : AFixingReflectionFixedNeighborCardBoundary labeling)
    {p : labeling.data.toAFiberCoordinates.P}
    (hp : p ∈ labeling.aFiberReflectionSupport)
    (d : ZMod 19) (hd : d ≠ 0) :
    (∀ r : labeling.data.toAFiberCoordinates.P,
        r ∈ labeling.aFiberReflectionSupport →
          AFiberCoordinates.matchingEquiv h.isMoore
              labeling.data.toAFiberCoordinates 0
              (0 + (midpointOf d + midpointOf d))
              (index_ne_add_of_ne_zero
                (add_self_ne_zero_zmod19 (midpointOf_ne_zero hd))) r =
            labeling.midpointReflectionCoordPerm (midpointOf d) r) ↔
      AFiberCoordinates.matchingEquiv h.isMoore
          labeling.data.toAFiberCoordinates 0
          (0 + (midpointOf d + midpointOf d))
          (index_ne_add_of_ne_zero
            (add_self_ne_zero_zmod19 (midpointOf_ne_zero hd))) p =
        labeling.midpointReflectionCoordPerm (midpointOf d) p ∧
      AFiberCoordinates.matchingEquiv h.isMoore
          labeling.data.toAFiberCoordinates 0
          (0 + (midpointOf d + midpointOf d))
          (index_ne_add_of_ne_zero
            (add_self_ne_zero_zmod19 (midpointOf_ne_zero hd)))
          (labeling.aFiberReflectionCoordPerm p) =
        labeling.midpointReflectionCoordPerm (midpointOf d)
          (labeling.aFiberReflectionCoordPerm p) := by
  constructor
  · intro hall
    exact
      ⟨hall p hp,
        hall (labeling.aFiberReflectionCoordPerm p)
          (labeling.aFiberReflectionCoordPerm_mem_support_of_mem hp)⟩
  · intro hpair r hr
    rcases
      (supportCard.mem_aFiberReflectionSupport_iff_eq_or_eq_reflection_of_mem hp).1
        hr with rfl | rfl
    · exact hpair.1
    · exact hpair.2

end AFixingReflectionFixedNeighborCardBoundary

/-- Boundary form for the card-two midpoint-equation obstruction reduced to
one chosen support point and its reflection mate. -/
structure MidpointExceptionAFixingSupportPairMidpointNonEquationBoundary
    (labeling : BranchOrbitABCReflectionLabeling h) : Prop where
  not_pair_midpoint_equations_of_support :
    ∀ d : ZMod 19, ∀ hd : d ≠ 0,
      ∀ p : labeling.data.toAFiberCoordinates.P,
        p ∈ labeling.aFiberReflectionSupport →
          ¬
            (AFiberCoordinates.matchingEquiv h.isMoore
                labeling.data.toAFiberCoordinates 0
                (0 + (midpointOf d + midpointOf d))
                (index_ne_add_of_ne_zero
                  (add_self_ne_zero_zmod19 (midpointOf_ne_zero hd))) p =
              labeling.midpointReflectionCoordPerm (midpointOf d) p ∧
             AFiberCoordinates.matchingEquiv h.isMoore
                labeling.data.toAFiberCoordinates 0
                (0 + (midpointOf d + midpointOf d))
                (index_ne_add_of_ne_zero
                  (add_self_ne_zero_zmod19 (midpointOf_ne_zero hd)))
                (labeling.aFiberReflectionCoordPerm p) =
              labeling.midpointReflectionCoordPerm (midpointOf d)
                (labeling.aFiberReflectionCoordPerm p))

namespace MidpointExceptionAFixingSupportPairMidpointNonEquationBoundary

variable {labeling : BranchOrbitABCReflectionLabeling h}

/-- Convert the pairwise card-two midpoint-equation obstruction to the
existing all-support midpoint-equation obstruction. -/
def toMidpointExceptionAFixingSupportNoAllMidpointEquationsBoundary
    (boundary :
      MidpointExceptionAFixingSupportPairMidpointNonEquationBoundary labeling)
    (supportCard : AFixingReflectionFixedNeighborCardBoundary labeling) :
    MidpointExceptionAFixingSupportNoAllMidpointEquationsBoundary labeling where
  not_all_support_midpoint_equations := by
    intro d hd hall
    rcases supportCard.exists_mem_aFiberReflectionSupport with ⟨p, hp⟩
    exact boundary.not_pair_midpoint_equations_of_support d hd p hp
      ((supportCard.all_support_midpoint_equations_iff_pair_midpoint_equations_of_mem
        hp d hd).1 hall)

/-- Direct conversion to the non-containment boundary used to exclude the
card-two midpoint-exception case. -/
def toMidpointExceptionAFixingSupportNoCardTwoBoundary
    (boundary :
      MidpointExceptionAFixingSupportPairMidpointNonEquationBoundary labeling)
    (supportCard : AFixingReflectionFixedNeighborCardBoundary labeling)
    (criterion : MidpointReflectionCriterionBoundary labeling) :
    MidpointExceptionAFixingSupportNoCardTwoBoundary labeling :=
  (boundary.toMidpointExceptionAFixingSupportNoAllMidpointEquationsBoundary
      supportCard)
    |>.toMidpointExceptionAFixingSupportNoCardTwoBoundary criterion

end MidpointExceptionAFixingSupportPairMidpointNonEquationBoundary

end BranchOrbitABCReflectionLabeling

end

end Moore57
