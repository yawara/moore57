import Moore57.D19OnMoore57.BranchOrbit.ABCExceptionCardTwoBoundary
import Moore57.D19OnMoore57.BranchOrbit.Midpoint

/-!
# All-support connectors for the midpoint-exception card-two boundary

This file expands the hypothesis `E ⊆ S_m` into the pointwise midpoint
statements used in the natural-language common-neighbor contradiction.

Here `E` is `aFiberReflectionSupport` and `S_m` is `midpointExceptionSet m`.
The first connector is definitional: membership in `S_m` says that the
matching mate in the middle fiber belongs to `midpointMiddleSupport m`.  With
the midpoint criterion available, the same hypothesis also yields the endpoint
midpoint matching equation, and hence the corresponding adjacency statement.
-/

namespace Moore57

open Finset

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

local instance instExceptionAllSupportBoundaryPFintype
    {h : D19ActsOnMoore57 V Γ}
    (labeling : BranchOrbitABCReflectionLabeling h) :
    Fintype labeling.data.toAFiberCoordinates.P :=
  labeling.data.toAFiberCoordinates.P_fintype

local instance instExceptionAllSupportBoundaryDecidableEq
    (α : Type*) : DecidableEq α :=
  Classical.decEq α

namespace BranchOrbitABCReflectionLabeling

variable {h : D19ActsOnMoore57 V Γ}

/-- Pointwise expansion of `E ⊆ S_m`: if an A-fixing reflection-support
coordinate belongs to the midpoint exception set, then its matching mate in
the middle A-fiber is moved by the midpoint reflection. -/
theorem matching_mate_mem_midpointMiddleSupport_of_mem_aFiberReflectionSupport_of_subset_midpointExceptionSet
    (labeling : BranchOrbitABCReflectionLabeling h)
    {m : ZMod 19} {hm : m ≠ 0}
    (hsubset :
      labeling.aFiberReflectionSupport ⊆ labeling.midpointExceptionSet m hm)
    {p : labeling.data.toAFiberCoordinates.P}
    (hp : p ∈ labeling.aFiberReflectionSupport) :
    AFiberCoordinates.matchingEquiv h.isMoore
        labeling.data.toAFiberCoordinates 0 (0 + m)
        (index_ne_add_of_ne_zero hm) p ∈
      labeling.midpointMiddleSupport m := by
  exact (labeling.mem_midpointExceptionSet m hm p).1 (hsubset hp)

/-- With the midpoint criterion, the same `E ⊆ S_m` hypothesis promotes each
support coordinate to a solution of the endpoint midpoint equation. -/
theorem mem_midpointEquationSet_of_mem_aFiberReflectionSupport_of_subset_midpointExceptionSet
    (labeling : BranchOrbitABCReflectionLabeling h)
    (criterion : MidpointReflectionCriterionBoundary labeling)
    {m : ZMod 19} {hm : m ≠ 0}
    (hsubset :
      labeling.aFiberReflectionSupport ⊆ labeling.midpointExceptionSet m hm)
    {p : labeling.data.toAFiberCoordinates.P}
    (hp : p ∈ labeling.aFiberReflectionSupport) :
    p ∈ labeling.midpointEquationSet m hm := by
  exact (criterion.midpoint_equation_iff_exception m hm p).2 (hsubset hp)

/-- Equation form of
`mem_midpointEquationSet_of_mem_aFiberReflectionSupport_of_subset_midpointExceptionSet`. -/
theorem midpointEquation_of_mem_aFiberReflectionSupport_of_subset_midpointExceptionSet
    (labeling : BranchOrbitABCReflectionLabeling h)
    (criterion : MidpointReflectionCriterionBoundary labeling)
    {m : ZMod 19} {hm : m ≠ 0}
    (hsubset :
      labeling.aFiberReflectionSupport ⊆ labeling.midpointExceptionSet m hm)
    {p : labeling.data.toAFiberCoordinates.P}
    (hp : p ∈ labeling.aFiberReflectionSupport) :
    AFiberCoordinates.matchingEquiv h.isMoore
        labeling.data.toAFiberCoordinates 0 (0 + (m + m))
        (index_ne_add_of_ne_zero (add_self_ne_zero_zmod19 hm)) p =
      labeling.midpointReflectionCoordPerm m p := by
  exact (labeling.mem_midpointEquationSet m hm p).1
    (labeling.mem_midpointEquationSet_of_mem_aFiberReflectionSupport_of_subset_midpointExceptionSet
      criterion hsubset hp)

/-- Adjacency form of the midpoint equation obtained from `E ⊆ S_m` and the
midpoint criterion.  This is the endpoint adjacency that the matching equation
encodes. -/
theorem midpointEndpointAdj_of_mem_aFiberReflectionSupport_of_subset_midpointExceptionSet
    (labeling : BranchOrbitABCReflectionLabeling h)
    (criterion : MidpointReflectionCriterionBoundary labeling)
    {m : ZMod 19} {hm : m ≠ 0}
    (hsubset :
      labeling.aFiberReflectionSupport ⊆ labeling.midpointExceptionSet m hm)
    {p : labeling.data.toAFiberCoordinates.P}
    (hp : p ∈ labeling.aFiberReflectionSupport) :
    Γ.Adj
      (((labeling.data.toAFiberCoordinates.coord 0 p :
        {x : V // x ∈
          branchFiber Γ labeling.data.toAFiberCoordinates.u
            (labeling.data.toAFiberCoordinates.a 0)}) : V))
      (((labeling.data.toAFiberCoordinates.coord (0 + (m + m))
          ((labeling.midpointReflectionCoordPerm m) p) :
        {x : V // x ∈
          branchFiber Γ labeling.data.toAFiberCoordinates.u
            (labeling.data.toAFiberCoordinates.a (0 + (m + m)))}) : V)) := by
  exact
    (AFiberCoordinates.adj_iff_matchingEquiv_eq h.isMoore
      labeling.data.toAFiberCoordinates
      (index_ne_add_of_ne_zero (add_self_ne_zero_zmod19 hm))
      p ((labeling.midpointReflectionCoordPerm m) p)).2
      (labeling.midpointEquation_of_mem_aFiberReflectionSupport_of_subset_midpointExceptionSet
        criterion hsubset hp)

/-- Boundary form excluding `E ⊆ S_(d/2)` by denying that every support point's
midpoint mate lies in the middle moving support.  This version is purely
definitional and does not require the midpoint criterion. -/
structure MidpointExceptionAFixingSupportNoAllMatesInMiddleBoundary
    (labeling : BranchOrbitABCReflectionLabeling h) : Prop where
  not_all_support_mates_in_middle :
    ∀ d : ZMod 19, ∀ hd : d ≠ 0,
      ¬ ∀ p : labeling.data.toAFiberCoordinates.P,
        p ∈ labeling.aFiberReflectionSupport →
          AFiberCoordinates.matchingEquiv h.isMoore
              labeling.data.toAFiberCoordinates 0 (0 + midpointOf d)
              (index_ne_add_of_ne_zero (midpointOf_ne_zero hd)) p ∈
            labeling.midpointMiddleSupport (midpointOf d)

namespace MidpointExceptionAFixingSupportNoAllMatesInMiddleBoundary

variable {labeling : BranchOrbitABCReflectionLabeling h}

/-- Convert the pointwise middle-support negation into the existing
non-containment boundary `¬ E ⊆ S_(d/2)`. -/
def toMidpointExceptionAFixingSupportNoCardTwoBoundary
    (boundary :
      MidpointExceptionAFixingSupportNoAllMatesInMiddleBoundary labeling) :
    MidpointExceptionAFixingSupportNoCardTwoBoundary labeling where
  not_all_support_subset_exception := by
    intro d hd hsubset
    exact boundary.not_all_support_mates_in_middle d hd (by
      intro p hp
      exact
        labeling.matching_mate_mem_midpointMiddleSupport_of_mem_aFiberReflectionSupport_of_subset_midpointExceptionSet
          hsubset hp)

end MidpointExceptionAFixingSupportNoAllMatesInMiddleBoundary

/-- Boundary form excluding `E ⊆ S_(d/2)` by denying that every support point
satisfies the endpoint midpoint matching equation.  The conversion uses the
midpoint criterion to pass from exception-set membership to equation
membership. -/
structure MidpointExceptionAFixingSupportNoAllMidpointEquationsBoundary
    (labeling : BranchOrbitABCReflectionLabeling h) : Prop where
  not_all_support_midpoint_equations :
    ∀ d : ZMod 19, ∀ hd : d ≠ 0,
      ¬ ∀ p : labeling.data.toAFiberCoordinates.P,
        p ∈ labeling.aFiberReflectionSupport →
          AFiberCoordinates.matchingEquiv h.isMoore
              labeling.data.toAFiberCoordinates 0
              (0 + (midpointOf d + midpointOf d))
              (index_ne_add_of_ne_zero
                (add_self_ne_zero_zmod19 (midpointOf_ne_zero hd))) p =
            labeling.midpointReflectionCoordPerm (midpointOf d) p

namespace MidpointExceptionAFixingSupportNoAllMidpointEquationsBoundary

variable {labeling : BranchOrbitABCReflectionLabeling h}

/-- Convert the matching-equation negation into the existing non-containment
boundary `¬ E ⊆ S_(d/2)`. -/
def toMidpointExceptionAFixingSupportNoCardTwoBoundary
    (boundary :
      MidpointExceptionAFixingSupportNoAllMidpointEquationsBoundary labeling)
    (criterion : MidpointReflectionCriterionBoundary labeling) :
    MidpointExceptionAFixingSupportNoCardTwoBoundary labeling where
  not_all_support_subset_exception := by
    intro d hd hsubset
    exact boundary.not_all_support_midpoint_equations d hd (by
      intro p hp
      exact
        labeling.midpointEquation_of_mem_aFiberReflectionSupport_of_subset_midpointExceptionSet
          criterion hsubset hp)

end MidpointExceptionAFixingSupportNoAllMidpointEquationsBoundary

/-- Boundary form excluding `E ⊆ S_(d/2)` by denying that every support point
has the endpoint adjacency encoded by the midpoint equation. -/
structure MidpointExceptionAFixingSupportNoAllEndpointAdjBoundary
    (labeling : BranchOrbitABCReflectionLabeling h) : Prop where
  not_all_support_endpoint_adj :
    ∀ d : ZMod 19, ∀ _hd : d ≠ 0,
      ¬ ∀ p : labeling.data.toAFiberCoordinates.P,
        p ∈ labeling.aFiberReflectionSupport →
          Γ.Adj
            (((labeling.data.toAFiberCoordinates.coord 0 p :
              {x : V // x ∈
                branchFiber Γ labeling.data.toAFiberCoordinates.u
                  (labeling.data.toAFiberCoordinates.a 0)}) : V))
            (((labeling.data.toAFiberCoordinates.coord
                (0 + (midpointOf d + midpointOf d))
                (labeling.midpointReflectionCoordPerm (midpointOf d) p) :
              {x : V // x ∈
                branchFiber Γ labeling.data.toAFiberCoordinates.u
                  (labeling.data.toAFiberCoordinates.a
                    (0 + (midpointOf d + midpointOf d)))}) : V))

namespace MidpointExceptionAFixingSupportNoAllEndpointAdjBoundary

variable {labeling : BranchOrbitABCReflectionLabeling h}

/-- Convert the endpoint-adjacency negation into the existing non-containment
boundary `¬ E ⊆ S_(d/2)`. -/
def toMidpointExceptionAFixingSupportNoCardTwoBoundary
    (boundary :
      MidpointExceptionAFixingSupportNoAllEndpointAdjBoundary labeling)
    (criterion : MidpointReflectionCriterionBoundary labeling) :
    MidpointExceptionAFixingSupportNoCardTwoBoundary labeling where
  not_all_support_subset_exception := by
    intro d hd hsubset
    exact boundary.not_all_support_endpoint_adj d hd (by
      intro p hp
      exact
        labeling.midpointEndpointAdj_of_mem_aFiberReflectionSupport_of_subset_midpointExceptionSet
          criterion hsubset hp)

end MidpointExceptionAFixingSupportNoAllEndpointAdjBoundary

end BranchOrbitABCReflectionLabeling

end

end Moore57
