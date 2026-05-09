import Moore57.BranchOrbitABCMinimalRemainingRefinedBoundary
import Moore57.BranchOrbitABCDoublingReflectedAdjFromEquation
import Moore57.BranchOrbitABCEndpointSignMatchingSymmetry

/-!
# Current final-gap report boundary

This file records the present endpoint and doubling gaps as Lean structures
rather than prose.  The wrappers keep the four issues separate:

* endpoint target sign/equation compatibility;
* endpoint sign adjacency, using the current no-reflected-reference diagnostic;
* doubling reflected-middle matching, with an equation-set form;
* the all-support subset exception needed to turn the doubling equation-set
  form into pointwise midpoint-equation membership.

The final package converts through the existing refined minimal boundary.
-/

namespace Moore57

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

local instance instFinalGapReportBoundaryPFintype
    {h : D19ActsOnMoore57 V Γ}
    (labeling : BranchOrbitABCReflectionLabeling h) :
    Fintype labeling.data.toAFiberCoordinates.P :=
  labeling.data.toAFiberCoordinates.P_fintype

local instance instFinalGapReportBoundaryDecidableEq
    (α : Type*) : DecidableEq α :=
  Classical.decEq α

/-- Endpoint target sign/equation issue.  This is the reduced target-sign
compatibility already isolated upstream: under the positive endpoint matching
equation, the reflected target at sign `-d` must be the desired target at
sign `d`. -/
structure BranchOrbitABCEndpointTargetSignEquationIssueBoundary
    {h : D19ActsOnMoore57 V Γ}
    (labeling : BranchOrbitABCReflectionLabeling h) : Prop where
  endpointTargetSign :
    BranchOrbitABCReflectionLabeling.EndpointMatchingAFixingTargetSignBoundary
      labeling

namespace BranchOrbitABCEndpointTargetSignEquationIssueBoundary

variable {h : D19ActsOnMoore57 V Γ}
variable {labeling : BranchOrbitABCReflectionLabeling h}

/-- Forget the report wrapper back to the upstream target-sign boundary. -/
def toEndpointMatchingAFixingTargetSignBoundary
    (boundary :
      BranchOrbitABCEndpointTargetSignEquationIssueBoundary labeling) :
    BranchOrbitABCReflectionLabeling.EndpointMatchingAFixingTargetSignBoundary
      labeling :=
  boundary.endpointTargetSign

/-- Endpoint target sign compatibility gives the coordinate endpoint matching
boundary used by the reduced final pipeline. -/
def toEndpointMatchingAFixingCoordinateBoundary
    (boundary :
      BranchOrbitABCEndpointTargetSignEquationIssueBoundary labeling) :
    BranchOrbitABCReflectionLabeling.EndpointMatchingAFixingCoordinateBoundary
      labeling :=
  boundary.endpointTargetSign
    |>.toEndpointMatchingAFixingCoordinateBoundary

end BranchOrbitABCEndpointTargetSignEquationIssueBoundary

/-- Endpoint sign-adjacency issue, in the diagnostic form from
`BranchOrbitABCEndpointSignMatchingSymmetry`: the reflected-reference negative
matching premise must not occur on the A-fixing moving support. -/
structure BranchOrbitABCEndpointSignAdjacencyIssueBoundary
    {h : D19ActsOnMoore57 V Γ}
    (labeling : BranchOrbitABCReflectionLabeling h) : Prop where
  noReflectedReferenceNegMatching :
    BranchOrbitABCReflectionLabeling.EndpointSignNoReflectedReferenceNegMatchingBoundary
      labeling

namespace BranchOrbitABCEndpointSignAdjacencyIssueBoundary

variable {h : D19ActsOnMoore57 V Γ}
variable {labeling : BranchOrbitABCReflectionLabeling h}

/-- The diagnostic no-premise form gives the endpoint sign matching boundary. -/
def toEndpointSignMatchingBoundary
    (boundary :
      BranchOrbitABCEndpointSignAdjacencyIssueBoundary labeling) :
    BranchOrbitABCReflectionLabeling.EndpointSignMatchingBoundary labeling :=
  boundary.noReflectedReferenceNegMatching
    |>.toEndpointSignMatchingBoundary

/-- The endpoint sign matching boundary gives the actual adjacency retargeting
input used by the refined minimal package. -/
def toEndpointSignAdjacencyBoundary
    (boundary :
      BranchOrbitABCEndpointSignAdjacencyIssueBoundary labeling) :
    BranchOrbitABCReflectionLabeling.EndpointSignAdjacencyBoundary labeling :=
  boundary.toEndpointSignMatchingBoundary
    |>.toEndpointSignAdjacencyBoundary

/-- Repackage an existing endpoint sign matching boundary as the diagnostic
issue form. -/
def ofEndpointSignMatchingBoundary
    (boundary :
      BranchOrbitABCReflectionLabeling.EndpointSignMatchingBoundary labeling) :
    BranchOrbitABCEndpointSignAdjacencyIssueBoundary labeling where
  noReflectedReferenceNegMatching :=
    boundary.toEndpointSignNoReflectedReferenceNegMatchingBoundary

/-- Repackage the paired negative-endpoint symmetry plus the same-target
identification as the diagnostic endpoint sign-adjacency issue. -/
def ofNegativeMatchingPairSameTarget
    (paired :
      BranchOrbitABCReflectionLabeling.EndpointSignNegativeMatchingPairBoundary
        labeling)
    (sameTarget :
      BranchOrbitABCReflectionLabeling.EndpointSignNegativeMatchingPairBoundary.SameNegativeEndpointTargetBoundary
        paired) :
    BranchOrbitABCEndpointSignAdjacencyIssueBoundary labeling :=
  ofEndpointSignMatchingBoundary
    (paired.toEndpointSignMatchingBoundary sameTarget)

end BranchOrbitABCEndpointSignAdjacencyIssueBoundary

/-- Support-subset exception issue used by the doubling equation-set reduction:
every A-fixing moving support point is assumed to lie in the corresponding
midpoint exception set. -/
structure BranchOrbitABCSupportSubsetExceptionIssueBoundary
    {h : D19ActsOnMoore57 V Γ}
    (labeling : BranchOrbitABCReflectionLabeling h) : Prop where
  support_subset_exception :
    ∀ m : ZMod 19, ∀ hm : m ≠ 0,
      labeling.aFiberReflectionSupport ⊆
        labeling.midpointExceptionSet m hm

namespace BranchOrbitABCSupportSubsetExceptionIssueBoundary

variable {h : D19ActsOnMoore57 V Γ}
variable {labeling : BranchOrbitABCReflectionLabeling h}

/-- Under the midpoint criterion, the support-subset exception supplies the
pointwise midpoint-equation membership used by the reflected matching
equation. -/
def midpointEquationMembership
    (boundary :
      BranchOrbitABCSupportSubsetExceptionIssueBoundary labeling)
    (criterion :
      BranchOrbitABCReflectionLabeling.MidpointReflectionCriterionBoundary
        labeling) :
    ∀ m : ZMod 19, ∀ hm : m ≠ 0,
      ∀ p : labeling.data.toAFiberCoordinates.P,
        p ∈ labeling.aFiberReflectionSupport →
          p ∈ labeling.midpointEquationSet m hm := by
  intro m hm p hpSupport
  exact
    labeling.mem_midpointEquationSet_of_mem_aFiberReflectionSupport_of_subset_midpointExceptionSet
      criterion (boundary.support_subset_exception m hm) hpSupport

end BranchOrbitABCSupportSubsetExceptionIssueBoundary

/-- Doubling reflected-middle matching issue, in direct matching-equation
form. -/
structure BranchOrbitABCDoublingReflectedMatchingIssueBoundary
    {h : D19ActsOnMoore57 V Γ}
    (labeling : BranchOrbitABCReflectionLabeling h) : Prop where
  reflectedMatching :
    BranchOrbitABCReflectionLabeling.MidpointExceptionDoublingMiddleReflectedMatchingBoundary
      labeling

namespace BranchOrbitABCDoublingReflectedMatchingIssueBoundary

variable {h : D19ActsOnMoore57 V Γ}
variable {labeling : BranchOrbitABCReflectionLabeling h}

/-- Convert the reflected-middle matching equation to the reflected adjacency
boundary used by the refined minimal package. -/
def toMidpointExceptionDoublingMiddleReflectedAdjBoundary
    (boundary :
      BranchOrbitABCDoublingReflectedMatchingIssueBoundary labeling) :
    BranchOrbitABCReflectionLabeling.MidpointExceptionDoublingMiddleReflectedAdjBoundary
      labeling :=
  boundary.reflectedMatching
    |>.toMidpointExceptionDoublingMiddleReflectedAdjBoundary

end BranchOrbitABCDoublingReflectedMatchingIssueBoundary

/-- Doubling reflected-middle issue, in equation-set form.  The midpoint
criterion is stored separately from the all-support subset exception so the
remaining conversion dependency is explicit. -/
structure BranchOrbitABCDoublingReflectedEquationIssueBoundary
    {h : D19ActsOnMoore57 V Γ}
    (labeling : BranchOrbitABCReflectionLabeling h) : Prop where
  midpointCriterion :
    BranchOrbitABCReflectionLabeling.MidpointReflectionCriterionBoundary
      labeling
  reflectedAdjFromEquation :
    BranchOrbitABCReflectionLabeling.MidpointExceptionDoublingMiddleReflectedAdjFromEquationBoundary
      labeling

namespace BranchOrbitABCDoublingReflectedEquationIssueBoundary

variable {h : D19ActsOnMoore57 V Γ}
variable {labeling : BranchOrbitABCReflectionLabeling h}

/-- Convert the equation-set doubling issue to direct reflected matching,
provided the support-subset exception supplies midpoint-equation membership on
the moving support. -/
def toDoublingReflectedMatchingIssueBoundary
    (boundary :
      BranchOrbitABCDoublingReflectedEquationIssueBoundary labeling)
    (supportSubset :
      BranchOrbitABCSupportSubsetExceptionIssueBoundary labeling) :
    BranchOrbitABCDoublingReflectedMatchingIssueBoundary labeling where
  reflectedMatching :=
    boundary.reflectedAdjFromEquation
      |>.toMidpointExceptionDoublingMiddleReflectedMatchingBoundary
        (supportSubset.midpointEquationMembership boundary.midpointCriterion)

/-- Convert the equation-set doubling issue to reflected adjacency, provided
the support-subset exception supplies midpoint-equation membership on the
moving support. -/
def toMidpointExceptionDoublingMiddleReflectedAdjBoundary
    (boundary :
      BranchOrbitABCDoublingReflectedEquationIssueBoundary labeling)
    (supportSubset :
      BranchOrbitABCSupportSubsetExceptionIssueBoundary labeling) :
    BranchOrbitABCReflectionLabeling.MidpointExceptionDoublingMiddleReflectedAdjBoundary
      labeling :=
  (boundary.toDoublingReflectedMatchingIssueBoundary supportSubset)
    |>.toMidpointExceptionDoublingMiddleReflectedAdjBoundary

end BranchOrbitABCDoublingReflectedEquationIssueBoundary

/-- Current structured action-level final-gap report.  The ordinary star,
center, and reference-matching fields are unchanged from the refined minimal
package; the endpoint and doubling fields are the separated issue records
above. -/
structure BranchOrbitABCCurrentFinalGapBoundary
    (h : D19ActsOnMoore57 V Γ) where
  starCounts : ReflectionFixedNeighborStarCounts h
  labeling : BranchOrbitABCReflectionLabeling h
  middle :
    BranchOrbitABCReflectionLabeling.ReflectionFixedStarMiddleBoundary
      starCounts.toReflectionFixedStarBoundary labeling
  aFixing :
    BranchOrbitABCReflectionLabeling.ReflectionFixedStarAFixingBoundary
      starCounts.toReflectionFixedStarBoundary labeling
  referenceMatching :
    BranchOrbitABCReflectionLabeling.ReferenceMatchingPipelineBoundary labeling
  endpointTargetSignEquation :
    BranchOrbitABCEndpointTargetSignEquationIssueBoundary labeling
  endpointSignAdjacency :
    BranchOrbitABCEndpointSignAdjacencyIssueBoundary labeling
  doublingReflectedEquation :
    BranchOrbitABCDoublingReflectedEquationIssueBoundary labeling
  supportSubsetException :
    BranchOrbitABCSupportSubsetExceptionIssueBoundary labeling

namespace BranchOrbitABCCurrentFinalGapBoundary

variable {h : D19ActsOnMoore57 V Γ}

/-- Convert the current final-gap report to the existing refined minimal
remaining boundary. -/
def toActionLevelMinimalRemainingRefinedBoundary
    (boundary : BranchOrbitABCCurrentFinalGapBoundary h) :
    BranchOrbitABCActionLevelMinimalRemainingRefinedBoundary h where
  starCounts := boundary.starCounts
  labeling := boundary.labeling
  middle := boundary.middle
  aFixing := boundary.aFixing
  referenceMatching := boundary.referenceMatching
  doublingReflectedAdj :=
    boundary.doublingReflectedEquation
      |>.toMidpointExceptionDoublingMiddleReflectedAdjBoundary
        boundary.supportSubsetException
  endpointTargetSign :=
    boundary.endpointTargetSignEquation
      |>.toEndpointMatchingAFixingTargetSignBoundary
  endpointSignAdjacency :=
    boundary.endpointSignAdjacency
      |>.toEndpointSignAdjacencyBoundary

/-- Convert the current final-gap report to the common-neighbor reduced
boundary. -/
def toActionLevelCommonNeighborReducedBoundary
    (boundary : BranchOrbitABCCurrentFinalGapBoundary h) :
    BranchOrbitABCActionLevelCommonNeighborReducedBoundary h :=
  boundary.toActionLevelMinimalRemainingRefinedBoundary
    |>.toActionLevelCommonNeighborReducedBoundary

/-- Convert the current final-gap report to the Lean-aware fixed-star final
boundary. -/
noncomputable def toLeanAwareFixedStarFinalBoundary
    (boundary : BranchOrbitABCCurrentFinalGapBoundary h) :
    BranchOrbitABCReflectionLabeling.LeanAwareFixedStarFinalBoundary
      boundary.starCounts.toReflectionFixedStarBoundary boundary.labeling :=
  boundary.toActionLevelMinimalRemainingRefinedBoundary
    |>.toLeanAwareFixedStarFinalBoundary

end BranchOrbitABCCurrentFinalGapBoundary

/-- No current final-gap report can coexist with the representation component
boundary. -/
theorem no_D19_currentFinalGapBoundary
    (h : D19ActsOnMoore57 V Γ) :
    ¬ ∃ _representationComponents :
          D19ActsOnMoore57.RepresentationCharacterComponentsBoundary h,
        Nonempty (BranchOrbitABCCurrentFinalGapBoundary h) := by
  rintro ⟨representationComponents, ⟨boundary⟩⟩
  exact no_D19_actionLevelMinimalRemainingRefinedBoundary h
    ⟨representationComponents,
      ⟨boundary.toActionLevelMinimalRemainingRefinedBoundary⟩⟩

end

end Moore57
