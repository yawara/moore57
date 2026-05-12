import Moore57.D19OnMoore57.BranchOrbit.ABCFinalGapReportBoundary
import Moore57.D19OnMoore57.BranchOrbit.ABCEndpointPairedSymmetryBoundary

/-!
# Endpoint-paired final boundary

This file gives the final-gap report an endpoint-paired path.  The endpoint
field stores the corrected paired adjacency boundary from
`BranchOrbitABCEndpointPairedSymmetryBoundary`, rather than repackaging the
diagnostic `EndpointSignNoReflectedReferenceNegMatchingBoundary`.

Paired adjacency alone reaches the corrected target `R (A p)`.  The existing
final theorem path still expects the older endpoint target `R p`, so the
conversion into `BranchOrbitABCActionLevelMinimalRemainingRefinedBoundary`
takes a separately named remaining endpoint target-equality boundary.
-/

namespace Moore57

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- Endpoint sign-adjacency issue in corrected paired form.

This is the final-report wrapper around
`EndpointSignPairedAdjacencyBoundary`; it intentionally avoids the older
diagnostic no-premise boundary. -/
structure BranchOrbitABCEndpointPairedSignAdjacencyIssueBoundary
    {h : D19ActsOnMoore57 V Γ}
    (labeling : BranchOrbitABCReflectionLabeling h) : Prop where
  pairedAdjacency :
    BranchOrbitABCReflectionLabeling.EndpointSignPairedAdjacencyBoundary
      labeling

namespace BranchOrbitABCEndpointPairedSignAdjacencyIssueBoundary

variable {h : D19ActsOnMoore57 V Γ}
variable {labeling : BranchOrbitABCReflectionLabeling h}

/-- Forget the report wrapper back to the paired endpoint-adjacency boundary. -/
def toEndpointSignPairedAdjacencyBoundary
    (boundary :
      BranchOrbitABCEndpointPairedSignAdjacencyIssueBoundary labeling) :
    BranchOrbitABCReflectionLabeling.EndpointSignPairedAdjacencyBoundary
      labeling :=
  boundary.pairedAdjacency

/-- Paired endpoint adjacency gives the corrected paired common-neighbor input
with target `R (A p)`. -/
def toMidpointExceptionEndpointPairedAdjCommonNeighborBasicBoundary
    (boundary :
      BranchOrbitABCEndpointPairedSignAdjacencyIssueBoundary labeling) :
    BranchOrbitABCReflectionLabeling.MidpointExceptionEndpointPairedAdjCommonNeighborBasicBoundary
      labeling :=
  boundary.pairedAdjacency
    |>.toMidpointExceptionEndpointPairedAdjCommonNeighborBasicBoundary

/-- Repackage an existing paired endpoint-adjacency boundary as a final-report
issue. -/
def ofEndpointSignPairedAdjacencyBoundary
    (boundary :
      BranchOrbitABCReflectionLabeling.EndpointSignPairedAdjacencyBoundary
        labeling) :
    BranchOrbitABCEndpointPairedSignAdjacencyIssueBoundary labeling where
  pairedAdjacency := boundary

/-- Repackage paired negative-endpoint matching as the corrected paired
endpoint-adjacency issue.  This uses only the paired target `R (A p)`. -/
def ofNegativeMatchingPair
    (paired :
      BranchOrbitABCReflectionLabeling.EndpointSignNegativeMatchingPairBoundary
        labeling) :
    BranchOrbitABCEndpointPairedSignAdjacencyIssueBoundary labeling where
  pairedAdjacency := paired.toEndpointSignPairedAdjacencyBoundary

end BranchOrbitABCEndpointPairedSignAdjacencyIssueBoundary

/-- The explicit remaining endpoint target equality needed to rejoin the
existing final theorem path.

This names the extra `R (A p) = R p` dependency separately from paired
adjacency. -/
structure BranchOrbitABCEndpointPairedRemainingTargetEqualityBoundary
    {h : D19ActsOnMoore57 V Γ}
    (labeling : BranchOrbitABCReflectionLabeling h) : Prop where
  remainingEndpointTargetEquality :
    BranchOrbitABCReflectionLabeling.EndpointSignPairedTargetEqualityBoundary
      labeling

namespace BranchOrbitABCEndpointPairedRemainingTargetEqualityBoundary

variable {h : D19ActsOnMoore57 V Γ}
variable {labeling : BranchOrbitABCReflectionLabeling h}

/-- Forget the report wrapper back to the paired endpoint target equality. -/
def toEndpointSignPairedTargetEqualityBoundary
    (boundary :
      BranchOrbitABCEndpointPairedRemainingTargetEqualityBoundary labeling) :
    BranchOrbitABCReflectionLabeling.EndpointSignPairedTargetEqualityBoundary
      labeling :=
  boundary.remainingEndpointTargetEquality

/-- Repackage an existing paired target-equality boundary as the named
remaining endpoint target equality. -/
def ofEndpointSignPairedTargetEqualityBoundary
    (boundary :
      BranchOrbitABCReflectionLabeling.EndpointSignPairedTargetEqualityBoundary
        labeling) :
    BranchOrbitABCEndpointPairedRemainingTargetEqualityBoundary labeling where
  remainingEndpointTargetEquality := boundary

/-- Coordinate same-target data supplies the named remaining endpoint target
equality. -/
def ofNegativeMatchingPairSameTarget
    {paired :
      BranchOrbitABCReflectionLabeling.EndpointSignNegativeMatchingPairBoundary
        labeling}
    (sameTarget :
      BranchOrbitABCReflectionLabeling.EndpointSignNegativeMatchingPairBoundary.SameNegativeEndpointTargetBoundary
        paired) :
    BranchOrbitABCEndpointPairedRemainingTargetEqualityBoundary labeling where
  remainingEndpointTargetEquality :=
    sameTarget.toEndpointSignPairedTargetEqualityBoundary

end BranchOrbitABCEndpointPairedRemainingTargetEqualityBoundary

namespace BranchOrbitABCEndpointPairedSignAdjacencyIssueBoundary

variable {h : D19ActsOnMoore57 V Γ}
variable {labeling : BranchOrbitABCReflectionLabeling h}

/-- Paired endpoint adjacency recovers the older endpoint-sign adjacency
boundary only after adding the named remaining endpoint target equality. -/
def toEndpointSignAdjacencyBoundary
    (boundary :
      BranchOrbitABCEndpointPairedSignAdjacencyIssueBoundary labeling)
    (targetEquality :
      BranchOrbitABCEndpointPairedRemainingTargetEqualityBoundary labeling) :
    BranchOrbitABCReflectionLabeling.EndpointSignAdjacencyBoundary labeling :=
  boundary.pairedAdjacency.toEndpointSignAdjacencyBoundary
    targetEquality.remainingEndpointTargetEquality

end BranchOrbitABCEndpointPairedSignAdjacencyIssueBoundary

/-- Structured final-gap report whose endpoint field is the corrected paired
adjacency issue.  It does not include the old endpoint target equality. -/
structure BranchOrbitABCEndpointPairedFinalGapBoundary
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
  endpointSignPairedAdjacency :
    BranchOrbitABCEndpointPairedSignAdjacencyIssueBoundary labeling
  doublingReflectedEquation :
    BranchOrbitABCDoublingReflectedEquationIssueBoundary labeling
  supportSubsetException :
    BranchOrbitABCSupportSubsetExceptionIssueBoundary labeling

namespace BranchOrbitABCEndpointPairedFinalGapBoundary

variable {h : D19ActsOnMoore57 V Γ}

/-- The endpoint component available from the paired report without target
identification: the corrected paired common-neighbor input. -/
def toMidpointExceptionEndpointPairedAdjCommonNeighborBasicBoundary
    (boundary : BranchOrbitABCEndpointPairedFinalGapBoundary h) :
    BranchOrbitABCReflectionLabeling.MidpointExceptionEndpointPairedAdjCommonNeighborBasicBoundary
      boundary.labeling :=
  boundary.endpointSignPairedAdjacency
    |>.toMidpointExceptionEndpointPairedAdjCommonNeighborBasicBoundary

/-- Convert the paired endpoint field to the older endpoint-sign adjacency
boundary using the separately named remaining target equality. -/
def toEndpointSignAdjacencyBoundary
    (boundary : BranchOrbitABCEndpointPairedFinalGapBoundary h)
    (targetEquality :
      BranchOrbitABCEndpointPairedRemainingTargetEqualityBoundary
        boundary.labeling) :
    BranchOrbitABCReflectionLabeling.EndpointSignAdjacencyBoundary
      boundary.labeling :=
  boundary.endpointSignPairedAdjacency.toEndpointSignAdjacencyBoundary
    targetEquality

/-- Convert the paired final-gap report into the existing refined minimal
remaining boundary, with the remaining endpoint target equality explicit. -/
def toActionLevelMinimalRemainingRefinedBoundary
    (boundary : BranchOrbitABCEndpointPairedFinalGapBoundary h)
    (targetEquality :
      BranchOrbitABCEndpointPairedRemainingTargetEqualityBoundary
        boundary.labeling) :
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
    boundary.toEndpointSignAdjacencyBoundary targetEquality

/-- Convert the paired report to the common-neighbor reduced boundary, again
requiring the explicit remaining endpoint target equality. -/
def toActionLevelCommonNeighborReducedBoundary
    (boundary : BranchOrbitABCEndpointPairedFinalGapBoundary h)
    (targetEquality :
      BranchOrbitABCEndpointPairedRemainingTargetEqualityBoundary
        boundary.labeling) :
    BranchOrbitABCActionLevelCommonNeighborReducedBoundary h :=
  boundary.toActionLevelMinimalRemainingRefinedBoundary targetEquality
    |>.toActionLevelCommonNeighborReducedBoundary

/-- Convert the paired report to the Lean-aware final boundary, with the
target equality still explicit at the call site. -/
noncomputable def toLeanAwareFixedStarFinalBoundary
    (boundary : BranchOrbitABCEndpointPairedFinalGapBoundary h)
    (targetEquality :
      BranchOrbitABCEndpointPairedRemainingTargetEqualityBoundary
        boundary.labeling) :
    BranchOrbitABCReflectionLabeling.LeanAwareFixedStarFinalBoundary
      boundary.starCounts.toReflectionFixedStarBoundary boundary.labeling :=
  boundary.toActionLevelMinimalRemainingRefinedBoundary targetEquality
    |>.toLeanAwareFixedStarFinalBoundary

end BranchOrbitABCEndpointPairedFinalGapBoundary

/-- Endpoint-paired final boundary that can use the existing final theorem.

The additional field is deliberately only the named remaining endpoint target
equality; paired adjacency itself is kept separate in
`pairedFinalGap.endpointSignPairedAdjacency`. -/
structure BranchOrbitABCEndpointPairedFinalBoundary
    (h : D19ActsOnMoore57 V Γ) where
  pairedFinalGap : BranchOrbitABCEndpointPairedFinalGapBoundary h
  endpointPairedRemainingTargetEquality :
    BranchOrbitABCEndpointPairedRemainingTargetEqualityBoundary
      pairedFinalGap.labeling

namespace BranchOrbitABCEndpointPairedFinalBoundary

variable {h : D19ActsOnMoore57 V Γ}

/-- Convert the endpoint-paired final package to the existing refined minimal
remaining boundary. -/
def toActionLevelMinimalRemainingRefinedBoundary
    (boundary : BranchOrbitABCEndpointPairedFinalBoundary h) :
    BranchOrbitABCActionLevelMinimalRemainingRefinedBoundary h :=
  boundary.pairedFinalGap.toActionLevelMinimalRemainingRefinedBoundary
    boundary.endpointPairedRemainingTargetEquality

/-- Convert the endpoint-paired final package to the common-neighbor reduced
boundary. -/
def toActionLevelCommonNeighborReducedBoundary
    (boundary : BranchOrbitABCEndpointPairedFinalBoundary h) :
    BranchOrbitABCActionLevelCommonNeighborReducedBoundary h :=
  boundary.toActionLevelMinimalRemainingRefinedBoundary
    |>.toActionLevelCommonNeighborReducedBoundary

/-- Convert the endpoint-paired final package to the Lean-aware final
boundary. -/
noncomputable def toLeanAwareFixedStarFinalBoundary
    (boundary : BranchOrbitABCEndpointPairedFinalBoundary h) :
    BranchOrbitABCReflectionLabeling.LeanAwareFixedStarFinalBoundary
      boundary.pairedFinalGap.starCounts.toReflectionFixedStarBoundary
        boundary.pairedFinalGap.labeling :=
  boundary.toActionLevelMinimalRemainingRefinedBoundary
    |>.toLeanAwareFixedStarFinalBoundary

end BranchOrbitABCEndpointPairedFinalBoundary

/-- No endpoint-paired final boundary can coexist with the representation
component boundary once the remaining endpoint target equality is supplied. -/
theorem no_D19_endpointPairedFinalBoundary
    (h : D19ActsOnMoore57 V Γ) :
    ¬ ∃ _representationComponents :
          D19ActsOnMoore57.RepresentationCharacterComponentsBoundary h,
        Nonempty (BranchOrbitABCEndpointPairedFinalBoundary h) := by
  rintro ⟨representationComponents, ⟨boundary⟩⟩
  exact no_D19_actionLevelMinimalRemainingRefinedBoundary h
    ⟨representationComponents,
      ⟨boundary.toActionLevelMinimalRemainingRefinedBoundary⟩⟩

end

end Moore57
