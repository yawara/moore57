import Moore57.D19OnMoore57.Reflection.RawActionFixedStar
import Moore57.D19OnMoore57.BranchOrbit.ABCSupportCardFrontier
import Moore57.D19OnMoore57.BranchOrbit.ABCCardTwoAllOffsetsFinalGapBoundary
import Moore57.D19OnMoore57.BranchOrbit.ABCReferenceMatchingLocalObstructionBridge

/-!
# Raw-action default-base frontier bridge

The raw action now supplies both reflection fixed-star and fixed-center-leaf
boundaries.  This file uses those positive facts to remove the corresponding
fields from the default-base non-representation frontier constructors.
-/

namespace Moore57

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

namespace D19ActsOnMoore57

variable {h : D19ActsOnMoore57 V Γ}

/-- Hard reference-side target for the raw-action default-base labeling: every
reference matching solution lies off the A-fixing reflection moving support.
This is the support-complement form of the desired reference fixedness input. -/
structure RawActionDefaultBaseReferenceSolutionSupportComplBoundary
    (h : D19ActsOnMoore57 V Γ) : Prop where
  supportCompl :
    ∀ k : ZMod 19,
      BranchOrbitABCReflectionLabeling.ReferenceRotationMatchingSolutionAFixingSupportComplBoundary
        (h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k)

/-- Pointwise moving-support form of the raw-action default-base reference
target.  This is the Lean surface closest to a label-exchange proof: after
choosing the raw default-base labeling, no A-fixing moving coordinate may solve
the reference matching equation. -/
structure RawActionDefaultBaseReferenceMovingSolutionExclusionBoundary
    (h : D19ActsOnMoore57 V Γ) : Prop where
  movingExclusion :
    ∀ k : ZMod 19,
      BranchOrbitABCReflectionLabeling.ReferenceRotationMovingSolutionExclusionBoundary
        (h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k)

/-- Raw-action default-base package for the same-target source-exchange input
identified as the remaining reference-side hard core. -/
structure RawActionDefaultBaseReferenceSourceExchangeBoundary
    (h : D19ActsOnMoore57 V Γ) : Prop where
  sourceExchange :
    ∀ k : ZMod 19,
      BranchOrbitABCReflectionLabeling.ReferenceMatchingAFixingSourceExchangeBoundary
        (h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k)

/-- Raw-action default-base package for the adjacency form of the same-target
source-exchange input. -/
structure RawActionDefaultBaseReferenceCrossAdjacencyBoundary
    (h : D19ActsOnMoore57 V Γ) : Prop where
  crossAdjacency :
    ∀ k : ZMod 19,
      BranchOrbitABCReflectionLabeling.ReferenceMatchingAFixingCrossAdjacencyBoundary
        (h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k)

/-- Raw-action default-base package for same-offset mate-closure of reference
solutions on the A-fixing moving support.  This is a separate input from the
already-proved reflection transport, which changes the offset from `d` to
`-d`. -/
structure RawActionDefaultBaseReferenceSupportMateBoundary
    (h : D19ActsOnMoore57 V Γ) : Prop where
  supportMate :
    ∀ k : ZMod 19,
      BranchOrbitABCReflectionLabeling.ReferenceMatchingAFixingSupportMateBoundary
        (h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k)

/-- Raw-action default-base package for the support-pair no-all reference
target.  It says the two-point A-fixing moving support is never entirely
contained in one reference matching solution set. -/
structure RawActionDefaultBaseReferenceSupportNoAllBoundary
    (h : D19ActsOnMoore57 V Γ) : Prop where
  supportNoAll :
    ∀ k : ZMod 19,
      BranchOrbitABCReflectionLabeling.ReferenceMatchingAFixingSupportNoAllBoundary
        (h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k)

/-- Raw-action default-base package for the paired-solution exclusion matching
the theorem-level `d -> -d` reflection transport. -/
structure RawActionDefaultBaseReferenceNoPairedSolutionBoundary
    (h : D19ActsOnMoore57 V Γ) : Prop where
  noPairedSolution :
    ∀ k : ZMod 19,
      BranchOrbitABCReflectionLabeling.ReferenceMatchingAFixingNoPairedSolutionBoundary
        (h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k)

namespace RawActionDefaultBaseReferenceSolutionSupportComplBoundary

variable {h : D19ActsOnMoore57 V Γ}

/-- Expose the per-default-base support-complement boundary. -/
noncomputable def referenceRotationMatchingSolutionAFixingSupportComplBoundary
    (boundary : RawActionDefaultBaseReferenceSolutionSupportComplBoundary h)
    (k : ZMod 19) :
    BranchOrbitABCReflectionLabeling.ReferenceRotationMatchingSolutionAFixingSupportComplBoundary
      (h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k) :=
  boundary.supportCompl k

/-- Rephrase the hard raw-action default-base reference target as exclusion
of moving-support reference matching solutions. -/
def toReferenceRotationMovingSolutionExclusionBoundary
    (boundary : RawActionDefaultBaseReferenceSolutionSupportComplBoundary h)
    (k : ZMod 19) :
    BranchOrbitABCReflectionLabeling.ReferenceRotationMovingSolutionExclusionBoundary
      (h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k) :=
  (boundary.referenceRotationMatchingSolutionAFixingSupportComplBoundary k)
    |>.toReferenceRotationMovingSolutionExclusionBoundary

/-- The hard target gives the vertex-fixed reference-solution boundary on each
raw-action default-base labeling. -/
noncomputable def toReferenceRotationMatchingSolutionVertexFixedBoundary
    (boundary : RawActionDefaultBaseReferenceSolutionSupportComplBoundary h)
    (k : ZMod 19) :
    BranchOrbitABCReflectionLabeling.ReferenceRotationMatchingSolutionVertexFixedBoundary
      (h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k) :=
  (boundary.referenceRotationMatchingSolutionAFixingSupportComplBoundary k)
    |>.toReferenceRotationMatchingSolutionVertexFixedBoundary

/-- The hard target gives the direct reference-to-midpoint boundary on each
raw-action default-base labeling. -/
noncomputable def toReferenceRotationToMidpointReflectionBoundary
    (boundary : RawActionDefaultBaseReferenceSolutionSupportComplBoundary h)
    (k : ZMod 19) :
    BranchOrbitABCReflectionLabeling.ReferenceRotationToMidpointReflectionBoundary
      (h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k) :=
  (boundary.referenceRotationMatchingSolutionAFixingSupportComplBoundary k)
    |>.toReferenceRotationToMidpointReflectionBoundary

/-- The support-complement package also supplies the paired-solution exclusion
form on every raw-action default-base labeling. -/
def toRawActionDefaultBaseReferenceNoPairedSolutionBoundary
    (boundary : RawActionDefaultBaseReferenceSolutionSupportComplBoundary h) :
    RawActionDefaultBaseReferenceNoPairedSolutionBoundary h where
  noPairedSolution k :=
    (boundary.referenceRotationMatchingSolutionAFixingSupportComplBoundary k)
      |>.toReferenceMatchingAFixingNoPairedSolutionBoundary

/-- Existing local-obstruction packages imply the reference-side hard target.
This records the non-circular route that still needs raw/default-base local
obstruction input. -/
noncomputable def of_referenceMatchingLocalObstruction
    (localObs :
      ∀ k : ZMod 19,
        BranchOrbitABCReflectionLabeling.ReferenceMatchingLocalObstructionBoundary
          h.reflectionFixedStarBoundary_of_raw_action
          (h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k)) :
    RawActionDefaultBaseReferenceSolutionSupportComplBoundary h where
  supportCompl k :=
    (localObs k).toReferenceRotationMatchingSolutionAFixingSupportComplBoundary

/-- Existing fixed-star local-obstruction packages also imply the reference-
side hard target. -/
noncomputable def of_fixedStarLocalObstruction
    (localObs :
      ∀ k : ZMod 19,
        BranchOrbitABCReflectionLabeling.FixedStarLocalObstructionBoundary
          h.reflectionFixedStarBoundary_of_raw_action
          (h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k)) :
    RawActionDefaultBaseReferenceSolutionSupportComplBoundary h where
  supportCompl k :=
    (localObs k).toReferenceRotationMatchingSolutionAFixingSupportComplBoundary

end RawActionDefaultBaseReferenceSolutionSupportComplBoundary

namespace RawActionDefaultBaseReferenceMovingSolutionExclusionBoundary

variable {h : D19ActsOnMoore57 V Γ}

/-- Expose the per-default-base moving-support exclusion boundary. -/
def referenceRotationMovingSolutionExclusionBoundary
    (boundary : RawActionDefaultBaseReferenceMovingSolutionExclusionBoundary h)
    (k : ZMod 19) :
    BranchOrbitABCReflectionLabeling.ReferenceRotationMovingSolutionExclusionBoundary
      (h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k) :=
  boundary.movingExclusion k

/-- Moving-support exclusion is exactly the pointwise route to the
support-complement target. -/
def toRawActionDefaultBaseReferenceSolutionSupportComplBoundary
    (boundary : RawActionDefaultBaseReferenceMovingSolutionExclusionBoundary h) :
    RawActionDefaultBaseReferenceSolutionSupportComplBoundary h where
  supportCompl k :=
    (boundary.referenceRotationMovingSolutionExclusionBoundary k)
      |>.toReferenceRotationMatchingSolutionAFixingSupportComplBoundary

/-- Consequence on each raw-action default-base labeling: moving-support
exclusion fixes all reference matching solution vertices. -/
noncomputable def toReferenceRotationMatchingSolutionVertexFixedBoundary
    (boundary : RawActionDefaultBaseReferenceMovingSolutionExclusionBoundary h)
    (k : ZMod 19) :
    BranchOrbitABCReflectionLabeling.ReferenceRotationMatchingSolutionVertexFixedBoundary
      (h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k) :=
  (boundary.referenceRotationMovingSolutionExclusionBoundary k)
    |>.toReferenceRotationMatchingSolutionVertexFixedBoundary

/-- Consequence on each raw-action default-base labeling: moving-support
exclusion supplies the reference-to-midpoint comparison. -/
noncomputable def toReferenceRotationToMidpointReflectionBoundary
    (boundary : RawActionDefaultBaseReferenceMovingSolutionExclusionBoundary h)
    (k : ZMod 19) :
    BranchOrbitABCReflectionLabeling.ReferenceRotationToMidpointReflectionBoundary
      (h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k) :=
  (boundary.referenceRotationMovingSolutionExclusionBoundary k)
    |>.toReferenceRotationToMidpointReflectionBoundary

/-- Moving-support exclusion supplies the paired-solution exclusion package on
each raw-action default-base labeling. -/
def toRawActionDefaultBaseReferenceNoPairedSolutionBoundary
    (boundary : RawActionDefaultBaseReferenceMovingSolutionExclusionBoundary h) :
    RawActionDefaultBaseReferenceNoPairedSolutionBoundary h where
  noPairedSolution k :=
    (boundary.referenceRotationMovingSolutionExclusionBoundary k)
      |>.toReferenceMatchingAFixingNoPairedSolutionBoundary

end RawActionDefaultBaseReferenceMovingSolutionExclusionBoundary

namespace RawActionDefaultBaseReferenceSourceExchangeBoundary

variable {h : D19ActsOnMoore57 V Γ}

/-- Expose the per-default-base same-target source-exchange boundary. -/
def referenceMatchingAFixingSourceExchangeBoundary
    (boundary : RawActionDefaultBaseReferenceSourceExchangeBoundary h)
    (k : ZMod 19) :
    BranchOrbitABCReflectionLabeling.ReferenceMatchingAFixingSourceExchangeBoundary
      (h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k) :=
  boundary.sourceExchange k

/-- Same-target source exchange supplies the raw-action moving-exclusion
reference target. -/
def toRawActionDefaultBaseReferenceMovingSolutionExclusionBoundary
    (boundary : RawActionDefaultBaseReferenceSourceExchangeBoundary h) :
    RawActionDefaultBaseReferenceMovingSolutionExclusionBoundary h where
  movingExclusion k :=
    (boundary.referenceMatchingAFixingSourceExchangeBoundary k)
      |>.toReferenceRotationMovingSolutionExclusionBoundary

/-- Same-target source exchange and same-target cross-adjacency are equivalent
on every raw-action default-base labeling. -/
def toRawActionDefaultBaseReferenceCrossAdjacencyBoundary
    (boundary : RawActionDefaultBaseReferenceSourceExchangeBoundary h) :
    RawActionDefaultBaseReferenceCrossAdjacencyBoundary h where
  crossAdjacency k :=
    (boundary.referenceMatchingAFixingSourceExchangeBoundary k)
      |>.toReferenceMatchingAFixingCrossAdjacencyBoundary

/-- Same-target source exchange supplies the raw-action support-complement
reference target. -/
def toRawActionDefaultBaseReferenceSolutionSupportComplBoundary
    (boundary : RawActionDefaultBaseReferenceSourceExchangeBoundary h) :
    RawActionDefaultBaseReferenceSolutionSupportComplBoundary h :=
  boundary.toRawActionDefaultBaseReferenceMovingSolutionExclusionBoundary
    |>.toRawActionDefaultBaseReferenceSolutionSupportComplBoundary

/-- Same-target source exchange also supplies the paired-solution exclusion
package on every raw-action default-base labeling. -/
def toRawActionDefaultBaseReferenceNoPairedSolutionBoundary
    (boundary : RawActionDefaultBaseReferenceSourceExchangeBoundary h) :
    RawActionDefaultBaseReferenceNoPairedSolutionBoundary h :=
  boundary.toRawActionDefaultBaseReferenceMovingSolutionExclusionBoundary
    |>.toRawActionDefaultBaseReferenceNoPairedSolutionBoundary

end RawActionDefaultBaseReferenceSourceExchangeBoundary

namespace RawActionDefaultBaseReferenceSupportMateBoundary

variable {h : D19ActsOnMoore57 V Γ}

/-- Expose the per-default-base same-offset support-mate boundary. -/
def referenceMatchingAFixingSupportMateBoundary
    (boundary : RawActionDefaultBaseReferenceSupportMateBoundary h)
    (k : ZMod 19) :
    BranchOrbitABCReflectionLabeling.ReferenceMatchingAFixingSupportMateBoundary
      (h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k) :=
  boundary.supportMate k

end RawActionDefaultBaseReferenceSupportMateBoundary

/-- Raw action automatically supplies same-offset support-mate closure on each
default-base labeling, because it is a theorem of any reflection labeling after
combining reflection transport with reference solution sign symmetry. -/
def rawActionDefaultBaseReferenceSupportMateBoundary_of_raw_action :
    RawActionDefaultBaseReferenceSupportMateBoundary h where
  supportMate k :=
    (h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k)
      |>.referenceMatchingAFixingSupportMateBoundary

namespace RawActionDefaultBaseReferenceSupportNoAllBoundary

variable {h : D19ActsOnMoore57 V Γ}

/-- Expose the per-default-base support-pair no-all boundary. -/
def referenceMatchingAFixingSupportNoAllBoundary
    (boundary : RawActionDefaultBaseReferenceSupportNoAllBoundary h)
    (k : ZMod 19) :
    BranchOrbitABCReflectionLabeling.ReferenceMatchingAFixingSupportNoAllBoundary
      (h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k) :=
  boundary.supportNoAll k

/-- Support-pair no-all plus same-offset support-mate closure gives the
raw-action moving-support exclusion package.  The two-point support-card input
is supplied by the raw-action fixed-star/A-fixing boundary. -/
def toRawActionDefaultBaseReferenceMovingSolutionExclusionBoundary
    (boundary : RawActionDefaultBaseReferenceSupportNoAllBoundary h)
    (mate : RawActionDefaultBaseReferenceSupportMateBoundary h) :
    RawActionDefaultBaseReferenceMovingSolutionExclusionBoundary h where
  movingExclusion k :=
    (boundary.referenceMatchingAFixingSupportNoAllBoundary k)
      |>.toReferenceRotationMovingSolutionExclusionBoundary
        ((h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k)
          |>.reflectionFixedStarAFixingBoundary_of_raw_action
          |>.toAFixingReflectionFixedNeighborCardBoundary)
        (mate.referenceMatchingAFixingSupportMateBoundary k)

/-- Support-pair no-all plus same-offset support-mate closure gives the
raw-action support-complement package. -/
def toRawActionDefaultBaseReferenceSolutionSupportComplBoundary
    (boundary : RawActionDefaultBaseReferenceSupportNoAllBoundary h)
    (mate : RawActionDefaultBaseReferenceSupportMateBoundary h) :
    RawActionDefaultBaseReferenceSolutionSupportComplBoundary h :=
  (boundary.toRawActionDefaultBaseReferenceMovingSolutionExclusionBoundary mate)
    |>.toRawActionDefaultBaseReferenceSolutionSupportComplBoundary

/-- Support-pair no-all plus same-offset support-mate closure also gives the
paired-solution exclusion package. -/
def toRawActionDefaultBaseReferenceNoPairedSolutionBoundary
    (boundary : RawActionDefaultBaseReferenceSupportNoAllBoundary h)
    (mate : RawActionDefaultBaseReferenceSupportMateBoundary h) :
    RawActionDefaultBaseReferenceNoPairedSolutionBoundary h :=
  (boundary.toRawActionDefaultBaseReferenceMovingSolutionExclusionBoundary mate)
    |>.toRawActionDefaultBaseReferenceNoPairedSolutionBoundary

/-- Since the same-offset support-mate closure is theorem-level, the raw-action
support-pair no-all boundary alone gives moving-support exclusion. -/
def toRawActionDefaultBaseReferenceMovingSolutionExclusionBoundary_of_raw_action
    (boundary : RawActionDefaultBaseReferenceSupportNoAllBoundary h) :
    RawActionDefaultBaseReferenceMovingSolutionExclusionBoundary h :=
  boundary.toRawActionDefaultBaseReferenceMovingSolutionExclusionBoundary
    h.rawActionDefaultBaseReferenceSupportMateBoundary_of_raw_action

/-- Since the same-offset support-mate closure is theorem-level, the raw-action
support-pair no-all boundary alone gives the support-complement package. -/
def toRawActionDefaultBaseReferenceSolutionSupportComplBoundary_of_raw_action
    (boundary : RawActionDefaultBaseReferenceSupportNoAllBoundary h) :
    RawActionDefaultBaseReferenceSolutionSupportComplBoundary h :=
  boundary.toRawActionDefaultBaseReferenceSolutionSupportComplBoundary
    h.rawActionDefaultBaseReferenceSupportMateBoundary_of_raw_action

/-- Since same-offset support-mate closure is theorem-level, support-pair
no-all alone gives the paired-solution exclusion package. -/
def toRawActionDefaultBaseReferenceNoPairedSolutionBoundary_of_raw_action
    (boundary : RawActionDefaultBaseReferenceSupportNoAllBoundary h) :
    RawActionDefaultBaseReferenceNoPairedSolutionBoundary h :=
  boundary.toRawActionDefaultBaseReferenceNoPairedSolutionBoundary
    h.rawActionDefaultBaseReferenceSupportMateBoundary_of_raw_action

end RawActionDefaultBaseReferenceSupportNoAllBoundary

namespace RawActionDefaultBaseReferenceNoPairedSolutionBoundary

variable {h : D19ActsOnMoore57 V Γ}

/-- Expose the per-default-base paired-solution exclusion boundary. -/
def referenceMatchingAFixingNoPairedSolutionBoundary
    (boundary : RawActionDefaultBaseReferenceNoPairedSolutionBoundary h)
    (k : ZMod 19) :
    BranchOrbitABCReflectionLabeling.ReferenceMatchingAFixingNoPairedSolutionBoundary
      (h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k) :=
  boundary.noPairedSolution k

/-- Paired-solution exclusion gives the raw-action moving-support exclusion
package using the existing reflection transport theorem. -/
def toRawActionDefaultBaseReferenceMovingSolutionExclusionBoundary
    (boundary : RawActionDefaultBaseReferenceNoPairedSolutionBoundary h) :
    RawActionDefaultBaseReferenceMovingSolutionExclusionBoundary h where
  movingExclusion k :=
    (boundary.referenceMatchingAFixingNoPairedSolutionBoundary k)
      |>.toReferenceRotationMovingSolutionExclusionBoundary

/-- Paired-solution exclusion gives the raw-action support-complement package. -/
def toRawActionDefaultBaseReferenceSolutionSupportComplBoundary
    (boundary : RawActionDefaultBaseReferenceNoPairedSolutionBoundary h) :
    RawActionDefaultBaseReferenceSolutionSupportComplBoundary h :=
  boundary.toRawActionDefaultBaseReferenceMovingSolutionExclusionBoundary
    |>.toRawActionDefaultBaseReferenceSolutionSupportComplBoundary

end RawActionDefaultBaseReferenceNoPairedSolutionBoundary

namespace RawActionDefaultBaseReferenceCrossAdjacencyBoundary

variable {h : D19ActsOnMoore57 V Γ}

/-- Expose the per-default-base cross-adjacency boundary. -/
def referenceMatchingAFixingCrossAdjacencyBoundary
    (boundary : RawActionDefaultBaseReferenceCrossAdjacencyBoundary h)
    (k : ZMod 19) :
    BranchOrbitABCReflectionLabeling.ReferenceMatchingAFixingCrossAdjacencyBoundary
      (h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k) :=
  boundary.crossAdjacency k

/-- Cross-adjacency supplies the raw-action source-exchange package. -/
def toRawActionDefaultBaseReferenceSourceExchangeBoundary
    (boundary : RawActionDefaultBaseReferenceCrossAdjacencyBoundary h) :
    RawActionDefaultBaseReferenceSourceExchangeBoundary h where
  sourceExchange k :=
    (boundary.referenceMatchingAFixingCrossAdjacencyBoundary k)
      |>.toReferenceMatchingAFixingSourceExchangeBoundary

/-- Cross-adjacency supplies the raw-action support-complement reference
target. -/
def toRawActionDefaultBaseReferenceSolutionSupportComplBoundary
    (boundary : RawActionDefaultBaseReferenceCrossAdjacencyBoundary h) :
    RawActionDefaultBaseReferenceSolutionSupportComplBoundary h :=
  boundary.toRawActionDefaultBaseReferenceSourceExchangeBoundary
    |>.toRawActionDefaultBaseReferenceSolutionSupportComplBoundary

/-- Cross-adjacency also supplies the paired-solution exclusion package on
every raw-action default-base labeling. -/
def toRawActionDefaultBaseReferenceNoPairedSolutionBoundary
    (boundary : RawActionDefaultBaseReferenceCrossAdjacencyBoundary h) :
    RawActionDefaultBaseReferenceNoPairedSolutionBoundary h :=
  boundary.toRawActionDefaultBaseReferenceSourceExchangeBoundary
    |>.toRawActionDefaultBaseReferenceNoPairedSolutionBoundary

end RawActionDefaultBaseReferenceCrossAdjacencyBoundary

/-- Build the per-default-base moving-support exclusion target from the direct
support-exclusion hard core. -/
def referenceRotationMovingSolutionExclusionBoundary_of_raw_action_defaultBase_direct
    (k : ZMod 19)
    (hnot :
      ∀ d : ZMod 19, ∀ hd : d ≠ 0,
        ∀ p :
          ((h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k).data.toAFiberCoordinates.P),
          p ∈ ((h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k).referenceMatchingSolutionSet d hd) →
            p ∉ ((h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k).aFiberReflectionSupport)) :
    BranchOrbitABCReflectionLabeling.ReferenceRotationMovingSolutionExclusionBoundary
      (h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k) :=
  BranchOrbitABCReflectionLabeling.ReferenceRotationMovingSolutionExclusionBoundary.of_referenceMatchingSolution_not_mem_aFiberReflectionSupport
    (labeling := h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k)
    hnot

/-- Build the per-default-base support-complement target from the direct
support-exclusion hard core. -/
def referenceRotationMatchingSolutionAFixingSupportComplBoundary_of_raw_action_defaultBase_direct
    (k : ZMod 19)
    (hnot :
      ∀ d : ZMod 19, ∀ hd : d ≠ 0,
        ∀ p :
          ((h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k).data.toAFiberCoordinates.P),
          p ∈ ((h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k).referenceMatchingSolutionSet d hd) →
            p ∉ ((h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k).aFiberReflectionSupport)) :
    BranchOrbitABCReflectionLabeling.ReferenceRotationMatchingSolutionAFixingSupportComplBoundary
      (h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k) :=
  (referenceRotationMovingSolutionExclusionBoundary_of_raw_action_defaultBase_direct
      (h := h) k hnot)
    |>.toReferenceRotationMatchingSolutionAFixingSupportComplBoundary

/-- Raw-action package from the pointwise hard core excluding reference
solutions on the A-fixing moving support. -/
def rawActionDefaultBaseReferenceMovingSolutionExclusionBoundary_of_direct
    (hnot :
      ∀ k : ZMod 19, ∀ d : ZMod 19, ∀ hd : d ≠ 0,
        ∀ p :
          ((h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k).data.toAFiberCoordinates.P),
          p ∈ ((h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k).referenceMatchingSolutionSet d hd) →
            p ∉ ((h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k).aFiberReflectionSupport)) :
    RawActionDefaultBaseReferenceMovingSolutionExclusionBoundary h where
  movingExclusion k :=
    referenceRotationMovingSolutionExclusionBoundary_of_raw_action_defaultBase_direct
      (h := h) k (hnot k)

/-- Build the per-default-base paired-solution exclusion from the direct
support-exclusion hard core. -/
def referenceMatchingAFixingNoPairedSolutionBoundary_of_raw_action_defaultBase_direct
    (k : ZMod 19)
    (hnot :
      ∀ d : ZMod 19, ∀ hd : d ≠ 0,
        ∀ p :
          ((h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k).data.toAFiberCoordinates.P),
          p ∈ ((h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k).referenceMatchingSolutionSet d hd) →
            p ∉ ((h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k).aFiberReflectionSupport)) :
    BranchOrbitABCReflectionLabeling.ReferenceMatchingAFixingNoPairedSolutionBoundary
      (h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k) :=
  (referenceRotationMovingSolutionExclusionBoundary_of_raw_action_defaultBase_direct
      (h := h) k hnot)
    |>.toReferenceMatchingAFixingNoPairedSolutionBoundary

/-- Raw-action paired-solution exclusion package from the pointwise hard core
excluding reference solutions on the A-fixing moving support. -/
def rawActionDefaultBaseReferenceNoPairedSolutionBoundary_of_direct
    (hnot :
      ∀ k : ZMod 19, ∀ d : ZMod 19, ∀ hd : d ≠ 0,
        ∀ p :
          ((h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k).data.toAFiberCoordinates.P),
          p ∈ ((h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k).referenceMatchingSolutionSet d hd) →
            p ∉ ((h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k).aFiberReflectionSupport)) :
    RawActionDefaultBaseReferenceNoPairedSolutionBoundary h where
  noPairedSolution k :=
    referenceMatchingAFixingNoPairedSolutionBoundary_of_raw_action_defaultBase_direct
      (h := h) k (hnot k)

/-- Raw-action support-complement package from the pointwise hard core
excluding reference solutions on the A-fixing moving support. -/
def rawActionDefaultBaseReferenceSolutionSupportComplBoundary_of_direct
    (hnot :
      ∀ k : ZMod 19, ∀ d : ZMod 19, ∀ hd : d ≠ 0,
        ∀ p :
          ((h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k).data.toAFiberCoordinates.P),
          p ∈ ((h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k).referenceMatchingSolutionSet d hd) →
            p ∉ ((h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k).aFiberReflectionSupport)) :
    RawActionDefaultBaseReferenceSolutionSupportComplBoundary h :=
  (rawActionDefaultBaseReferenceMovingSolutionExclusionBoundary_of_direct
      (h := h) hnot)
    |>.toRawActionDefaultBaseReferenceSolutionSupportComplBoundary

/-- Raw-action constructor for the smaller reference-matching/local-obstruction
package.  It removes the `aFixing` field, which is already supplied by the raw
fixed-star data; the remaining fields are still real inputs. -/
noncomputable def referenceMatchingLocalObstructionBoundary_of_raw_action_defaultBase_fields
    (k : ZMod 19)
    (referenceMatching :
      BranchOrbitABCReflectionLabeling.ReferenceMatchingPipelineBoundary
        (h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k))
    (singletonFixed :
      BranchOrbitABCReflectionLabeling.MidpointExceptionAFixingSupportSingletonFixedBoundary
        (h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k))
    (noAllEndpointAdj :
      BranchOrbitABCReflectionLabeling.MidpointExceptionAFixingSupportNoAllEndpointAdjBoundary
        (h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k)) :
    BranchOrbitABCReflectionLabeling.ReferenceMatchingLocalObstructionBoundary
      h.reflectionFixedStarBoundary_of_raw_action
      (h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k) where
  aFixing :=
    (h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k)
      |>.reflectionFixedStarAFixingBoundary_of_raw_action
  referenceMatching := referenceMatching
  singletonFixed := singletonFixed
  noAllEndpointAdj := noAllEndpointAdj

/-- Raw-action support-complement package from the smaller local-obstruction
fields.  This is a fallback route only: the `referenceMatching` inputs must be
obtained independently, not from this support-complement target. -/
noncomputable def rawActionDefaultBaseReferenceSolutionSupportComplBoundary_of_localObstruction_fields
    (referenceMatching :
      ∀ k : ZMod 19,
        BranchOrbitABCReflectionLabeling.ReferenceMatchingPipelineBoundary
          (h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k))
    (singletonFixed :
      ∀ k : ZMod 19,
        BranchOrbitABCReflectionLabeling.MidpointExceptionAFixingSupportSingletonFixedBoundary
          (h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k))
    (noAllEndpointAdj :
      ∀ k : ZMod 19,
        BranchOrbitABCReflectionLabeling.MidpointExceptionAFixingSupportNoAllEndpointAdjBoundary
          (h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k)) :
    RawActionDefaultBaseReferenceSolutionSupportComplBoundary h :=
  RawActionDefaultBaseReferenceSolutionSupportComplBoundary.of_referenceMatchingLocalObstruction
      (fun k =>
        h.referenceMatchingLocalObstructionBoundary_of_raw_action_defaultBase_fields
          k (referenceMatching k) (singletonFixed k) (noAllEndpointAdj k))

/-- Target theorem surface for the raw-action default-base reference
support-complement boundary.  Supplying this boundary closes the reference side
of the current branch/A-fiber frontier. -/
noncomputable def referenceRotationMatchingSolutionAFixingSupportComplBoundary_of_raw_action_defaultBase
    (boundary : RawActionDefaultBaseReferenceSolutionSupportComplBoundary h)
    (k : ZMod 19) :
    BranchOrbitABCReflectionLabeling.ReferenceRotationMatchingSolutionAFixingSupportComplBoundary
      (h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k) :=
  boundary.referenceRotationMatchingSolutionAFixingSupportComplBoundary k

/-- Target theorem surface in the pointwise moving-support-exclusion spelling. -/
def referenceRotationMovingSolutionExclusionBoundary_of_raw_action_defaultBase
    (boundary : RawActionDefaultBaseReferenceMovingSolutionExclusionBoundary h)
    (k : ZMod 19) :
    BranchOrbitABCReflectionLabeling.ReferenceRotationMovingSolutionExclusionBoundary
      (h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k) :=
  boundary.referenceRotationMovingSolutionExclusionBoundary k

/-- Reference-to-midpoint consequence of the raw-action default-base
support-complement target. -/
noncomputable def referenceRotationToMidpointReflectionBoundary_of_raw_action_defaultBase_supportCompl
    (boundary : RawActionDefaultBaseReferenceSolutionSupportComplBoundary h)
    (k : ZMod 19) :
    BranchOrbitABCReflectionLabeling.ReferenceRotationToMidpointReflectionBoundary
      (h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k) :=
  boundary.toReferenceRotationToMidpointReflectionBoundary k

/-- Raw action supplies the corrected all-offset endpoint obstruction on every
default-base labeling.  This is the useful replacement for trying to prove the
older single-offset `noAllEndpointAdj` shape from the card-two common-neighbor
construction. -/
def noAllOffsetsEndpointAdj_of_raw_action_defaultBase
    (k : ZMod 19) :
    BranchOrbitABCReflectionLabeling.NoAllOffsetsEndpointAdj
        (h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k) :=
  (h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k)
    |>.reflectionFixedStarAFixingBoundary_of_raw_action
    |>.toAFixingReflectionFixedNeighborCardBoundary
    |>.toNoAllOffsetsEndpointAdj

/-- Raw action supplies the all-offset no-support-subset boundary on every
default-base labeling. -/
def noAllOffsetsSupportSubsetBoundary_of_raw_action_defaultBase
    (k : ZMod 19) :
    BranchOrbitABCReflectionLabeling.NoAllOffsetsSupportSubsetBoundary
        (h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k) :=
  h.noAllOffsetsEndpointAdj_of_raw_action_defaultBase k
    |>.toNoAllOffsetsSupportSubsetBoundary
      ((h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k)
        |>.midpointReflectionCriterionBoundary_of_raw_action)

/-- Raw action rules out the global all-offset support-subset exception on
every default-base labeling. -/
theorem not_supportSubsetExceptionIssueBoundary_of_raw_action_defaultBase
    (k : ZMod 19) :
    ¬ BranchOrbitABCSupportSubsetExceptionIssueBoundary
        (h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k) :=
  h.noAllOffsetsSupportSubsetBoundary_of_raw_action_defaultBase k
    |>.not_supportSubsetExceptionIssueBoundary

/-- No raw-action default-base labeling can satisfy the global support-subset
exception package. -/
theorem not_exists_supportSubsetExceptionIssueBoundary_of_raw_action_defaultBase :
    ¬ ∃ k : ZMod 19,
        BranchOrbitABCSupportSubsetExceptionIssueBoundary
          (h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k) := by
  rintro ⟨k, supportSubset⟩
  exact h.not_supportSubsetExceptionIssueBoundary_of_raw_action_defaultBase k
    supportSubset

/-- Raw-action constructor for the default-base A-fixing frontier.  The
fixed-star and fixed-center-leaf fields are supplied automatically from the raw
action; the remaining inputs are the genuinely local default-base fields. -/
noncomputable def
    remainingNonRepresentationFrontierAfterDefaultBaseAFixingConnector_of_raw_action_fields
    (k : ZMod 19)
    (aFixing :
      BranchOrbitABCReflectionLabeling.ReflectionFixedStarAFixingBoundary
        h.reflectionFixedStarBoundary_of_raw_action
        (h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k))
    (referenceMatching :
      BranchOrbitABCReflectionLabeling.ReferenceMatchingPipelineBoundary
        (h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k))
    (no_card_one :
      ∀ d : ZMod 19, ∀ hd : d ≠ 0,
        ((h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k)
            |>.midpointExceptionAFixingSupportIntersection
              (midpointOf d) (midpointOf_ne_zero hd)).card ≠ 1)
    (noAllEndpointAdj :
      BranchOrbitABCReflectionLabeling.MidpointExceptionAFixingSupportNoAllEndpointAdjBoundary
        (h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k)) :
    RemainingNonRepresentationFrontierAfterDefaultBaseAFixingConnector h where
  star := h.reflectionFixedStarBoundary_of_raw_action
  fixedCenterLeaf := h.reflectionFixedCenterLeafBoundary_of_raw_action
  k := k
  aFixing := aFixing
  referenceMatching := referenceMatching
  no_card_one := no_card_one
  noAllEndpointAdj := noAllEndpointAdj

/-- Raw-action constructor for the default-base A-fixing frontier with the
A-fixing center identification filled automatically.  The remaining inputs are
now the reference-matching pipeline, card-one exclusion, and endpoint-adjacency
obstruction. -/
noncomputable def
    remainingNonRepresentationFrontierAfterDefaultBaseAFixingConnector_of_raw_action
    (k : ZMod 19)
    (referenceMatching :
      BranchOrbitABCReflectionLabeling.ReferenceMatchingPipelineBoundary
        (h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k))
    (no_card_one :
      ∀ d : ZMod 19, ∀ hd : d ≠ 0,
        ((h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k)
            |>.midpointExceptionAFixingSupportIntersection
              (midpointOf d) (midpointOf_ne_zero hd)).card ≠ 1)
    (noAllEndpointAdj :
      BranchOrbitABCReflectionLabeling.MidpointExceptionAFixingSupportNoAllEndpointAdjBoundary
        (h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k)) :
    RemainingNonRepresentationFrontierAfterDefaultBaseAFixingConnector h :=
  h.remainingNonRepresentationFrontierAfterDefaultBaseAFixingConnector_of_raw_action_fields
    k
    ((h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k)
      |>.reflectionFixedStarAFixingBoundary_of_raw_action)
    referenceMatching no_card_one noAllEndpointAdj

/-- Raw-action constructor for the default-base A-fixing frontier after reducing
the reference-matching pipeline to vertex-fixed reference solutions. -/
noncomputable def
    remainingNonRepresentationFrontierAfterDefaultBaseAFixingConnector_of_raw_action_vertexFixed
    (k : ZMod 19)
    (referenceSolutionVertexFixed :
      BranchOrbitABCReflectionLabeling.ReferenceRotationMatchingSolutionVertexFixedBoundary
        (h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k))
    (no_card_one :
      ∀ d : ZMod 19, ∀ hd : d ≠ 0,
        ((h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k)
            |>.midpointExceptionAFixingSupportIntersection
              (midpointOf d) (midpointOf_ne_zero hd)).card ≠ 1)
    (noAllEndpointAdj :
      BranchOrbitABCReflectionLabeling.MidpointExceptionAFixingSupportNoAllEndpointAdjBoundary
        (h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k)) :
    RemainingNonRepresentationFrontierAfterDefaultBaseAFixingConnector h :=
  h.remainingNonRepresentationFrontierAfterDefaultBaseAFixingConnector_of_raw_action
    k
    ((h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k)
      |>.referenceMatchingPipelineBoundary_of_raw_action_vertexFixed
        referenceSolutionVertexFixed)
    no_card_one noAllEndpointAdj

/-- Raw-action constructor for the default-base A-fixing frontier with the
one-point exception case supplied by singleton-fixedness. -/
noncomputable def
    remainingNonRepresentationFrontierAfterDefaultBaseAFixingConnector_of_raw_action_vertexFixed_singletonFixed
    (k : ZMod 19)
    (referenceSolutionVertexFixed :
      BranchOrbitABCReflectionLabeling.ReferenceRotationMatchingSolutionVertexFixedBoundary
        (h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k))
    (singletonFixed :
      BranchOrbitABCReflectionLabeling.MidpointExceptionAFixingSupportSingletonFixedBoundary
        (h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k))
    (noAllEndpointAdj :
      BranchOrbitABCReflectionLabeling.MidpointExceptionAFixingSupportNoAllEndpointAdjBoundary
        (h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k)) :
    RemainingNonRepresentationFrontierAfterDefaultBaseAFixingConnector h :=
  h.remainingNonRepresentationFrontierAfterDefaultBaseAFixingConnector_of_raw_action_vertexFixed
    k referenceSolutionVertexFixed singletonFixed.no_card_one noAllEndpointAdj

/-- Raw-action constructor for the default-base A-fixing frontier from an
independent reference-to-midpoint comparison and endpoint target-sign
compatibility. -/
noncomputable def
    remainingNonRepresentationFrontierAfterDefaultBaseAFixingConnector_of_raw_action_referenceToMidpoint_endpointTargetSign
    (k : ZMod 19)
    (referenceToMidpoint :
      BranchOrbitABCReflectionLabeling.ReferenceRotationToMidpointReflectionBoundary
        (h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k))
    (endpointTargetSign :
      BranchOrbitABCReflectionLabeling.EndpointMatchingAFixingTargetSignBoundary
        (h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k))
    (noAllEndpointAdj :
      BranchOrbitABCReflectionLabeling.MidpointExceptionAFixingSupportNoAllEndpointAdjBoundary
        (h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k)) :
    RemainingNonRepresentationFrontierAfterDefaultBaseAFixingConnector h :=
  let labeling := h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k
  let singletonFixed :=
    endpointTargetSign.toMidpointEquationSetAFixingInvariantBoundary
      |>.toMidpointExceptionAFixingSupportSingletonFixedBoundary
        labeling.midpointReflectionCriterionBoundary_of_raw_action
  h.remainingNonRepresentationFrontierAfterDefaultBaseAFixingConnector_of_raw_action
    k
    (labeling.referenceMatchingPipelineBoundary_of_raw_action
      labeling.midpointMiddleSupportCardTwoBoundary_of_raw_action
      referenceToMidpoint)
    singletonFixed.no_card_one noAllEndpointAdj

/-- Raw-action constructor for the default-base A-fixing frontier from an
independent reference-to-midpoint comparison and the corrected negative-endpoint
label exchange. -/
noncomputable def
    remainingNonRepresentationFrontierAfterDefaultBaseAFixingConnector_of_raw_action_referenceToMidpoint_endpointNegativePair
    (k : ZMod 19)
    (referenceToMidpoint :
      BranchOrbitABCReflectionLabeling.ReferenceRotationToMidpointReflectionBoundary
        (h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k))
    (endpointNegativePair :
      BranchOrbitABCReflectionLabeling.EndpointSignNegativeMatchingPairBoundary
        (h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k))
    (noAllEndpointAdj :
      BranchOrbitABCReflectionLabeling.MidpointExceptionAFixingSupportNoAllEndpointAdjBoundary
        (h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k)) :
    RemainingNonRepresentationFrontierAfterDefaultBaseAFixingConnector h :=
  let labeling := h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k
  let criterion := labeling.midpointReflectionCriterionBoundary_of_raw_action
  let noPaired :=
    endpointNegativePair
      |>.toMidpointExceptionAFixingSupportNoPairedSingletonBoundary criterion
  let transport :=
    labeling.midpointExceptionAFixingSupportIntersectionNegInvariantBoundary
      criterion
  let noCardOne :=
    noPaired.toMidpointExceptionAFixingSupportNoCardOneBoundary transport
  h.remainingNonRepresentationFrontierAfterDefaultBaseAFixingConnector_of_raw_action
    k
    (labeling.referenceMatchingPipelineBoundary_of_raw_action
      labeling.midpointMiddleSupportCardTwoBoundary_of_raw_action
      referenceToMidpoint)
    noCardOne.no_card_one noAllEndpointAdj

/-- Raw-action constructor for the default-base A-fixing frontier from an
independent reference-to-midpoint comparison and paired endpoint adjacency. -/
noncomputable def
    remainingNonRepresentationFrontierAfterDefaultBaseAFixingConnector_of_raw_action_referenceToMidpoint_endpointPairedAdj
    (k : ZMod 19)
    (referenceToMidpoint :
      BranchOrbitABCReflectionLabeling.ReferenceRotationToMidpointReflectionBoundary
        (h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k))
    (endpointPairedAdj :
      BranchOrbitABCReflectionLabeling.EndpointSignPairedAdjacencyBoundary
        (h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k))
    (noAllEndpointAdj :
      BranchOrbitABCReflectionLabeling.MidpointExceptionAFixingSupportNoAllEndpointAdjBoundary
        (h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k)) :
    RemainingNonRepresentationFrontierAfterDefaultBaseAFixingConnector h :=
  h.remainingNonRepresentationFrontierAfterDefaultBaseAFixingConnector_of_raw_action_referenceToMidpoint_endpointNegativePair
    k referenceToMidpoint
    endpointPairedAdj.toEndpointSignNegativeMatchingPairBoundary
    noAllEndpointAdj

/-- Raw-action constructor for the default-base A-fixing frontier from an
independent reference-to-midpoint comparison and pointwise endpoint
non-adjacency.  The pointwise endpoint obstruction supplies both the paired
label exchange and the endpoint non-containment input. -/
noncomputable def
    remainingNonRepresentationFrontierAfterDefaultBaseAFixingConnector_of_raw_action_referenceToMidpoint_endpointPointwiseNonadj
    (k : ZMod 19)
    (referenceToMidpoint :
      BranchOrbitABCReflectionLabeling.ReferenceRotationToMidpointReflectionBoundary
        (h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k))
    (endpointPointwiseNonadj :
      BranchOrbitABCReflectionLabeling.MidpointExceptionAFixingSupportEndpointPointwiseNonadjBoundary
        (h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k)) :
    RemainingNonRepresentationFrontierAfterDefaultBaseAFixingConnector h :=
  let labeling := h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k
  h.remainingNonRepresentationFrontierAfterDefaultBaseAFixingConnector_of_raw_action
    k
    (labeling.referenceMatchingPipelineBoundary_of_raw_action
      labeling.midpointMiddleSupportCardTwoBoundary_of_raw_action
      referenceToMidpoint)
    (let criterion := labeling.midpointReflectionCriterionBoundary_of_raw_action
     let noPaired :=
       endpointPointwiseNonadj.toEndpointSignPairedAdjacencyBoundary
         |>.toMidpointExceptionAFixingSupportNoPairedSingletonBoundary criterion
     let transport :=
       labeling.midpointExceptionAFixingSupportIntersectionNegInvariantBoundary
         criterion
     let noCardOne :=
       noPaired.toMidpointExceptionAFixingSupportNoCardOneBoundary transport
     noCardOne.no_card_one)
    (endpointPointwiseNonadj.toMidpointExceptionAFixingSupportNoAllEndpointAdjBoundary
      (labeling.reflectionFixedStarAFixingBoundary_of_raw_action
        |>.toAFixingReflectionFixedNeighborCardBoundary))

/-- Raw-action constructor for the default-base A-fixing frontier from
reference-to-midpoint and the single-endpoint common-neighbor boundary. -/
noncomputable def
    remainingNonRepresentationFrontierAfterDefaultBaseAFixingConnector_of_raw_action_referenceToMidpoint_endpointCommonNeighborBasic
    (k : ZMod 19)
    (referenceToMidpoint :
      BranchOrbitABCReflectionLabeling.ReferenceRotationToMidpointReflectionBoundary
        (h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k))
    (endpointCommonNeighborBasic :
      BranchOrbitABCReflectionLabeling.MidpointExceptionEndpointAdjCommonNeighborBasicBoundary
        (h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k)) :
    RemainingNonRepresentationFrontierAfterDefaultBaseAFixingConnector h :=
  h.remainingNonRepresentationFrontierAfterDefaultBaseAFixingConnector_of_raw_action_referenceToMidpoint_endpointPointwiseNonadj
    k referenceToMidpoint
    endpointCommonNeighborBasic.toMidpointExceptionAFixingSupportEndpointPointwiseNonadjBoundary

/-- Raw-action constructor for the default-base A-fixing frontier from
reference-to-midpoint and endpoint-reference exchange. -/
noncomputable def
    remainingNonRepresentationFrontierAfterDefaultBaseAFixingConnector_of_raw_action_referenceToMidpoint_endpointExchangeCommonNeighbor
    (k : ZMod 19)
    (referenceToMidpoint :
      BranchOrbitABCReflectionLabeling.ReferenceRotationToMidpointReflectionBoundary
        (h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k))
    (endpointExchange :
      BranchOrbitABCReflectionLabeling.EndpointReferenceExchangeCommonNeighborBoundary
        (h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k)) :
    RemainingNonRepresentationFrontierAfterDefaultBaseAFixingConnector h :=
  h.remainingNonRepresentationFrontierAfterDefaultBaseAFixingConnector_of_raw_action_referenceToMidpoint_endpointPointwiseNonadj
    k referenceToMidpoint
    endpointExchange.toMidpointExceptionAFixingSupportEndpointPointwiseNonadjBoundary

/-- Raw-action constructor for the default-base A-fixing frontier from
reference-to-midpoint and the no-reflected-reference negative matching
diagnostic. -/
noncomputable def
    remainingNonRepresentationFrontierAfterDefaultBaseAFixingConnector_of_raw_action_referenceToMidpoint_endpointNoReflectedReferenceNegMatching
    (k : ZMod 19)
    (referenceToMidpoint :
      BranchOrbitABCReflectionLabeling.ReferenceRotationToMidpointReflectionBoundary
        (h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k))
    (endpointNoReflectedReferenceNegMatching :
      BranchOrbitABCReflectionLabeling.EndpointSignNoReflectedReferenceNegMatchingBoundary
        (h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k)) :
    RemainingNonRepresentationFrontierAfterDefaultBaseAFixingConnector h :=
  h.remainingNonRepresentationFrontierAfterDefaultBaseAFixingConnector_of_raw_action_referenceToMidpoint_endpointPointwiseNonadj
    k referenceToMidpoint
    (endpointNoReflectedReferenceNegMatching
      |>.toMidpointExceptionAFixingSupportEndpointPointwiseNonadjBoundary)

/-- Raw-action constructor for the default-base A-fixing frontier from
reference-to-midpoint and the no-positive-target endpoint diagnostic. -/
noncomputable def
    remainingNonRepresentationFrontierAfterDefaultBaseAFixingConnector_of_raw_action_referenceToMidpoint_endpointNoPositiveTarget
    (k : ZMod 19)
    (referenceToMidpoint :
      BranchOrbitABCReflectionLabeling.ReferenceRotationToMidpointReflectionBoundary
        (h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k))
    (endpointNoPositiveTarget :
      BranchOrbitABCReflectionLabeling.EndpointMatchingAFixingNoPositiveTargetBoundary
        (h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k)) :
    RemainingNonRepresentationFrontierAfterDefaultBaseAFixingConnector h :=
  h.remainingNonRepresentationFrontierAfterDefaultBaseAFixingConnector_of_raw_action_referenceToMidpoint_endpointPointwiseNonadj
    k referenceToMidpoint
    endpointNoPositiveTarget.toMidpointExceptionAFixingSupportEndpointPointwiseNonadjBoundary

/-- Raw-action constructor for the explicit default-base non-representation
frontier after removing the `star`, `fixedCenterLeaf`, and `support_card_boundary`
fields. -/
noncomputable def
    remainingNonRepresentationFrontierAfterDefaultBase_of_raw_action_fields
    (k : ZMod 19)
    (referenceMatching :
      BranchOrbitABCReflectionLabeling.ReferenceMatchingPipelineBoundary
        (h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k))
    (no_card_one :
      ∀ d : ZMod 19, ∀ hd : d ≠ 0,
        ((h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k)
            |>.midpointExceptionAFixingSupportIntersection
              (midpointOf d) (midpointOf_ne_zero hd)).card ≠ 1)
    (noAllEndpointAdj :
      BranchOrbitABCReflectionLabeling.MidpointExceptionAFixingSupportNoAllEndpointAdjBoundary
        (h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k)) :
    RemainingNonRepresentationFrontierAfterDefaultBase h :=
  (h.remainingNonRepresentationFrontierAfterDefaultBaseAFixingConnector_of_raw_action
    k referenceMatching no_card_one noAllEndpointAdj)
    |>.toRemainingNonRepresentationFrontierAfterDefaultBase

/-- Raw-action constructor for the explicit default-base frontier after reducing
the reference-matching pipeline to vertex-fixed reference solutions. -/
noncomputable def
    remainingNonRepresentationFrontierAfterDefaultBase_of_raw_action_vertexFixed_fields
    (k : ZMod 19)
    (referenceSolutionVertexFixed :
      BranchOrbitABCReflectionLabeling.ReferenceRotationMatchingSolutionVertexFixedBoundary
        (h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k))
    (no_card_one :
      ∀ d : ZMod 19, ∀ hd : d ≠ 0,
        ((h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k)
            |>.midpointExceptionAFixingSupportIntersection
              (midpointOf d) (midpointOf_ne_zero hd)).card ≠ 1)
    (noAllEndpointAdj :
      BranchOrbitABCReflectionLabeling.MidpointExceptionAFixingSupportNoAllEndpointAdjBoundary
        (h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k)) :
    RemainingNonRepresentationFrontierAfterDefaultBase h :=
  (h.remainingNonRepresentationFrontierAfterDefaultBaseAFixingConnector_of_raw_action_vertexFixed
    k referenceSolutionVertexFixed no_card_one noAllEndpointAdj)
    |>.toRemainingNonRepresentationFrontierAfterDefaultBase

/-- Raw-action constructor for the explicit default-base frontier with the
one-point exception case supplied by singleton-fixedness. -/
noncomputable def
    remainingNonRepresentationFrontierAfterDefaultBase_of_raw_action_vertexFixed_singletonFixed_fields
    (k : ZMod 19)
    (referenceSolutionVertexFixed :
      BranchOrbitABCReflectionLabeling.ReferenceRotationMatchingSolutionVertexFixedBoundary
        (h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k))
    (singletonFixed :
      BranchOrbitABCReflectionLabeling.MidpointExceptionAFixingSupportSingletonFixedBoundary
        (h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k))
    (noAllEndpointAdj :
      BranchOrbitABCReflectionLabeling.MidpointExceptionAFixingSupportNoAllEndpointAdjBoundary
        (h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k)) :
    RemainingNonRepresentationFrontierAfterDefaultBase h :=
  (h.remainingNonRepresentationFrontierAfterDefaultBaseAFixingConnector_of_raw_action_vertexFixed_singletonFixed
    k referenceSolutionVertexFixed singletonFixed noAllEndpointAdj)
    |>.toRemainingNonRepresentationFrontierAfterDefaultBase

/-- Raw-action constructor for the explicit default-base frontier from an
independent reference-to-midpoint comparison and endpoint target-sign
compatibility. -/
noncomputable def
    remainingNonRepresentationFrontierAfterDefaultBase_of_raw_action_referenceToMidpoint_endpointTargetSign_fields
    (k : ZMod 19)
    (referenceToMidpoint :
      BranchOrbitABCReflectionLabeling.ReferenceRotationToMidpointReflectionBoundary
        (h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k))
    (endpointTargetSign :
      BranchOrbitABCReflectionLabeling.EndpointMatchingAFixingTargetSignBoundary
        (h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k))
    (noAllEndpointAdj :
      BranchOrbitABCReflectionLabeling.MidpointExceptionAFixingSupportNoAllEndpointAdjBoundary
        (h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k)) :
    RemainingNonRepresentationFrontierAfterDefaultBase h :=
  (h.remainingNonRepresentationFrontierAfterDefaultBaseAFixingConnector_of_raw_action_referenceToMidpoint_endpointTargetSign
    k referenceToMidpoint endpointTargetSign noAllEndpointAdj)
    |>.toRemainingNonRepresentationFrontierAfterDefaultBase

/-- Raw-action constructor for the explicit default-base frontier from an
independent reference-to-midpoint comparison and the corrected negative-endpoint
label exchange. -/
noncomputable def
    remainingNonRepresentationFrontierAfterDefaultBase_of_raw_action_referenceToMidpoint_endpointNegativePair_fields
    (k : ZMod 19)
    (referenceToMidpoint :
      BranchOrbitABCReflectionLabeling.ReferenceRotationToMidpointReflectionBoundary
        (h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k))
    (endpointNegativePair :
      BranchOrbitABCReflectionLabeling.EndpointSignNegativeMatchingPairBoundary
        (h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k))
    (noAllEndpointAdj :
      BranchOrbitABCReflectionLabeling.MidpointExceptionAFixingSupportNoAllEndpointAdjBoundary
        (h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k)) :
    RemainingNonRepresentationFrontierAfterDefaultBase h :=
  (h.remainingNonRepresentationFrontierAfterDefaultBaseAFixingConnector_of_raw_action_referenceToMidpoint_endpointNegativePair
    k referenceToMidpoint endpointNegativePair noAllEndpointAdj)
    |>.toRemainingNonRepresentationFrontierAfterDefaultBase

/-- Raw-action constructor for the explicit default-base frontier from an
independent reference-to-midpoint comparison and paired endpoint adjacency. -/
noncomputable def
    remainingNonRepresentationFrontierAfterDefaultBase_of_raw_action_referenceToMidpoint_endpointPairedAdj_fields
    (k : ZMod 19)
    (referenceToMidpoint :
      BranchOrbitABCReflectionLabeling.ReferenceRotationToMidpointReflectionBoundary
        (h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k))
    (endpointPairedAdj :
      BranchOrbitABCReflectionLabeling.EndpointSignPairedAdjacencyBoundary
        (h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k))
    (noAllEndpointAdj :
      BranchOrbitABCReflectionLabeling.MidpointExceptionAFixingSupportNoAllEndpointAdjBoundary
        (h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k)) :
    RemainingNonRepresentationFrontierAfterDefaultBase h :=
  (h.remainingNonRepresentationFrontierAfterDefaultBaseAFixingConnector_of_raw_action_referenceToMidpoint_endpointPairedAdj
    k referenceToMidpoint endpointPairedAdj noAllEndpointAdj)
    |>.toRemainingNonRepresentationFrontierAfterDefaultBase

/-- Raw-action constructor for the explicit default-base frontier from an
independent reference-to-midpoint comparison and pointwise endpoint
non-adjacency. -/
noncomputable def
    remainingNonRepresentationFrontierAfterDefaultBase_of_raw_action_referenceToMidpoint_endpointPointwiseNonadj_fields
    (k : ZMod 19)
    (referenceToMidpoint :
      BranchOrbitABCReflectionLabeling.ReferenceRotationToMidpointReflectionBoundary
        (h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k))
    (endpointPointwiseNonadj :
      BranchOrbitABCReflectionLabeling.MidpointExceptionAFixingSupportEndpointPointwiseNonadjBoundary
        (h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k)) :
    RemainingNonRepresentationFrontierAfterDefaultBase h :=
  (h.remainingNonRepresentationFrontierAfterDefaultBaseAFixingConnector_of_raw_action_referenceToMidpoint_endpointPointwiseNonadj
    k referenceToMidpoint endpointPointwiseNonadj)
    |>.toRemainingNonRepresentationFrontierAfterDefaultBase

/-- Raw-action constructor for the explicit default-base frontier from
reference-to-midpoint and the single-endpoint common-neighbor boundary. -/
noncomputable def
    remainingNonRepresentationFrontierAfterDefaultBase_of_raw_action_referenceToMidpoint_endpointCommonNeighborBasic_fields
    (k : ZMod 19)
    (referenceToMidpoint :
      BranchOrbitABCReflectionLabeling.ReferenceRotationToMidpointReflectionBoundary
        (h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k))
    (endpointCommonNeighborBasic :
      BranchOrbitABCReflectionLabeling.MidpointExceptionEndpointAdjCommonNeighborBasicBoundary
        (h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k)) :
    RemainingNonRepresentationFrontierAfterDefaultBase h :=
  (h.remainingNonRepresentationFrontierAfterDefaultBaseAFixingConnector_of_raw_action_referenceToMidpoint_endpointCommonNeighborBasic
    k referenceToMidpoint endpointCommonNeighborBasic)
    |>.toRemainingNonRepresentationFrontierAfterDefaultBase

/-- Raw-action constructor for the explicit default-base frontier from
reference-to-midpoint and endpoint-reference exchange. -/
noncomputable def
    remainingNonRepresentationFrontierAfterDefaultBase_of_raw_action_referenceToMidpoint_endpointExchangeCommonNeighbor_fields
    (k : ZMod 19)
    (referenceToMidpoint :
      BranchOrbitABCReflectionLabeling.ReferenceRotationToMidpointReflectionBoundary
        (h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k))
    (endpointExchange :
      BranchOrbitABCReflectionLabeling.EndpointReferenceExchangeCommonNeighborBoundary
        (h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k)) :
    RemainingNonRepresentationFrontierAfterDefaultBase h :=
  (h.remainingNonRepresentationFrontierAfterDefaultBaseAFixingConnector_of_raw_action_referenceToMidpoint_endpointExchangeCommonNeighbor
    k referenceToMidpoint endpointExchange)
    |>.toRemainingNonRepresentationFrontierAfterDefaultBase

/-- Raw-action constructor for the explicit default-base frontier from
reference-to-midpoint and the no-reflected-reference negative matching
diagnostic. -/
noncomputable def
    remainingNonRepresentationFrontierAfterDefaultBase_of_raw_action_referenceToMidpoint_endpointNoReflectedReferenceNegMatching_fields
    (k : ZMod 19)
    (referenceToMidpoint :
      BranchOrbitABCReflectionLabeling.ReferenceRotationToMidpointReflectionBoundary
        (h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k))
    (endpointNoReflectedReferenceNegMatching :
      BranchOrbitABCReflectionLabeling.EndpointSignNoReflectedReferenceNegMatchingBoundary
        (h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k)) :
    RemainingNonRepresentationFrontierAfterDefaultBase h :=
  (h.remainingNonRepresentationFrontierAfterDefaultBaseAFixingConnector_of_raw_action_referenceToMidpoint_endpointNoReflectedReferenceNegMatching
    k referenceToMidpoint endpointNoReflectedReferenceNegMatching)
    |>.toRemainingNonRepresentationFrontierAfterDefaultBase

/-- Raw-action constructor for the explicit default-base frontier from
reference-to-midpoint and the no-positive-target endpoint diagnostic. -/
noncomputable def
    remainingNonRepresentationFrontierAfterDefaultBase_of_raw_action_referenceToMidpoint_endpointNoPositiveTarget_fields
    (k : ZMod 19)
    (referenceToMidpoint :
      BranchOrbitABCReflectionLabeling.ReferenceRotationToMidpointReflectionBoundary
        (h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k))
    (endpointNoPositiveTarget :
      BranchOrbitABCReflectionLabeling.EndpointMatchingAFixingNoPositiveTargetBoundary
        (h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k)) :
    RemainingNonRepresentationFrontierAfterDefaultBase h :=
  (h.remainingNonRepresentationFrontierAfterDefaultBaseAFixingConnector_of_raw_action_referenceToMidpoint_endpointNoPositiveTarget
    k referenceToMidpoint endpointNoPositiveTarget)
    |>.toRemainingNonRepresentationFrontierAfterDefaultBase

/-- Raw-action constructor for the fixed-star-local default-base frontier.  This
removes the now-proved raw fixed-star and fixed-center-leaf fields from the
connector surface. -/
noncomputable def
    remainingNonRepresentationFrontierAfterDefaultBaseFixedStarLocalConnector_of_raw_action_fields
    (k : ZMod 19)
    (fixedStarLocal :
      BranchOrbitABCReflectionLabeling.FixedStarLocalObstructionBoundary
        h.reflectionFixedStarBoundary_of_raw_action
        (h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k)) :
    RemainingNonRepresentationFrontierAfterDefaultBaseFixedStarLocalConnector h where
  star := h.reflectionFixedStarBoundary_of_raw_action
  fixedCenterLeaf := h.reflectionFixedCenterLeafBoundary_of_raw_action
  k := k
  fixedStarLocal := fixedStarLocal

end D19ActsOnMoore57

end

end Moore57
