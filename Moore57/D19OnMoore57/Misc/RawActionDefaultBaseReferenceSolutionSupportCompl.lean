import Moore57.D19OnMoore57.Misc.ReferenceMatchingSupportComplFromDisjointness
import Moore57.D19OnMoore57.Reflection.ReflectionRawActionFixedStar
import Moore57.D19OnMoore57.Reflection.ReflectionRawActionFixedCenterLeaf
import Moore57.D19OnMoore57.BranchOrbit.BranchOrbitABCAFixingReflectionSupportBoundary
import Moore57.D19OnMoore57.Reflection.ReflectionRawActionDefaultBaseFrontier

/-!
# Raw-action default-base reference-side support complement

For the raw `D₁₉` action, the default-base reflection-compatible labeling
`fixedCenterLeafDefaultBaseLabeling_of_raw_action k` (for any `k : ZMod 19`)
inherits:

* the midpoint reflection criterion
  (`midpointReflectionCriterionBoundary_of_raw_action`),
* the A-fixing support-card boundary (via the fixed-star A-fixing data
  `reflectionFixedStarAFixingBoundary_of_raw_action` and its conversion).

Combined with the now-proved `ReferenceMatchingSupportComplFromDisjointness`,
this constructs `RawActionDefaultBaseReferenceSolutionSupportComplBoundary`
without any additional input — closing Rank 1 of the downstream blocker list.
-/

namespace Moore57

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

namespace D19ActsOnMoore57

/-- The raw-action default-base reference-side support complement boundary,
constructed from the now-proved Lemma 6.3 derivation plus raw-action
consequences supplying the criterion and the support-card boundary. -/
noncomputable def rawActionDefaultBaseReferenceSolutionSupportComplBoundary_of_raw_action
    (h : D19ActsOnMoore57 V Γ) :
    RawActionDefaultBaseReferenceSolutionSupportComplBoundary h where
  supportCompl k :=
    let labeling := h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k
    let criterion := labeling.midpointReflectionCriterionBoundary_of_raw_action
    let supportCard :=
      labeling.reflectionFixedStarAFixingBoundary_of_raw_action
        |>.toAFixingReflectionFixedNeighborCardBoundary
    labeling.referenceRotationMatchingSolutionAFixingSupportComplBoundary_of_criterion_supportCard
      criterion supportCard

end D19ActsOnMoore57

end

end Moore57
