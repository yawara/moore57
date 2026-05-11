import Moore57.D19OnMoore57.BranchOrbit.BranchOrbitABCCenterNeighborBaseFrontier
import Moore57.D19OnMoore57.Reflection.ReflectionStarSmallCandidateExclusion
import Moore57.D19OnMoore57.Reflection.ReflectionTraceSmallCandidateReduction

/-!
# Geometry boundary for trace-remaining reflection candidates

After trace reduction, a reflection fixed count is one of
`6, 10, 16, 26, 36, 46, 56`.  This file records the geometric split for the
non-`56` alternatives:

* the nonregular branch gives the fixed-center leaf condition used by the
  existing labeled-reflection/index frontiers;
* the regular branch is exactly the `10` case, where all three
  center-neighbor rotation orbits are preserved.

Thus a global attempt to keep every reflection in a non-`56` candidate either
already supplies `ReflectionFixedCenterLeafBoundary`, or it leaves the clean
regular-`10` all-orbits-preserved boundary as the next geometric obstruction.
-/

namespace Moore57

open Finset

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- Trace-remaining candidates except the paper target `56`. -/
def ReflectionTraceRemainingNon56Candidate
    (h : D19ActsOnMoore57 V Γ) (k : ZMod 19) : Prop :=
  fixedVertexCount (h.smulEquiv (DihedralGroup.sr k)) = 6 ∨
  fixedVertexCount (h.smulEquiv (DihedralGroup.sr k)) = 10 ∨
  fixedVertexCount (h.smulEquiv (DihedralGroup.sr k)) = 16 ∨
  fixedVertexCount (h.smulEquiv (DihedralGroup.sr k)) = 26 ∨
  fixedVertexCount (h.smulEquiv (DihedralGroup.sr k)) = 36 ∨
  fixedVertexCount (h.smulEquiv (DihedralGroup.sr k)) = 46

/-- Local, per-reflection form of the fixed-center leaf boundary. -/
structure ReflectionFixedCenterLeafAt
    (h : D19ActsOnMoore57 V Γ) (k : ZMod 19) : Prop where
  degree_le_one :
    (h.fixedInducedGraph (DihedralGroup.sr k)).degree
        (reflectionRotationFixedCenterVertex h k) ≤ 1

namespace ReflectionFixedCenterLeafAt

variable {h : D19ActsOnMoore57 V Γ} {k : ZMod 19}

/-- Convert the local fixed-induced degree bound to the local fixed-neighbor
count bound consumed by the reflected-index frontier. -/
theorem fixed_center_neighbors_card_le_one
    (leaf : ReflectionFixedCenterLeafAt h k) :
    ((Γ.neighborFinset h.rotationFixedCenter).filter fun y =>
      h.smul (DihedralGroup.sr k) y = y).card ≤ 1 := by
  have hdegree :=
    h.fixedInducedGraph_degree_eq_fixedNeighborFinset_card
      (DihedralGroup.sr k) (reflectionRotationFixedCenterVertex h k)
  have hcard :
      (reflectionFixedNeighborFinset h k h.rotationFixedCenter).card ≤ 1 := by
    simpa [reflectionFixedNeighborFinset, reflectionRotationFixedCenterVertex] using
      hdegree.symm.trans_le leaf.degree_le_one
  simpa [reflectionFixedNeighborFinset] using hcard

/-- The local fixed-center leaf condition forces a moved reflected index for
any chosen three-orbit center-neighbor decomposition. -/
theorem exists_reflectionCenterNeighborOrbitIndex_ne
    (leaf : ReflectionFixedCenterLeafAt h k)
    (base : Fin 3 → V)
    (base_adj : ∀ q : Fin 3, Γ.Adj h.rotationFixedCenter (base q))
    (base_pairwise_disjoint :
      ∀ q r : Fin 3, q ≠ r →
        Disjoint (h.rotationOrbitFinset (base q))
          (h.rotationOrbitFinset (base r)))
    (base_cover :
      Γ.neighborFinset h.rotationFixedCenter = h.orbitFamilyUnion base) :
    ∃ b : Fin 3,
      BranchOrbitABCReflectionLabeling.reflectionCenterNeighborOrbitIndex
        (h := h) base base_adj base_cover k b ≠ b :=
  BranchOrbitABCReflectionLabeling.exists_reflectionCenterNeighborOrbitIndex_ne_of_fixed_neighbors_card_le_one
    (h := h) base base_adj base_pairwise_disjoint base_cover k
    leaf.fixed_center_neighbors_card_le_one

/-- Default-base moved-index consequence of the local fixed-center leaf
condition. -/
theorem exists_remainingCenterNeighborBase_index_ne
    (leaf : ReflectionFixedCenterLeafAt h k) :
    ∃ b : Fin 3,
      BranchOrbitABCReflectionLabeling.reflectionCenterNeighborOrbitIndex
        (h := h)
        (remainingCenterNeighborOrbitBase h)
        (remainingCenterNeighborOrbitBase_adj (h := h))
        (remainingCenterNeighborOrbitBase_cover (h := h))
        k b ≠ b :=
  leaf.exists_reflectionCenterNeighborOrbitIndex_ne
    (remainingCenterNeighborOrbitBase h)
    (remainingCenterNeighborOrbitBase_adj (h := h))
    (remainingCenterNeighborOrbitBase_pairwise_disjoint (h := h))
    (remainingCenterNeighborOrbitBase_cover (h := h))

/-- The local fixed-center leaf condition supplies the existing labeled
reflection-pair boundary on the default center-neighbor base. -/
noncomputable def toHasLabeledReflectionPair_defaultBase
    (leaf : ReflectionFixedCenterLeafAt h k) :
    BranchOrbitABCReflectionLabeling.HasLabeledReflectionPair h := by
  classical
  rcases leaf.exists_remainingCenterNeighborBase_index_ne with ⟨b, hb⟩
  exact
    BranchOrbitABCReflectionLabeling.hasLabeledReflectionPair_of_remainingCenterNeighborBase_index_ne
      (h := h) hb

end ReflectionFixedCenterLeafAt

/-- Regular-`10` boundary left by the trace-compatible candidates.  It is the
exact opposite quotient-orbit geometry from the fixed-center leaf branch:
every center-neighbor rotation orbit is preserved by the reflection. -/
def ReflectionRegularTenAllCenterNeighborOrbitsPreserved
    (h : D19ActsOnMoore57 V Γ) (k : ZMod 19) : Prop :=
  fixedVertexCount (h.smulEquiv (DihedralGroup.sr k)) = 10 ∧
    ∃ (base : Fin 3 → V),
    ∃ (base_adj : ∀ q : Fin 3, Γ.Adj h.rotationFixedCenter (base q)),
    ∃ (_base_pairwise_disjoint :
      ∀ q r : Fin 3, q ≠ r →
        Disjoint (h.rotationOrbitFinset (base q))
          (h.rotationOrbitFinset (base r))),
    ∃ (base_cover :
      Γ.neighborFinset h.rotationFixedCenter = h.orbitFamilyUnion base),
      (h.fixedInducedGraph (DihedralGroup.sr k)).degree
          (D19ActsOnMoore57.reflectionRotationFixedCenter h k) = 3 ∧
      (reflectionFixedNeighborFinset h k h.rotationFixedCenter).card = 3 ∧
      (∀ q : Fin 3,
        BranchOrbitABCReflectionLabeling.reflectionCenterNeighborOrbitIndex
          (h := h) base base_adj base_cover k q = q) ∧
      (∀ q : Fin 3,
        ((h.rotationOrbitFinset (base q)).filter fun z =>
          h.smul (DihedralGroup.sr k) z = z).card = 1)

namespace D19ActsOnMoore57

variable {h : D19ActsOnMoore57 V Γ}

/-- A regular reflection lands in the regular-`10` all-orbits-preserved
boundary. -/
theorem reflectionRegularTenAllCenterNeighborOrbitsPreserved_of_regular
    (k : ZMod 19)
    (hregular :
      ∃ d : ℕ,
        ∀ x : fixedVertexSet (h.smulEquiv (DihedralGroup.sr k)),
          (h.fixedInducedGraph (DihedralGroup.sr k)).degree x = d) :
    ReflectionRegularTenAllCenterNeighborOrbitsPreserved h k := by
  classical
  have hcount := h.fixedVertexCount_reflection_regular_eq_ten k hregular
  rcases
    h.reflection_regular_fixedVertexCount_eq_ten_center_orbits_preserved
      k hregular hcount with
    ⟨base, base_adj, base_pairwise_disjoint, base_cover, hdegree,
      hneighbors, hpreserved, hcards⟩
  exact ⟨hcount, base, base_adj, base_pairwise_disjoint, base_cover,
    hdegree, hneighbors, hpreserved, hcards⟩

/-- A nonregular reflection fixed-induced graph gives the local fixed-center
leaf boundary. -/
theorem reflectionFixedCenterLeafAt_of_not_regular
    (k : ZMod 19)
    (hnotRegular :
      ¬ ∃ d : ℕ,
        ∀ x : fixedVertexSet (h.smulEquiv (DihedralGroup.sr k)),
          (h.fixedInducedGraph (DihedralGroup.sr k)).degree x = d) :
    ReflectionFixedCenterLeafAt h k := by
  have hstrong := h.fixedInducedGraph_isStrongZeroOne (DihedralGroup.sr k)
  rcases hstrong.exists_isStarWithCenter_of_not_regular hnotRegular with
    ⟨c, hstar⟩
  refine ⟨?_⟩
  rw [
    h.fixedInducedGraph_reflection_rotationFixedCenter_degree_eq_one_of_fixedInduced_isStarWithCenter
      k hstar]

/-- For one non-`56` trace-remaining candidate, the available geometry is
exactly: local fixed-center leaf, or regular-`10` all-orbits-preserved. -/
theorem reflection_remaining_non56_candidate_geometry
    (k : ZMod 19)
    (_hcandidate : ReflectionTraceRemainingNon56Candidate h k) :
    ReflectionFixedCenterLeafAt h k ∨
      ReflectionRegularTenAllCenterNeighborOrbitsPreserved h k := by
  by_cases hregular :
      ∃ d : ℕ,
        ∀ x : fixedVertexSet (h.smulEquiv (DihedralGroup.sr k)),
          (h.fixedInducedGraph (DihedralGroup.sr k)).degree x = d
  · exact Or.inr
      (h.reflectionRegularTenAllCenterNeighborOrbitsPreserved_of_regular k
        hregular)
  · exact Or.inl (h.reflectionFixedCenterLeafAt_of_not_regular k hregular)

/-- If every reflection is kept in a non-`56` trace-remaining candidate, then
the existing global fixed-center leaf boundary holds unless some reflection is
in the regular-`10` all-orbits-preserved boundary. -/
theorem reflection_remaining_non56_global_geometry
    (hcandidate :
      ∀ k : ZMod 19, ReflectionTraceRemainingNon56Candidate h k) :
    ReflectionFixedCenterLeafBoundary h ∨
      ∃ k : ZMod 19,
        ReflectionRegularTenAllCenterNeighborOrbitsPreserved h k := by
  classical
  by_cases hregularBoundary :
      ∃ k : ZMod 19,
        ReflectionRegularTenAllCenterNeighborOrbitsPreserved h k
  · exact Or.inr hregularBoundary
  · refine Or.inl ?_
    exact
      { degree_le_one := by
          intro k
          rcases h.reflection_remaining_non56_candidate_geometry k
              (hcandidate k) with hleaf | hregular
          · exact hleaf.degree_le_one
          · exact False.elim (hregularBoundary ⟨k, hregular⟩) }

/-- Contrapositive form: excluding the regular-`10` all-preserved boundary
turns the trace non-`56` alternatives into the existing fixed-center leaf
boundary. -/
theorem reflectionFixedCenterLeafBoundary_of_remaining_non56_no_regularTenPreserved
    (hcandidate :
      ∀ k : ZMod 19, ReflectionTraceRemainingNon56Candidate h k)
    (hnoRegular :
      ¬ ∃ k : ZMod 19,
        ReflectionRegularTenAllCenterNeighborOrbitsPreserved h k) :
    ReflectionFixedCenterLeafBoundary h := by
  rcases h.reflection_remaining_non56_global_geometry hcandidate with
    hleaf | hregular
  · exact hleaf
  · exact False.elim (hnoRegular hregular)

/-- If the fixed-center leaf route is unavailable, the remaining non-`56`
candidates force the clean regular-`10` all-preserved boundary. -/
theorem exists_regularTenPreserved_of_remaining_non56_no_fixedCenterLeaf
    (hcandidate :
      ∀ k : ZMod 19, ReflectionTraceRemainingNon56Candidate h k)
    (hnoLeaf : ¬ ReflectionFixedCenterLeafBoundary h) :
    ∃ k : ZMod 19,
      ReflectionRegularTenAllCenterNeighborOrbitsPreserved h k := by
  rcases h.reflection_remaining_non56_global_geometry hcandidate with
    hleaf | hregular
  · exact False.elim (hnoLeaf hleaf)
  · exact hregular

end D19ActsOnMoore57

/-! ## Connector to existing labeled-reflection no-go frontiers -/

/-- Leaf-side connector for a trace non-`56` candidate: once a moved default
center-neighbor index and the reference-fiber matching equation are supplied,
the existing reflected-index matching-equation connector applies. -/
structure RemainingNon56FixedCenterLeafIndexMatchingEquationConnector
    (h : D19ActsOnMoore57 V Γ) where
  k : ZMod 19
  non56Candidate : ReflectionTraceRemainingNon56Candidate h k
  leaf : ReflectionFixedCenterLeafAt h k
  b : Fin 3
  hmove :
    BranchOrbitABCReflectionLabeling.reflectionCenterNeighborOrbitIndex
      (h := h)
      (remainingCenterNeighborOrbitBase h)
      (remainingCenterNeighborOrbitBase_adj (h := h))
      (remainingCenterNeighborOrbitBase_cover (h := h))
      k b ≠ b
  referenceMatchingEquationCardTwo :
    BranchOrbitABCReflectionLabeling.ReferenceFiberMatchingEquationCardTwoOfPair
      (h := h)
      (BranchOrbitABCReflectionLabeling.hasLabeledReflectionPair_of_remainingCenterNeighborBase_index_ne
        (h := h) hmove)

namespace RemainingNon56FixedCenterLeafIndexMatchingEquationConnector

variable {h : D19ActsOnMoore57 V Γ}

/-- Forget the trace-candidate and local-leaf provenance back to the existing
reflected-index matching-equation connector. -/
noncomputable def toRemainingReflectionIndexMatchingEquationConnector
    (connector :
      RemainingNon56FixedCenterLeafIndexMatchingEquationConnector h) :
    RemainingReflectionIndexMatchingEquationConnector h :=
  RemainingReflectionIndexMatchingEquationConnector.ofRemainingCenterNeighborBase
    (h := h) connector.hmove connector.referenceMatchingEquationCardTwo

/-- Forget further to the raw labeled-reflection matching-equation connector. -/
noncomputable def toRemainingLabeledReflectionMatchingEquationConnector
    (connector :
      RemainingNon56FixedCenterLeafIndexMatchingEquationConnector h) :
    RemainingLabeledReflectionMatchingEquationConnector h :=
  connector.toRemainingReflectionIndexMatchingEquationConnector
    |>.toRemainingLabeledReflectionMatchingEquationConnector

end RemainingNon56FixedCenterLeafIndexMatchingEquationConnector

/-- Component-level no-go inherited from the existing reflected-index
matching-equation frontier. -/
theorem no_remainingNon56FixedCenterLeafIndexMatchingEquationConnector_of_components
    (h : D19ActsOnMoore57 V Γ) :
    ¬ ∃ _representationComponents : RemainingRepresentationComponents h,
        Nonempty
          (RemainingNon56FixedCenterLeafIndexMatchingEquationConnector h) := by
  rintro ⟨representationComponents, ⟨connector⟩⟩
  exact no_remainingReflectionIndexMatchingEquationConnector_of_components h
    ⟨representationComponents,
      ⟨connector.toRemainingReflectionIndexMatchingEquationConnector⟩⟩

end

end Moore57
