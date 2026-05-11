import Moore57.MidpointExceptionECardTwoContradiction
import Moore57.AFiberCoordinatesOfBranchesMatchingId
import Moore57.MidpointMiddleSupportRotationBridge
import Moore57.BranchOrbitABCReferenceSolutionGeometryBoundary

/-!
# Reference-side support complement from disjointness (default-base)

For the default-base coordinate scheme (`BranchOrbitABCFromCenter.toAFiberCoordinates`)
where the matching equivalence is the identity, the natural-language Lemma 6.4
result `Fix(A_d) ⊆ F` follows directly from Lemma 6.3 (the midpoint-exception
disjointness boundary):

* a `referenceMatchingSolutionSet`-member `p` satisfies `p = rotationCoordPerm d 0 p`
  (from matching = id),
* if also `p ∈ aFiberReflectionSupport`, the rotation-bridge places `p` in
  `midpointMiddleSupport d`, hence in `midpointExceptionSet d hd`,
* combined with `p ∈ aFiberReflectionSupport`, `p` is in the intersection,
* which Lemma 6.3 (specialized at `midpointOf (2 * d) = d`) proves empty.

This makes `ReferenceRotationMatchingSolutionAFixingSupportComplBoundary` a
consequence of the natural-language Lemma 6.3 alone — the natural-language
proof's Lemma 6.4 inclusion is exactly this Lean derivation.
-/

namespace Moore57

open Finset

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

local instance instReferenceMatchingSupportComplPFintype
    {h : D19ActsOnMoore57 V Γ}
    (labeling : BranchOrbitABCReflectionLabeling h) :
    Fintype labeling.data.toAFiberCoordinates.P :=
  labeling.data.toAFiberCoordinates.P_fintype

local instance instReferenceMatchingSupportComplDecidableEq
    (α : Type*) : DecidableEq α :=
  Classical.decEq α

namespace BranchOrbitABCReflectionLabeling

variable {h : D19ActsOnMoore57 V Γ}

/-- Helper: substitute `midpointExceptionSet` along an index equality. -/
private theorem midpointExceptionSet_index_subst
    (labeling : BranchOrbitABCReflectionLabeling h)
    {m m' : ZMod 19} (hmm' : m = m') (hm : m ≠ 0) (hm' : m' ≠ 0) :
    labeling.midpointExceptionSet m hm =
      labeling.midpointExceptionSet m' hm' := by
  subst hmm'
  rfl

/-- The reference-side support-complement boundary for any labeling whose
matching equivalence is the identity (default-base), given Lemma 6.3
disjointness.

Natural-language form: `Fix(A_d) ⊆ F` (Lemma 6.4 inclusion).  Proof goes via
the Bridge `mem_midpointMiddleSupport_iff` and the disjointness boundary at
`midpointOf (2 * d) = d`. -/
def referenceRotationMatchingSolutionAFixingSupportComplBoundary_of_disjointness_matchingId
    (labeling : BranchOrbitABCReflectionLabeling h)
    (disjointness : MidpointExceptionDisjointAFixingSupportBoundary labeling)
    (matching_id :
      ∀ d : ZMod 19, ∀ hd : (0 : ZMod 19) ≠ d,
        ∀ p : labeling.data.toAFiberCoordinates.P,
          AFiberCoordinates.matchingEquiv h.isMoore
              labeling.data.toAFiberCoordinates 0 d hd p = p) :
    ReferenceRotationMatchingSolutionAFixingSupportComplBoundary labeling where
  reference_matching_solution_subset_aFiberReflectionSupport_compl := by
    intro d hd p hp
    classical
    rw [Finset.mem_compl]
    intro hpSupport
    -- From p ∈ referenceMatchingSolutionSet, extract the matching equation.
    have h0d : (0 : ZMod 19) ≠ 0 + d := index_ne_add_of_ne_zero hd
    have hpMatchEq :
        AFiberCoordinates.matchingEquiv h.isMoore
            labeling.data.toAFiberCoordinates 0 (0 + d)
            (index_ne_add_of_ne_zero hd) p =
          labeling.data.toAFiberRotationEquivariance.coordPerm d 0 p :=
      (labeling.mem_referenceMatchingSolutionSet d hd p).1 hp
    -- Use matching_id to collapse the LHS to `p`.
    have hpId :
        AFiberCoordinates.matchingEquiv h.isMoore
            labeling.data.toAFiberCoordinates 0 (0 + d)
            (index_ne_add_of_ne_zero hd) p = p :=
      matching_id (0 + d) h0d p
    have hpFixed :
        p = labeling.data.toAFiberRotationEquivariance.coordPerm d 0 p :=
      hpId.symm.trans hpMatchEq
    -- Hence `(rot.coordPerm d 0).symm p = p`.
    have hpSymm :
        (labeling.data.toAFiberRotationEquivariance.coordPerm d 0).symm p = p := by
      conv_lhs => rw [hpFixed]
      exact
        (labeling.data.toAFiberRotationEquivariance.coordPerm d 0).symm_apply_apply
          p
    -- By the rotation bridge, `p ∈ midpointMiddleSupport d`.
    have hpMM : p ∈ labeling.midpointMiddleSupport d := by
      rw [labeling.mem_midpointMiddleSupport_iff_rotationCoordPerm_symm_mem_aFiberReflectionSupport
        d p]
      rw [hpSymm]
      exact hpSupport
    -- And `p ∈ midpointExceptionSet d hd` via matching = id.
    have hpExc : p ∈ labeling.midpointExceptionSet d hd := by
      rw [labeling.mem_midpointExceptionSet d hd p]
      rw [hpId]
      exact hpMM
    -- Lemma 6.3 disjointness, instantiated at `2 * d` so that `midpointOf (2*d) = d`.
    have h2dne : (2 : ZMod 19) * d ≠ 0 := two_mul_ne_zero_zmod19 hd
    have hMidEq : midpointOf ((2 : ZMod 19) * d) = d := by
      dsimp [midpointOf]
      rw [← mul_assoc, inv_mul_cancel₀ two_ne_zero_zmod19, one_mul]
    have hDisj :=
      disjointness.midpointException_disjoint_aFiberReflectionSupport
        ((2 : ZMod 19) * d) h2dne
    -- Translate the disjointness at `midpointOf (2*d)` to disjointness at `d`.
    have hExcEq :
        labeling.midpointExceptionSet (midpointOf ((2 : ZMod 19) * d))
            (midpointOf_ne_zero h2dne) =
          labeling.midpointExceptionSet d hd :=
      labeling.midpointExceptionSet_index_subst hMidEq
        (midpointOf_ne_zero h2dne) hd
    rw [hExcEq] at hDisj
    exact (Finset.disjoint_left.mp hDisj) hpExc hpSupport

/-- For any `BranchOrbitABCFromCenter` data, the resulting coordinate's matching
equivalence at index `(0, d)` for `d ≠ 0` is the identity. -/
private theorem matching_id_of_fromCenter
    (data : BranchOrbitABCFromCenter h)
    {d : ZMod 19} (hd : (0 : ZMod 19) ≠ d)
    (p : data.toAFiberCoordinates.P) :
    AFiberCoordinates.matchingEquiv h.isMoore data.toAFiberCoordinates 0 d hd p =
      p :=
  BranchOrbitABCFromCenter.toAFiberCoordinates_matchingEquiv_zero_apply data hd p

/-- Specialization to any `BranchOrbitABCReflectionLabeling` whose underlying
data is a `BranchOrbitABCFromCenter`.  This applies to the default-base
labeling. -/
def referenceRotationMatchingSolutionAFixingSupportComplBoundary_of_disjointness
    (labeling : BranchOrbitABCReflectionLabeling h)
    (disjointness : MidpointExceptionDisjointAFixingSupportBoundary labeling) :
    ReferenceRotationMatchingSolutionAFixingSupportComplBoundary labeling :=
  labeling.referenceRotationMatchingSolutionAFixingSupportComplBoundary_of_disjointness_matchingId
    disjointness
    (fun _d hd p => matching_id_of_fromCenter labeling.data hd p)

/-- Final assembly: criterion + supportCard give
`ReferenceRotationMatchingSolutionAFixingSupportComplBoundary` (the
natural-language Lemma 6.4 inclusion `Fix(A_d) ⊆ F`) for the default-base
coordinate scheme via the closed Lemma 6.3. -/
def referenceRotationMatchingSolutionAFixingSupportComplBoundary_of_criterion_supportCard
    (labeling : BranchOrbitABCReflectionLabeling h)
    (criterion : MidpointReflectionCriterionBoundary labeling)
    (supportCard : AFixingReflectionFixedNeighborCardBoundary labeling) :
    ReferenceRotationMatchingSolutionAFixingSupportComplBoundary labeling :=
  labeling.referenceRotationMatchingSolutionAFixingSupportComplBoundary_of_disjointness
    (labeling.midpointExceptionDisjointAFixingSupportBoundary_of_criterion_supportCard
      criterion supportCard)

end BranchOrbitABCReflectionLabeling

end

end Moore57
