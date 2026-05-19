import Moore57.Foundations.ZMod19.AvoidanceBoundary

-- `native_decide` is intentional here (see `Moore57/AxiomsCheck.lean`).
set_option linter.style.nativeDecide false

/-!
# Index candidates for card-two common-neighbor constructions

This file packages the elementary `ZMod 19` choice needed in the card-two
common-neighbor boundary: for a nonzero reference index `j`, choose two
nonzero indices which avoid `j`, are distinct from each other, and therefore
have the corresponding nonzero index differences.
-/

namespace Moore57

/-- Candidate indices for the card-two common-neighbor construction relative
to a nonzero reference index `j`. -/
structure ZMod19CardTwoCandidateIndices (j : ZMod 19) where
  k : ZMod 19
  l : ZMod 19
  j_ne_zero : j ≠ 0
  k_ne_zero : k ≠ 0
  l_ne_zero : l ≠ 0
  k_ne_j : k ≠ j
  l_ne_j : l ≠ j
  k_ne_l : k ≠ l
  k_sub_j_ne_zero : k - j ≠ 0
  l_sub_j_ne_zero : l - j ≠ 0
  j_sub_k_ne_zero : j - k ≠ 0
  j_sub_l_ne_zero : j - l ≠ 0
  k_sub_l_ne_zero : k - l ≠ 0
  l_sub_k_ne_zero : l - k ≠ 0

namespace ZMod19CardTwoCandidateIndices

/-- Constructor from the basic nonzero, avoidance, and distinctness facts. -/
def ofBasic
    (j k l : ZMod 19)
    (hj : j ≠ 0) (hk0 : k ≠ 0) (hl0 : l ≠ 0)
    (hkj : k ≠ j) (hlj : l ≠ j) (hkl : k ≠ l) :
    ZMod19CardTwoCandidateIndices j where
  k := k
  l := l
  j_ne_zero := hj
  k_ne_zero := hk0
  l_ne_zero := hl0
  k_ne_j := hkj
  l_ne_j := hlj
  k_ne_l := hkl
  k_sub_j_ne_zero := sub_ne_zero.mpr hkj
  l_sub_j_ne_zero := sub_ne_zero.mpr hlj
  j_sub_k_ne_zero := sub_ne_zero.mpr hkj.symm
  j_sub_l_ne_zero := sub_ne_zero.mpr hlj.symm
  k_sub_l_ne_zero := sub_ne_zero.mpr hkl
  l_sub_k_ne_zero := sub_ne_zero.mpr hkl.symm

end ZMod19CardTwoCandidateIndices

/-- A nonzero reference index in `ZMod 19` admits two card-two candidate
indices with all required nonzero difference facts. -/
def zmod19_card_two_candidate_indices
    (j : ZMod 19) (hj : j ≠ 0) :
    ZMod19CardTwoCandidateIndices j := by
  by_cases h1 : j = (1 : ZMod 19)
  · exact
      ZMod19CardTwoCandidateIndices.ofBasic j 2 3 hj
        (by native_decide)
        (by native_decide)
        (by simpa [h1] using (by native_decide : (2 : ZMod 19) ≠ 1))
        (by simpa [h1] using (by native_decide : (3 : ZMod 19) ≠ 1))
        (by native_decide)
  · by_cases h2 : j = (2 : ZMod 19)
    · exact
        ZMod19CardTwoCandidateIndices.ofBasic j 1 3 hj
          (by native_decide)
          (by native_decide)
          (by simpa [h2] using (by native_decide : (1 : ZMod 19) ≠ 2))
          (by simpa [h2] using (by native_decide : (3 : ZMod 19) ≠ 2))
          (by native_decide)
    · exact
        ZMod19CardTwoCandidateIndices.ofBasic j 1 2 hj
          (by native_decide)
          (by native_decide)
          (by
            intro h
            exact h1 h.symm)
          (by
            intro h
            exact h2 h.symm)
          (by native_decide)

/-- Existential form of `zmod19_card_two_candidate_indices` for callers that
prefer unpacked witnesses. -/
theorem zmod19_exists_card_two_candidate_indices
    (j : ZMod 19) (hj : j ≠ 0) :
    ∃ k l : ZMod 19,
      k ≠ 0 ∧ l ≠ 0 ∧ k ≠ j ∧ l ≠ j ∧ k ≠ l ∧
        k - j ≠ 0 ∧ l - j ≠ 0 := by
  let indices := zmod19_card_two_candidate_indices j hj
  exact
    ⟨indices.k, indices.l, indices.k_ne_zero, indices.l_ne_zero,
      indices.k_ne_j, indices.l_ne_j, indices.k_ne_l,
      indices.k_sub_j_ne_zero, indices.l_sub_j_ne_zero⟩

end Moore57
