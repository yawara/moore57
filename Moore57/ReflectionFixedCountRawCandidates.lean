import Moore57.ReflectionFixedCenterDegreeBounds
import Moore57.ReflectionFixedCountStarCandidates
import Moore57.ReflectionRegularBranchRaw
import Mathlib.Tactic

/-!
# Raw reflection fixed-count candidates

This file combines the raw regular-branch arithmetic, the fixed-center degree
bound, and the star-branch arithmetic.  It does not prove the final
`56`-vertex fixed star; it reduces the raw reflection count to a finite list
without using `D19LinearCharacterInput`.
-/

namespace Moore57

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

namespace D19ActsOnMoore57

variable {h : D19ActsOnMoore57 V Γ}

/-- A reflection fixes an even number of vertices. -/
theorem two_dvd_reflection_fixedVertexCount (k : ZMod 19) :
    2 ∣ fixedVertexCount (h.smulEquiv (DihedralGroup.sr k)) := by
  have hsupport_even :
      2 ∣
        Fintype.card V -
          fixedVertexCount (h.smulEquiv (DihedralGroup.sr k)) :=
    two_dvd_card_sub_fixedVertexCount_of_involutive
      (h.smulEquiv (DihedralGroup.sr k))
      (h.reflection_smulEquiv_involutive k)
  obtain ⟨q, hq⟩ := hsupport_even
  refine ⟨1625 - q, ?_⟩
  have hcard : Fintype.card V = 3250 := h.isMoore.card
  have hfixed_le :
      fixedVertexCount (h.smulEquiv (DihedralGroup.sr k)) ≤ 3250 := by
    have hle :
        (fixedFinset (h.smulEquiv (DihedralGroup.sr k))).card ≤
          Fintype.card V :=
      Finset.card_le_univ _
    simpa [fixedFinset_card, hcard] using hle
  rw [hcard] at hq
  omega

/-- If the fixed-induced graph of a reflection is regular, then the raw
fixed-center degree bound leaves only fixed counts `2` and `10`. -/
theorem fixedVertexCount_reflection_regular_candidates
    (k : ZMod 19)
    (hregular :
      ∃ d : ℕ,
        ∀ x : fixedVertexSet (h.smulEquiv (DihedralGroup.sr k)),
          (h.fixedInducedGraph (DihedralGroup.sr k)).degree x = d) :
    fixedVertexCount (h.smulEquiv (DihedralGroup.sr k)) = 2 ∨
      fixedVertexCount (h.smulEquiv (DihedralGroup.sr k)) = 10 := by
  rcases hregular with ⟨d, hreg⟩
  let c : fixedVertexSet (h.smulEquiv (DihedralGroup.sr k)) :=
    ⟨h.rotationFixedCenter, by
      change h.smul (DihedralGroup.sr k) h.rotationFixedCenter =
        h.rotationFixedCenter
      exact h.reflection_smul_rotationFixedCenter k⟩
  have hdle : d ≤ 3 := by
    have hcenter := hreg c
    have hle := h.fixedInducedGraph_reflection_rotationFixedCenter_degree_le_three k
    rw [hcenter] at hle
    exact hle
  have hn :
      fixedVertexCount (h.smulEquiv (DihedralGroup.sr k)) = d * d + 1 :=
    h.reflection_regular_fixedVertexCount_eq_degree_sq_add_one k d hreg
  have heven : 2 ∣ fixedVertexCount (h.smulEquiv (DihedralGroup.sr k)) :=
    h.two_dvd_reflection_fixedVertexCount k
  interval_cases d
  · rw [hn] at heven
    norm_num at heven
  · left
    simpa using hn
  · rw [hn] at heven
    norm_num at heven
  · right
    simpa using hn

/-- Raw reflection fixed-count candidate reduction.  The regular branch gives
`2` or `10`; the non-regular strong `(0,1)` branch is a star and gives
`6, 16, 26, 36, 46, 56`. -/
theorem fixedVertexCount_reflection_raw_candidates
    (k : ZMod 19) :
    fixedVertexCount (h.smulEquiv (DihedralGroup.sr k)) = 2 ∨
    fixedVertexCount (h.smulEquiv (DihedralGroup.sr k)) = 6 ∨
    fixedVertexCount (h.smulEquiv (DihedralGroup.sr k)) = 10 ∨
    fixedVertexCount (h.smulEquiv (DihedralGroup.sr k)) = 16 ∨
    fixedVertexCount (h.smulEquiv (DihedralGroup.sr k)) = 26 ∨
    fixedVertexCount (h.smulEquiv (DihedralGroup.sr k)) = 36 ∨
    fixedVertexCount (h.smulEquiv (DihedralGroup.sr k)) = 46 ∨
    fixedVertexCount (h.smulEquiv (DihedralGroup.sr k)) = 56 := by
  by_cases hregular :
      ∃ d : ℕ,
        ∀ x : fixedVertexSet (h.smulEquiv (DihedralGroup.sr k)),
          (h.fixedInducedGraph (DihedralGroup.sr k)).degree x = d
  · rcases h.fixedVertexCount_reflection_regular_candidates k hregular with h2 | h10
    · exact Or.inl h2
    · exact Or.inr (Or.inr (Or.inl h10))
  · have hstrong := h.fixedInducedGraph_isStrongZeroOne (DihedralGroup.sr k)
    rcases hstrong.exists_isStarWithCenter_of_not_regular hregular with
      ⟨c, hstar⟩
    rcases h.fixedVertexCount_reflection_star_candidates_of_fixedInduced_isStarWithCenter
        k hstar with h6 | h16 | h26 | h36 | h46 | h56
    · exact Or.inr (Or.inl h6)
    · exact Or.inr (Or.inr (Or.inr (Or.inl h16)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h26))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h36)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h46))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h56))))))

end D19ActsOnMoore57

end

end Moore57
