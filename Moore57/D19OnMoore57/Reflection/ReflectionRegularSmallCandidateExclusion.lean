import Moore57.D19OnMoore57.Involution.InvolutionFixedDegreeParity
import Moore57.D19OnMoore57.Reflection.ReflectionCenterNeighborOrbitPermutation
import Moore57.D19OnMoore57.Reflection.ReflectionFixedCountRawCandidates
import Mathlib.Tactic

/-!
# Small regular raw reflection candidates

This file isolates what the current local reflection/orbit API proves about
the two regular raw candidates.  The candidate counts cannot yet be excluded
purely from the available local facts, but the regular degree is exact and the
two remaining cases force sharp center-neighbor orbit shapes.
-/

namespace Moore57

open Finset

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

namespace BranchOrbitABCReflectionLabeling

variable {h : D19ActsOnMoore57 V Γ}

/-- If a reflection fixes a vertex in one selected center-neighbor rotation
orbit, then the quotient-level reflection action preserves that orbit. -/
theorem reflectionCenterNeighborOrbitIndex_eq_self_of_fixed_mem
    (base : Fin 3 → V)
    (base_adj : ∀ q : Fin 3, Γ.Adj h.rotationFixedCenter (base q))
    (base_pairwise_disjoint :
      ∀ q r : Fin 3, q ≠ r →
        Disjoint (h.rotationOrbitFinset (base q))
          (h.rotationOrbitFinset (base r)))
    (base_cover :
      Γ.neighborFinset h.rotationFixedCenter = h.orbitFamilyUnion base)
    {k : ZMod 19} {q : Fin 3} {y : V}
    (hy :
      y ∈ (h.rotationOrbitFinset (base q)).filter
        fun z => h.smul (DihedralGroup.sr k) z = z) :
    reflectionCenterNeighborOrbitIndex (h := h) base base_adj base_cover k q = q := by
  rcases Finset.mem_filter.mp hy with ⟨hyOrbit, hyFixed⟩
  rcases (h.mem_rotationOrbitFinset (base q) y).mp hyOrbit with ⟨i, hi⟩
  have hyFixed' :
      h.smul (DihedralGroup.sr k) (h.rotation i (base q)) =
        h.rotation i (base q) := by
    simpa [hi] using hyFixed
  have hrefOrbit :
      h.smul (DihedralGroup.sr k) (base q) ∈
        h.rotationOrbitFinset (base q) := by
    refine (h.mem_rotationOrbitFinset (base q)
      (h.smul (DihedralGroup.sr k) (base q))).mpr ⟨i + i, ?_⟩
    calc
      h.rotation (i + i) (base q)
          = h.rotation i (h.rotation i (base q)) := by
              simpa [Equiv.Perm.mul_apply] using
                congrArg (fun σ : Equiv.Perm V => σ (base q))
                  (h.rotation_add i i)
      _ = h.rotation i
            (h.smul (DihedralGroup.sr k) (h.rotation i (base q))) := by
              rw [hyFixed']
      _ = h.rotation i
            (h.rotation (-i) (h.smul (DihedralGroup.sr k) (base q))) := by
              rw [h.reflection_smul_rotation]
      _ = h.smul (DihedralGroup.sr k) (base q) := by
              exact h.rotation_apply_neg_rotation i
                (h.smul (DihedralGroup.sr k) (base q))
  exact reflectionCenterNeighborOrbitIndex_eq_of_mem
    (h := h) base base_adj base_pairwise_disjoint base_cover hrefOrbit

end BranchOrbitABCReflectionLabeling

namespace D19ActsOnMoore57

variable {h : D19ActsOnMoore57 V Γ}

/-- The reflection-fixed center as a vertex of the reflection fixed set. -/
def reflectionRotationFixedCenter (h : D19ActsOnMoore57 V Γ) (k : ZMod 19) :
    fixedVertexSet (h.smulEquiv (DihedralGroup.sr k)) :=
  ⟨h.rotationFixedCenter, by
    change h.smul (DihedralGroup.sr k) h.rotationFixedCenter =
      h.rotationFixedCenter
    exact h.reflection_smul_rotationFixedCenter k⟩

/-- In a three-orbit decomposition of the neighbors of `rotationFixedCenter`,
the fixed-neighbor count is the sum of the three orbit-local fixed counts. -/
theorem reflection_fixed_center_neighbors_card_eq_sum_orbit_fixed_cards_of_decomposition
    (h : D19ActsOnMoore57 V Γ)
    (base : Fin 3 → V)
    (base_pairwise_disjoint :
      ∀ q r : Fin 3, q ≠ r →
        Disjoint (h.rotationOrbitFinset (base q))
          (h.rotationOrbitFinset (base r)))
    (base_cover :
      Γ.neighborFinset h.rotationFixedCenter = h.orbitFamilyUnion base)
    (k : ZMod 19) :
    ((Γ.neighborFinset h.rotationFixedCenter).filter
        fun y => h.smul (DihedralGroup.sr k) y = y).card =
      ∑ q : Fin 3,
        ((h.rotationOrbitFinset (base q)).filter
          fun y => h.smul (DihedralGroup.sr k) y = y).card := by
  classical
  let p : V → Prop := fun y => h.smul (DihedralGroup.sr k) y = y
  have hfilter :
      (h.orbitFamilyUnion base).filter p =
        (Finset.univ : Finset (Fin 3)).biUnion
          fun q => (h.rotationOrbitFinset (base q)).filter p := by
    ext y
    simp [D19ActsOnMoore57.orbitFamilyUnion, p]
  have hdisj :
      ∀ q ∈ (Finset.univ : Finset (Fin 3)), ∀ r ∈ (Finset.univ : Finset (Fin 3)),
        q ≠ r →
          Disjoint ((h.rotationOrbitFinset (base q)).filter p)
            ((h.rotationOrbitFinset (base r)).filter p) := by
    intro q _hq r _hr hqr
    exact (base_pairwise_disjoint q r hqr).mono
      (by intro y hy; exact (Finset.mem_filter.mp hy).1)
      (by intro y hy; exact (Finset.mem_filter.mp hy).1)
  calc
    ((Γ.neighborFinset h.rotationFixedCenter).filter
        fun y => h.smul (DihedralGroup.sr k) y = y).card
        = ((h.orbitFamilyUnion base).filter p).card := by
            simp [base_cover, p]
    _ = ((Finset.univ : Finset (Fin 3)).biUnion
          fun q => (h.rotationOrbitFinset (base q)).filter p).card := by
            rw [hfilter]
    _ = ∑ q ∈ (Finset.univ : Finset (Fin 3)),
          ((h.rotationOrbitFinset (base q)).filter p).card := by
            exact Finset.card_biUnion hdisj
    _ = ∑ q : Fin 3,
          ((h.rotationOrbitFinset (base q)).filter
            fun y => h.smul (DihedralGroup.sr k) y = y).card := by
            simp [p]

/-- Exact regular-branch candidates: the constant fixed-induced degree is
`1` or `3`, and the corresponding fixed count is `2` or `10`. -/
theorem reflection_regular_degree_fixedVertexCount_candidates
    (k : ZMod 19) (d : ℕ)
    (hreg :
      ∀ x : fixedVertexSet (h.smulEquiv (DihedralGroup.sr k)),
        (h.fixedInducedGraph (DihedralGroup.sr k)).degree x = d) :
    (d = 1 ∨ d = 3) ∧
      (fixedVertexCount (h.smulEquiv (DihedralGroup.sr k)) = 2 ∨
        fixedVertexCount (h.smulEquiv (DihedralGroup.sr k)) = 10) := by
  let c := reflectionRotationFixedCenter h k
  have hcenter : (h.fixedInducedGraph (DihedralGroup.sr k)).degree c = d :=
    hreg c
  have hdle : d ≤ 3 := by
    have hle :
        (h.fixedInducedGraph (DihedralGroup.sr k)).degree c ≤ 3 := by
      simpa [c, reflectionRotationFixedCenter] using
        h.fixedInducedGraph_reflection_rotationFixedCenter_degree_le_three k
    rw [hcenter] at hle
    exact hle
  have hodd : Odd d := by
    have hodd_center := h.fixedInducedGraph_reflection_degree_odd k c
    simpa [hcenter] using hodd_center
  have hd : d = 1 ∨ d = 3 := by
    interval_cases d
    · rcases hodd with ⟨m, hm⟩
      omega
    · exact Or.inl rfl
    · rcases hodd with ⟨m, hm⟩
      omega
    · exact Or.inr rfl
  exact ⟨hd, h.fixedVertexCount_reflection_regular_candidates k ⟨d, hreg⟩⟩

/-- Existential form of the exact regular degree candidate theorem. -/
theorem reflection_regular_degree_candidates
    (k : ZMod 19)
    (hregular :
      ∃ d : ℕ,
        ∀ x : fixedVertexSet (h.smulEquiv (DihedralGroup.sr k)),
          (h.fixedInducedGraph (DihedralGroup.sr k)).degree x = d) :
    ∃ d : ℕ,
      (∀ x : fixedVertexSet (h.smulEquiv (DihedralGroup.sr k)),
        (h.fixedInducedGraph (DihedralGroup.sr k)).degree x = d) ∧
      (d = 1 ∨ d = 3) := by
  rcases hregular with ⟨d, hreg⟩
  exact ⟨d, hreg, (h.reflection_regular_degree_fixedVertexCount_candidates k d hreg).1⟩

/-- If the regular candidate has two fixed vertices, then the fixed induced
graph has the forced `K₂` center shape, and the reflection must both preserve
one center-neighbor rotation orbit and move one. -/
theorem reflection_regular_fixedVertexCount_eq_two_K2_consequences
    (k : ZMod 19)
    (hregular :
      ∃ d : ℕ,
        ∀ x : fixedVertexSet (h.smulEquiv (DihedralGroup.sr k)),
          (h.fixedInducedGraph (DihedralGroup.sr k)).degree x = d)
    (hcount : fixedVertexCount (h.smulEquiv (DihedralGroup.sr k)) = 2) :
    (h.fixedInducedGraph (DihedralGroup.sr k)).degree
        (reflectionRotationFixedCenter h k) = 1 ∧
      (reflectionFixedNeighborFinset h k h.rotationFixedCenter).card = 1 ∧
      ∃ (base : Fin 3 → V),
      ∃ (base_adj : ∀ q : Fin 3, Γ.Adj h.rotationFixedCenter (base q)),
      ∃ (_base_pairwise_disjoint :
        ∀ q r : Fin 3, q ≠ r →
          Disjoint (h.rotationOrbitFinset (base q))
            (h.rotationOrbitFinset (base r))),
      ∃ (base_cover :
        Γ.neighborFinset h.rotationFixedCenter = h.orbitFamilyUnion base),
        (∃ q : Fin 3,
          ((h.rotationOrbitFinset (base q)).filter
            fun z => h.smul (DihedralGroup.sr k) z = z).card = 1) ∧
        (∃ b : Fin 3,
          BranchOrbitABCReflectionLabeling.reflectionCenterNeighborOrbitIndex
            (h := h) base base_adj base_cover
            k b ≠ b) := by
  classical
  rcases hregular with ⟨d, hreg⟩
  have hcount_degree :
      fixedVertexCount (h.smulEquiv (DihedralGroup.sr k)) = d * d + 1 :=
    h.reflection_regular_fixedVertexCount_eq_degree_sq_add_one k d hreg
  have hd : d = 1 := by
    rw [hcount] at hcount_degree
    nlinarith
  have hcenter_degree :
      (h.fixedInducedGraph (DihedralGroup.sr k)).degree
        (reflectionRotationFixedCenter h k) = 1 := by
    simpa [hd] using hreg (reflectionRotationFixedCenter h k)
  have hcenter_neighbors :
      (reflectionFixedNeighborFinset h k h.rotationFixedCenter).card = 1 := by
    have hdegree :=
      h.fixedInducedGraph_degree_eq_fixedNeighborFinset_card
        (DihedralGroup.sr k) (reflectionRotationFixedCenter h k)
    simpa [reflectionFixedNeighborFinset, reflectionRotationFixedCenter] using
      hdegree.symm.trans hcenter_degree
  rcases h.exists_three_rotation_orbits_on_rotationFixedCenter_neighbors with
    ⟨base, base_adj, _base_card, base_pairwise_disjoint, base_cover⟩
  have hfixed_le :
      ((Γ.neighborFinset h.rotationFixedCenter).filter fun y =>
        h.smul (DihedralGroup.sr k) y = y).card ≤ 1 := by
    simpa [reflectionFixedNeighborFinset] using Nat.le_of_eq hcenter_neighbors
  rcases h.exists_reflection_fixed_center_neighbor_orbit_card_eq_one_of_decomposition
      base base_adj base_pairwise_disjoint base_cover k with
    ⟨q, hq⟩
  rcases
    BranchOrbitABCReflectionLabeling.exists_reflectionCenterNeighborOrbitIndex_ne_of_fixed_neighbors_card_le_one
      (h := h) base base_adj base_pairwise_disjoint base_cover k hfixed_le with
    ⟨b, hb⟩
  exact ⟨hcenter_degree, hcenter_neighbors, base, base_adj,
    base_pairwise_disjoint, base_cover, ⟨q, hq⟩, ⟨b, hb⟩⟩

/-- If the regular candidate has ten fixed vertices, then the fixed induced
graph has degree `3` at the rotation-fixed center, and every center-neighbor
rotation orbit is preserved by the reflection with exactly one fixed vertex in
each such orbit. -/
theorem reflection_regular_fixedVertexCount_eq_ten_center_orbits_preserved_of_decomposition
    (k : ZMod 19)
    (hregular :
      ∃ d : ℕ,
        ∀ x : fixedVertexSet (h.smulEquiv (DihedralGroup.sr k)),
          (h.fixedInducedGraph (DihedralGroup.sr k)).degree x = d)
    (hcount : fixedVertexCount (h.smulEquiv (DihedralGroup.sr k)) = 10)
    (base : Fin 3 → V)
    (base_adj : ∀ q : Fin 3, Γ.Adj h.rotationFixedCenter (base q))
    (base_pairwise_disjoint :
      ∀ q r : Fin 3, q ≠ r →
        Disjoint (h.rotationOrbitFinset (base q))
          (h.rotationOrbitFinset (base r)))
    (base_cover :
      Γ.neighborFinset h.rotationFixedCenter = h.orbitFamilyUnion base) :
    (h.fixedInducedGraph (DihedralGroup.sr k)).degree
        (reflectionRotationFixedCenter h k) = 3 ∧
      (reflectionFixedNeighborFinset h k h.rotationFixedCenter).card = 3 ∧
      (∀ q : Fin 3,
        BranchOrbitABCReflectionLabeling.reflectionCenterNeighborOrbitIndex
          (h := h) base base_adj base_cover k q = q) ∧
      (∀ q : Fin 3,
        ((h.rotationOrbitFinset (base q)).filter
          fun z => h.smul (DihedralGroup.sr k) z = z).card = 1) := by
  classical
  rcases hregular with ⟨d, hreg⟩
  have hcount_degree :
      fixedVertexCount (h.smulEquiv (DihedralGroup.sr k)) = d * d + 1 :=
    h.reflection_regular_fixedVertexCount_eq_degree_sq_add_one k d hreg
  have hd : d = 3 := by
    rw [hcount] at hcount_degree
    nlinarith
  have hcenter_degree :
      (h.fixedInducedGraph (DihedralGroup.sr k)).degree
        (reflectionRotationFixedCenter h k) = 3 := by
    simpa [hd] using hreg (reflectionRotationFixedCenter h k)
  have hcenter_neighbors :
      (reflectionFixedNeighborFinset h k h.rotationFixedCenter).card = 3 := by
    have hdegree :=
      h.fixedInducedGraph_degree_eq_fixedNeighborFinset_card
        (DihedralGroup.sr k) (reflectionRotationFixedCenter h k)
    simpa [reflectionFixedNeighborFinset, reflectionRotationFixedCenter] using
      hdegree.symm.trans hcenter_degree
  have hsum :
      (∑ q : Fin 3,
        ((h.rotationOrbitFinset (base q)).filter
          fun z => h.smul (DihedralGroup.sr k) z = z).card) = 3 := by
    have hsplit :=
      h.reflection_fixed_center_neighbors_card_eq_sum_orbit_fixed_cards_of_decomposition
        base base_pairwise_disjoint base_cover k
    simpa [reflectionFixedNeighborFinset] using hsplit.symm.trans hcenter_neighbors
  have hle :
      ∀ q : Fin 3,
        ((h.rotationOrbitFinset (base q)).filter
          fun z => h.smul (DihedralGroup.sr k) z = z).card ≤ 1 := by
    intro q
    exact h.reflection_fixed_points_in_rotationOrbitFinset_card_le_one
      (k := k) (x := base q)
      (h.rotationFixedCenter_neighbor_moved (base_adj q))
  let a : Fin 3 → ℕ := fun q =>
    ((h.rotationOrbitFinset (base q)).filter
      fun z => h.smul (DihedralGroup.sr k) z = z).card
  have hsum_a : (∑ q : Fin 3, a q) = 3 := by
    simpa [a] using hsum
  have hsum012 : a 0 + a 1 + a 2 = 3 := by
    simpa [Fin.sum_univ_three] using hsum_a
  have hle_a : ∀ q : Fin 3, a q ≤ 1 := by
    intro q
    simpa [a] using hle q
  let a0 : ℕ := a 0
  let a1 : ℕ := a 1
  let a2 : ℕ := a 2
  have hsum_a012 : a0 + a1 + a2 = 3 := by
    simpa [a0, a1, a2] using hsum012
  have h0le : a0 ≤ 1 := by simpa [a0] using hle_a 0
  have h1le : a1 ≤ 1 := by simpa [a1] using hle_a 1
  have h2le : a2 ≤ 1 := by simpa [a2] using hle_a 2
  have h0eq : a0 = 1 := by
    have h12le : a1 + a2 ≤ 2 := Nat.add_le_add h1le h2le
    omega
  have h1eq : a1 = 1 := by
    have h02le : a0 + a2 ≤ 2 := Nat.add_le_add h0le h2le
    omega
  have h2eq : a2 = 1 := by
    have h01le : a0 + a1 ≤ 2 := Nat.add_le_add h0le h1le
    omega
  have hcard_one_a : ∀ q : Fin 3, a q = 1 := by
    intro q
    fin_cases q
    · simpa [a0] using h0eq
    · simpa [a1] using h1eq
    · simpa [a2] using h2eq
  have hcard_one :
      ∀ q : Fin 3,
        ((h.rotationOrbitFinset (base q)).filter
          fun z => h.smul (DihedralGroup.sr k) z = z).card = 1 := by
    intro q
    simpa [a] using hcard_one_a q
  have hpreserved :
      ∀ q : Fin 3,
        BranchOrbitABCReflectionLabeling.reflectionCenterNeighborOrbitIndex
          (h := h) base base_adj base_cover k q = q := by
    intro q
    have hpos :
        0 < ((h.rotationOrbitFinset (base q)).filter
          fun z => h.smul (DihedralGroup.sr k) z = z).card := by
      rw [hcard_one q]
      norm_num
    rcases Finset.card_pos.mp hpos with ⟨y, hy⟩
    exact
      BranchOrbitABCReflectionLabeling.reflectionCenterNeighborOrbitIndex_eq_self_of_fixed_mem
        (h := h) base base_adj base_pairwise_disjoint base_cover hy
  exact ⟨hcenter_degree, hcenter_neighbors, hpreserved, hcard_one⟩

/-- Existential wrapper using the canonical three-orbit decomposition around
`rotationFixedCenter`. -/
theorem reflection_regular_fixedVertexCount_eq_ten_center_orbits_preserved
    (k : ZMod 19)
    (hregular :
      ∃ d : ℕ,
        ∀ x : fixedVertexSet (h.smulEquiv (DihedralGroup.sr k)),
          (h.fixedInducedGraph (DihedralGroup.sr k)).degree x = d)
    (hcount : fixedVertexCount (h.smulEquiv (DihedralGroup.sr k)) = 10) :
    ∃ (base : Fin 3 → V),
    ∃ (base_adj : ∀ q : Fin 3, Γ.Adj h.rotationFixedCenter (base q)),
    ∃ (_base_pairwise_disjoint :
      ∀ q r : Fin 3, q ≠ r →
        Disjoint (h.rotationOrbitFinset (base q))
          (h.rotationOrbitFinset (base r))),
    ∃ (base_cover :
      Γ.neighborFinset h.rotationFixedCenter = h.orbitFamilyUnion base),
      (h.fixedInducedGraph (DihedralGroup.sr k)).degree
          (reflectionRotationFixedCenter h k) = 3 ∧
      (reflectionFixedNeighborFinset h k h.rotationFixedCenter).card = 3 ∧
      (∀ q : Fin 3,
        BranchOrbitABCReflectionLabeling.reflectionCenterNeighborOrbitIndex
          (h := h) base base_adj base_cover
          k q = q) ∧
      (∀ q : Fin 3,
        ((h.rotationOrbitFinset (base q)).filter
          fun z => h.smul (DihedralGroup.sr k) z = z).card = 1) := by
  classical
  rcases h.exists_three_rotation_orbits_on_rotationFixedCenter_neighbors with
    ⟨base, base_adj, _base_card, base_pairwise_disjoint, base_cover⟩
  rcases
    h.reflection_regular_fixedVertexCount_eq_ten_center_orbits_preserved_of_decomposition
      k hregular hcount base base_adj base_pairwise_disjoint base_cover with
    ⟨hdegree, hneighbors, hpreserved, hcards⟩
  exact ⟨base, base_adj, base_pairwise_disjoint, base_cover,
    hdegree, hneighbors, hpreserved, hcards⟩

end D19ActsOnMoore57

end

end Moore57
