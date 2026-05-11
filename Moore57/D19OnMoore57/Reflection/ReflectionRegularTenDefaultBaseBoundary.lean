import Moore57.D19OnMoore57.Reflection.ReflectionRemainingCandidateGeometryBoundary

/-!
# Default-base consequences of regular-ten preserved reflection orbits

This file specializes the regular-`10` all-center-neighbor-orbits-preserved
boundary to the default `remainingCenterNeighborOrbitBase`.
-/

namespace Moore57

open Finset

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

namespace D19ActsOnMoore57

variable {h : D19ActsOnMoore57 V Γ}

/-- If the reflection fixes exactly three neighbors of `rotationFixedCenter`,
then in any three-orbit center-neighbor decomposition each orbit-local fixed
point finset has cardinality `1`. -/
theorem reflection_orbit_fixed_card_eq_one_of_fixed_neighbors_card_eq_three
    (base : Fin 3 → V)
    (base_adj : ∀ q : Fin 3, Γ.Adj h.rotationFixedCenter (base q))
    (base_pairwise_disjoint :
      ∀ q r : Fin 3, q ≠ r →
        Disjoint (h.rotationOrbitFinset (base q))
          (h.rotationOrbitFinset (base r)))
    (base_cover :
      Γ.neighborFinset h.rotationFixedCenter = h.orbitFamilyUnion base)
    (k : ZMod 19)
    (hcenter_neighbors :
      (reflectionFixedNeighborFinset h k h.rotationFixedCenter).card = 3) :
    ∀ q : Fin 3,
      ((h.rotationOrbitFinset (base q)).filter fun z =>
        h.smul (DihedralGroup.sr k) z = z).card = 1 := by
  classical
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
  intro q
  fin_cases q
  · simpa [a0, a] using h0eq
  · simpa [a1, a] using h1eq
  · simpa [a2, a] using h2eq

end D19ActsOnMoore57

namespace ReflectionRegularTenAllCenterNeighborOrbitsPreserved

variable {h : D19ActsOnMoore57 V Γ} {k : ZMod 19}

/-- The regular-`10` preserved-orbits boundary fixes the neighbor count at
`rotationFixedCenter` to be `3`. -/
theorem fixed_neighbors_rotationFixedCenter_card_eq_three
    (regularTen : ReflectionRegularTenAllCenterNeighborOrbitsPreserved h k) :
    (reflectionFixedNeighborFinset h k h.rotationFixedCenter).card = 3 := by
  rcases regularTen with
    ⟨_hcount, _base, _base_adj, _base_pairwise_disjoint, _base_cover,
      _hdegree, hneighbors, _hpreserved, _hcards⟩
  exact hneighbors

/-- Filtered-neighbor form of
`fixed_neighbors_rotationFixedCenter_card_eq_three`. -/
theorem filtered_neighbors_rotationFixedCenter_card_eq_three
    (regularTen : ReflectionRegularTenAllCenterNeighborOrbitsPreserved h k) :
    ((Γ.neighborFinset h.rotationFixedCenter).filter fun z =>
      h.smul (DihedralGroup.sr k) z = z).card = 3 := by
  simpa [reflectionFixedNeighborFinset] using
    regularTen.fixed_neighbors_rotationFixedCenter_card_eq_three

/-- Default-base orbit-local fixed-point finsets each have cardinality `1`. -/
theorem remainingCenterNeighborOrbitBase_orbit_fixed_card_eq_one
    (regularTen : ReflectionRegularTenAllCenterNeighborOrbitsPreserved h k) :
    ∀ q : Fin 3,
      ((h.rotationOrbitFinset (remainingCenterNeighborOrbitBase h q)).filter fun z =>
        h.smul (DihedralGroup.sr k) z = z).card = 1 :=
  h.reflection_orbit_fixed_card_eq_one_of_fixed_neighbors_card_eq_three
    (remainingCenterNeighborOrbitBase h)
    (remainingCenterNeighborOrbitBase_adj (h := h))
    (remainingCenterNeighborOrbitBase_pairwise_disjoint (h := h))
    (remainingCenterNeighborOrbitBase_cover (h := h))
    k regularTen.fixed_neighbors_rotationFixedCenter_card_eq_three

/-- On the default base, the quotient-level reflection action preserves each
center-neighbor orbit. -/
theorem remainingCenterNeighborOrbitBase_reflectionCenterNeighborOrbitIndex_eq_self
    (regularTen : ReflectionRegularTenAllCenterNeighborOrbitsPreserved h k) :
    ∀ q : Fin 3,
      BranchOrbitABCReflectionLabeling.reflectionCenterNeighborOrbitIndex
        (h := h)
        (remainingCenterNeighborOrbitBase h)
        (remainingCenterNeighborOrbitBase_adj (h := h))
        (remainingCenterNeighborOrbitBase_cover (h := h))
        k q = q := by
  classical
  intro q
  have hcard :=
    regularTen.remainingCenterNeighborOrbitBase_orbit_fixed_card_eq_one q
  have hpos :
      0 < ((h.rotationOrbitFinset (remainingCenterNeighborOrbitBase h q)).filter fun z =>
        h.smul (DihedralGroup.sr k) z = z).card := by
    rw [hcard]
    norm_num
  rcases Finset.card_pos.mp hpos with ⟨y, hy⟩
  exact
    BranchOrbitABCReflectionLabeling.reflectionCenterNeighborOrbitIndex_eq_self_of_fixed_mem
      (h := h)
      (remainingCenterNeighborOrbitBase h)
      (remainingCenterNeighborOrbitBase_adj (h := h))
      (remainingCenterNeighborOrbitBase_pairwise_disjoint (h := h))
      (remainingCenterNeighborOrbitBase_cover (h := h))
      hy

/-- The default base has no moved reflected center-neighbor orbit index in the
regular-`10` preserved-orbits boundary. -/
theorem not_exists_remainingCenterNeighborOrbitBase_reflectionCenterNeighborOrbitIndex_ne
    (regularTen : ReflectionRegularTenAllCenterNeighborOrbitsPreserved h k) :
    ¬ ∃ b : Fin 3,
      BranchOrbitABCReflectionLabeling.reflectionCenterNeighborOrbitIndex
        (h := h)
        (remainingCenterNeighborOrbitBase h)
        (remainingCenterNeighborOrbitBase_adj (h := h))
        (remainingCenterNeighborOrbitBase_cover (h := h))
        k b ≠ b := by
  rintro ⟨b, hb⟩
  exact hb
    (regularTen.remainingCenterNeighborOrbitBase_reflectionCenterNeighborOrbitIndex_eq_self b)

end ReflectionRegularTenAllCenterNeighborOrbitsPreserved

end

end Moore57
