import Moore57.ReflectionCenterNeighborOrbitPermutation

/-!
# Raw reflection degree bounds at the rotation-fixed center

This file proves the orbit-local fixed-point bound for a reflection on a moved
rotation orbit, then applies the three-orbit decomposition of the neighbors of
`rotationFixedCenter` to bound the corresponding fixed-induced degree by `3`.
-/

namespace Moore57

open Finset

noncomputable section

namespace D19ActsOnMoore57

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- On a moved rotation orbit, a reflection has at most one fixed point. -/
theorem reflection_fixed_points_in_rotationOrbitFinset_card_le_one
    (h : D19ActsOnMoore57 V Γ) {k : ZMod 19} {x : V}
    (hmove : h.rotation 1 x ≠ x) :
    ((h.rotationOrbitFinset x).filter
      fun z => h.smul (DihedralGroup.sr k) z = z).card ≤ 1 := by
  classical
  rw [Finset.card_le_one_iff]
  intro a b ha hb
  rcases Finset.mem_filter.mp ha with ⟨haOrbit, haFixed⟩
  rcases Finset.mem_filter.mp hb with ⟨hbOrbit, hbFixed⟩
  rcases (h.mem_rotationOrbitFinset x a).mp haOrbit with ⟨i, hi⟩
  rcases (h.mem_rotationOrbitFinset x b).mp hbOrbit with ⟨j, hj⟩
  have hinj :
      Function.Injective (fun n : ZMod 19 => h.rotation n x) :=
    h.rotationOrbitW_injective_of_nonzero_moved (d := 1) (by decide) hmove
  have haFixed' :
      h.smul (DihedralGroup.sr k) (h.rotation i x) =
        h.rotation i x := by
    simpa [hi] using haFixed
  have hbFixed' :
      h.smul (DihedralGroup.sr k) (h.rotation j x) =
        h.rotation j x := by
    simpa [hj] using hbFixed
  have haCoord :
      h.smul (DihedralGroup.sr k) x =
        h.rotation (i + i) x := by
    calc
      h.smul (DihedralGroup.sr k) x
          = h.rotation i
              (h.rotation (-i) (h.smul (DihedralGroup.sr k) x)) := by
              exact (h.rotation_apply_neg_rotation i
                (h.smul (DihedralGroup.sr k) x)).symm
      _ = h.rotation i
              (h.smul (DihedralGroup.sr k) (h.rotation i x)) := by
              rw [← h.reflection_smul_rotation k i x]
      _ = h.rotation i (h.rotation i x) := by
              rw [haFixed']
      _ = h.rotation (i + i) x := by
              simpa [Equiv.Perm.mul_apply] using
                congrArg (fun σ : Equiv.Perm V => σ x)
                  (h.rotation_add i i).symm
  have hbCoord :
      h.smul (DihedralGroup.sr k) x =
        h.rotation (j + j) x := by
    calc
      h.smul (DihedralGroup.sr k) x
          = h.rotation j
              (h.rotation (-j) (h.smul (DihedralGroup.sr k) x)) := by
              exact (h.rotation_apply_neg_rotation j
                (h.smul (DihedralGroup.sr k) x)).symm
      _ = h.rotation j
              (h.smul (DihedralGroup.sr k) (h.rotation j x)) := by
              rw [← h.reflection_smul_rotation k j x]
      _ = h.rotation j (h.rotation j x) := by
              rw [hbFixed']
      _ = h.rotation (j + j) x := by
              simpa [Equiv.Perm.mul_apply] using
                congrArg (fun σ : Equiv.Perm V => σ x)
                  (h.rotation_add j j).symm
  have hij2 : i + i = j + j :=
    hinj (haCoord.symm.trans hbCoord)
  have htwo : (2 : ZMod 19) * i = (2 : ZMod 19) * j := by
    simpa [two_mul] using hij2
  have hij : i = j := by
    calc
      i = (2 : ZMod 19)⁻¹ * ((2 : ZMod 19) * i) := by
            rw [← mul_assoc, inv_mul_cancel₀ two_ne_zero_zmod19, one_mul]
      _ = (2 : ZMod 19)⁻¹ * ((2 : ZMod 19) * j) := by
            rw [htwo]
      _ = j := by
            rw [← mul_assoc, inv_mul_cancel₀ two_ne_zero_zmod19, one_mul]
  rw [← hi, ← hj, hij]

/-- For a three-orbit decomposition of the neighbors of `rotationFixedCenter`,
the reflection-fixed neighbors of `rotationFixedCenter` have cardinality at
most `3`. -/
theorem reflection_fixed_neighbors_rotationFixedCenter_card_le_three_of_decomposition
    (h : D19ActsOnMoore57 V Γ)
    (base : Fin 3 → V)
    (base_adj : ∀ q : Fin 3, Γ.Adj h.rotationFixedCenter (base q))
    (base_cover :
      Γ.neighborFinset h.rotationFixedCenter = h.orbitFamilyUnion base)
    (k : ZMod 19) :
    ((Γ.neighborFinset h.rotationFixedCenter).filter
      fun z => h.smul (DihedralGroup.sr k) z = z).card ≤ 3 := by
  classical
  have hsubset :
      ((Γ.neighborFinset h.rotationFixedCenter).filter
        fun z => h.smul (DihedralGroup.sr k) z = z) ⊆
        (Finset.univ : Finset (Fin 3)).biUnion
          fun q => (h.rotationOrbitFinset (base q)).filter
            fun z => h.smul (DihedralGroup.sr k) z = z := by
    intro z hz
    rcases Finset.mem_filter.mp hz with ⟨hzNeighbor, hzFixed⟩
    have hzUnion : z ∈ h.orbitFamilyUnion base := by
      simpa [base_cover] using hzNeighbor
    rcases (h.mem_orbitFamilyUnion base z).mp hzUnion with ⟨q, i, hi⟩
    refine Finset.mem_biUnion.mpr ⟨q, Finset.mem_univ q, ?_⟩
    exact Finset.mem_filter.mpr
      ⟨(h.mem_rotationOrbitFinset (base q) z).mpr ⟨i, hi⟩, hzFixed⟩
  calc
    ((Γ.neighborFinset h.rotationFixedCenter).filter
      fun z => h.smul (DihedralGroup.sr k) z = z).card
        ≤ ((Finset.univ : Finset (Fin 3)).biUnion
            fun q => (h.rotationOrbitFinset (base q)).filter
              fun z => h.smul (DihedralGroup.sr k) z = z).card :=
        Finset.card_le_card hsubset
    _ ≤ (∑ q ∈ (Finset.univ : Finset (Fin 3)),
          ((h.rotationOrbitFinset (base q)).filter
            fun z => h.smul (DihedralGroup.sr k) z = z).card) :=
        Finset.card_biUnion_le
    _ ≤ (∑ _q ∈ (Finset.univ : Finset (Fin 3)), 1) := by
        exact Finset.sum_le_sum (by
          intro q _hq
          exact h.reflection_fixed_points_in_rotationOrbitFinset_card_le_one
            (k := k) (x := base q)
            (h.rotationFixedCenter_neighbor_moved (base_adj q)))
    _ = 3 := by
        simp

/-- The reflection-fixed neighbors of `rotationFixedCenter` have cardinality at
most `3`. -/
theorem reflection_fixed_neighbors_rotationFixedCenter_card_le_three
    (h : D19ActsOnMoore57 V Γ) (k : ZMod 19) :
    ((Γ.neighborFinset h.rotationFixedCenter).filter
      fun z => h.smul (DihedralGroup.sr k) z = z).card ≤ 3 := by
  rcases h.exists_three_rotation_orbits_on_rotationFixedCenter_neighbors with
    ⟨base, base_adj, _base_card, _base_pairwise_disjoint, base_cover⟩
  exact h.reflection_fixed_neighbors_rotationFixedCenter_card_le_three_of_decomposition
    base base_adj base_cover k

/-- Public degree form: the reflection fixed-induced graph has degree at most
`3` at `rotationFixedCenter`. -/
theorem fixedInducedGraph_reflection_rotationFixedCenter_degree_le_three
    (h : D19ActsOnMoore57 V Γ) (k : ZMod 19) :
    (h.fixedInducedGraph (DihedralGroup.sr k)).degree
      ⟨h.rotationFixedCenter, by
        change h.smul (DihedralGroup.sr k) h.rotationFixedCenter =
          h.rotationFixedCenter
        exact h.reflection_smul_rotationFixedCenter k⟩ ≤ 3 := by
  let x : fixedVertexSet (h.smulEquiv (DihedralGroup.sr k)) :=
    ⟨h.rotationFixedCenter, by
      change h.smul (DihedralGroup.sr k) h.rotationFixedCenter =
        h.rotationFixedCenter
      exact h.reflection_smul_rotationFixedCenter k⟩
  have hdeg_eq :
      (h.fixedInducedGraph (DihedralGroup.sr k)).degree x =
        ((Γ.neighborFinset h.rotationFixedCenter).filter
          fun z => h.smul (DihedralGroup.sr k) z = z).card := by
    simpa [x, D19ActsOnMoore57.smulEquiv] using
      h.fixedInducedGraph_degree_eq_fixedNeighborFinset_card
        (DihedralGroup.sr k) x
  simpa [x] using
    hdeg_eq.trans_le
      (h.reflection_fixed_neighbors_rotationFixedCenter_card_le_three k)

end D19ActsOnMoore57

end

end Moore57
