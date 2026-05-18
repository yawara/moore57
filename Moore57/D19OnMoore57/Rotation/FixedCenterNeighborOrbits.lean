import Moore57.D19OnMoore57.Rotation.FixedCenterNeighbors
import Moore57.D19OnMoore57.Orbit.FamilyPartition
import Moore57.D19OnMoore57.Rotation.OrbitFinsetBasic

/-!
# Rotation orbits on the neighbors of the fixed center

The 57 neighbors of the unique rotation-fixed center split into three
rotation orbits.  Each selected orbit has size `19`, the selected orbits are
pairwise disjoint, and their union is the whole neighbor finset.
-/

namespace Moore57

namespace D19ActsOnMoore57

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- The fixed rotation center has exactly `57` neighbors. -/
theorem neighborFinset_rotationFixedCenter_card
    (h : D19ActsOnMoore57 V Γ) :
    (Γ.neighborFinset h.rotationFixedCenter).card = 57 := by
  rw [SimpleGraph.card_neighborFinset_eq_degree, h.isMoore.regular.degree_eq]

set_option linter.flexible false in
/-- The `57` neighbors of `h.rotationFixedCenter` are covered by three
pairwise-disjoint rotation orbits of size `19`. -/
theorem exists_three_rotationOrbitFinset_neighbors_rotationFixedCenter
    (h : D19ActsOnMoore57 V Γ) :
    ∃ base : Fin 3 → V,
      (∀ q : Fin 3, Γ.Adj h.rotationFixedCenter (base q)) ∧
      (∀ q : Fin 3, (h.rotationOrbitFinset (base q)).card = 19) ∧
      (∀ q r : Fin 3, q ≠ r →
        Disjoint (h.rotationOrbitFinset (base q))
          (h.rotationOrbitFinset (base r))) ∧
      Γ.neighborFinset h.rotationFixedCenter = h.orbitFamilyUnion base := by
  classical
  let S : Finset V := Γ.neighborFinset h.rotationFixedCenter
  have hS_card : S.card = 57 := by
    simpa [S] using h.neighborFinset_rotationFixedCenter_card
  have hS_pos : 0 < S.card := by
    rw [hS_card]
    norm_num
  rcases Finset.card_pos.mp hS_pos with ⟨b0, hb0S⟩
  have hb0Adj : Γ.Adj h.rotationFixedCenter b0 := by
    simpa [S, SimpleGraph.mem_neighborFinset] using hb0S
  have hO0_subset :
      h.rotationOrbitFinset b0 ⊆ S := by
    simpa [S] using
      h.rotationOrbitFinset_subset_neighborFinset_rotationFixedCenter hb0Adj
  have hO0_card : (h.rotationOrbitFinset b0).card = 19 :=
    h.rotationOrbitFinset_card_neighbor_rotationFixedCenter hb0Adj
  have hS_minus_O0_card : (S \ h.rotationOrbitFinset b0).card = 38 := by
    rw [Finset.card_sdiff_of_subset hO0_subset]
    omega
  have hS_minus_O0_pos : 0 < (S \ h.rotationOrbitFinset b0).card := by
    rw [hS_minus_O0_card]
    norm_num
  rcases Finset.card_pos.mp hS_minus_O0_pos with ⟨b1, hb1Rem⟩
  have hb1S : b1 ∈ S := (Finset.mem_sdiff.mp hb1Rem).1
  have hb1_not_O0 : b1 ∉ h.rotationOrbitFinset b0 :=
    (Finset.mem_sdiff.mp hb1Rem).2
  have hb1Adj : Γ.Adj h.rotationFixedCenter b1 := by
    simpa [S, SimpleGraph.mem_neighborFinset] using hb1S
  have hO1_subset :
      h.rotationOrbitFinset b1 ⊆ S := by
    simpa [S] using
      h.rotationOrbitFinset_subset_neighborFinset_rotationFixedCenter hb1Adj
  have hO1_card : (h.rotationOrbitFinset b1).card = 19 :=
    h.rotationOrbitFinset_card_neighbor_rotationFixedCenter hb1Adj
  have hO0O1_disjoint :
      Disjoint (h.rotationOrbitFinset b0) (h.rotationOrbitFinset b1) :=
    h.disjoint_rotationOrbitFinset_of_not_mem hb1_not_O0
  let U01 : Finset V := h.rotationOrbitFinset b0 ∪ h.rotationOrbitFinset b1
  have hU01_subset : U01 ⊆ S := by
    intro y hy
    rcases Finset.mem_union.mp hy with hy0 | hy1
    · exact hO0_subset hy0
    · exact hO1_subset hy1
  have hU01_card : U01.card = 38 := by
    dsimp [U01]
    rw [Finset.card_union_of_disjoint hO0O1_disjoint]
    omega
  have hS_minus_U01_card : (S \ U01).card = 19 := by
    rw [Finset.card_sdiff_of_subset hU01_subset]
    omega
  have hS_minus_U01_pos : 0 < (S \ U01).card := by
    rw [hS_minus_U01_card]
    norm_num
  rcases Finset.card_pos.mp hS_minus_U01_pos with ⟨b2, hb2Rem⟩
  have hb2S : b2 ∈ S := (Finset.mem_sdiff.mp hb2Rem).1
  have hb2_not_U01 : b2 ∉ U01 := (Finset.mem_sdiff.mp hb2Rem).2
  have hb2_not_O0 : b2 ∉ h.rotationOrbitFinset b0 := by
    intro hb2O0
    exact hb2_not_U01 (Finset.mem_union.mpr (Or.inl hb2O0))
  have hb2_not_O1 : b2 ∉ h.rotationOrbitFinset b1 := by
    intro hb2O1
    exact hb2_not_U01 (Finset.mem_union.mpr (Or.inr hb2O1))
  have hb2Adj : Γ.Adj h.rotationFixedCenter b2 := by
    simpa [S, SimpleGraph.mem_neighborFinset] using hb2S
  have hO2_card : (h.rotationOrbitFinset b2).card = 19 :=
    h.rotationOrbitFinset_card_neighbor_rotationFixedCenter hb2Adj
  have hO0O2_disjoint :
      Disjoint (h.rotationOrbitFinset b0) (h.rotationOrbitFinset b2) :=
    h.disjoint_rotationOrbitFinset_of_not_mem hb2_not_O0
  have hO1O2_disjoint :
      Disjoint (h.rotationOrbitFinset b1) (h.rotationOrbitFinset b2) :=
    h.disjoint_rotationOrbitFinset_of_not_mem hb2_not_O1
  let base : Fin 3 → V := fun q =>
    if q = 0 then b0 else if q = 1 then b1 else b2
  have hbase_adj : ∀ q : Fin 3, Γ.Adj h.rotationFixedCenter (base q) := by
    intro q
    fin_cases q <;> simp [base, hb0Adj, hb1Adj, hb2Adj]
  have hbase_card :
      ∀ q : Fin 3, (h.rotationOrbitFinset (base q)).card = 19 := by
    intro q
    fin_cases q <;> simp [base, hO0_card, hO1_card, hO2_card]
  have hbase_disjoint :
      ∀ q r : Fin 3, q ≠ r →
        Disjoint (h.rotationOrbitFinset (base q))
          (h.rotationOrbitFinset (base r)) := by
    intro q r hqr
    fin_cases q <;> fin_cases r <;>
      simp [base] at hqr ⊢
    · exact hO0O1_disjoint
    · exact hO0O2_disjoint
    · exact hO0O1_disjoint.symm
    · exact hO1O2_disjoint
    · exact hO0O2_disjoint.symm
    · exact hO1O2_disjoint.symm
  have hUnion_subset : h.orbitFamilyUnion base ⊆ S := by
    intro y hy
    rcases (h.mem_orbitFamilyUnion base y).mp hy with ⟨q, i, hi⟩
    have hyOrbit : y ∈ h.rotationOrbitFinset (base q) :=
      (h.mem_rotationOrbitFinset (base q) y).mpr ⟨i, hi⟩
    have hsub :
        h.rotationOrbitFinset (base q) ⊆ S := by
      simpa [S] using
        h.rotationOrbitFinset_subset_neighborFinset_rotationFixedCenter
          (hbase_adj q)
    exact hsub hyOrbit
  have hUnion_card : (h.orbitFamilyUnion base).card = 57 := by
    have hcard :=
      h.orbitFamilyUnion_card_eq_nineteen_mul_card base
        (by
          intro q r hqr
          exact hbase_disjoint q r hqr)
        hbase_card
    simpa using hcard
  have hcover : S = h.orbitFamilyUnion base := by
    exact (Finset.eq_of_subset_of_card_le hUnion_subset (by
      rw [hS_card, hUnion_card])).symm
  exact ⟨base, hbase_adj, hbase_card, hbase_disjoint, by
    simpa [S] using hcover⟩

end D19ActsOnMoore57

end Moore57
