import Moore57.D19OnMoore57.Reflection.ReflectionFixedCenterLocal

/-!
# Reflection permutation of the three center-neighbor rotation orbits

The reflection-induced quotient action on the three rotation orbits adjacent to
`rotationFixedCenter` is an involution.  Since it acts on `Fin 3`, it fixes at
least one orbit index, and the local fixed-center lemma then gives one fixed
vertex in that orbit.
-/

namespace Moore57

open Finset

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

namespace BranchOrbitABCReflectionLabeling

variable {h : D19ActsOnMoore57 V Γ}

/-- Every element of `Fin 3` is `0`, `1`, or `2`. -/
theorem fin3_eq_zero_or_one_or_two (q : Fin 3) :
    q = 0 ∨ q = 1 ∨ q = 2 := by
  fin_cases q <;> simp

/-- An involution of a three-element type has a fixed point. -/
theorem exists_fixed_of_involutive_fin3 (f : Fin 3 → Fin 3)
    (hf : Function.Involutive f) :
    ∃ q : Fin 3, f q = q := by
  rcases fin3_eq_zero_or_one_or_two (f 0) with h00 | h01 | h02
  · exact ⟨0, h00⟩
  · have hf1 : f 1 = 0 := by
      simpa [h01] using hf 0
    rcases fin3_eq_zero_or_one_or_two (f 2) with h20 | h21 | h22
    · have hf0 : f 0 = 2 := by
        simpa [h20] using hf 2
      exact False.elim (by omega)
    · have hf1' : f 1 = 2 := by
        simpa [h21] using hf 2
      exact False.elim (by omega)
    · exact ⟨2, h22⟩
  · have hf2 : f 2 = 0 := by
      simpa [h02] using hf 0
    rcases fin3_eq_zero_or_one_or_two (f 1) with h10 | h11 | h12
    · have hf0 : f 0 = 1 := by
        simpa [h10] using hf 1
      exact False.elim (by omega)
    · exact ⟨1, h11⟩
    · have hf2' : f 2 = 1 := by
        simpa [h12] using hf 1
      exact False.elim (by omega)

/-- Applying the same reflection again sends the indexed target orbit back to
the source orbit. -/
theorem reflectionCenterNeighborOrbitIndex_reflected_target_mem_source
    (base : Fin 3 → V)
    (base_adj : ∀ q : Fin 3, Γ.Adj h.rotationFixedCenter (base q))
    (base_cover :
      Γ.neighborFinset h.rotationFixedCenter = h.orbitFamilyUnion base)
    (k : ZMod 19) (q : Fin 3) :
    h.smul (DihedralGroup.sr k)
        (base (reflectionCenterNeighborOrbitIndex
          (h := h) base base_adj base_cover k q)) ∈
      h.rotationOrbitFinset (base q) := by
  classical
  let r : Fin 3 :=
    reflectionCenterNeighborOrbitIndex (h := h) base base_adj base_cover k q
  have hr :
      h.smul (DihedralGroup.sr k) (base q) ∈
        h.rotationOrbitFinset (base r) := by
    simpa [r] using
      reflectionCenterNeighborOrbitIndex_mem
        (h := h) base base_adj base_cover k q
  rcases (h.mem_rotationOrbitFinset (base r)
      (h.smul (DihedralGroup.sr k) (base q))).mp hr with ⟨i, hi⟩
  refine (h.mem_rotationOrbitFinset (base q)
    (h.smul (DihedralGroup.sr k) (base r))).mpr ⟨i, ?_⟩
  calc
    h.rotation i (base q)
        = h.rotation i
            (h.smul (DihedralGroup.sr k)
              (h.smul (DihedralGroup.sr k) (base q))) := by
            rw [h.reflection_smul_reflection_smul k (base q)]
    _ = h.rotation i
            (h.smul (DihedralGroup.sr k) (h.rotation i (base r))) := by
            rw [hi]
    _ = h.rotation i
            (h.rotation (-i) (h.smul (DihedralGroup.sr k) (base r))) := by
            rw [h.reflection_smul_rotation]
    _ = h.smul (DihedralGroup.sr k) (base r) := by
            exact h.rotation_apply_neg_rotation i
              (h.smul (DihedralGroup.sr k) (base r))

/-- The reflection-induced map on the three center-neighbor orbit indices is
an involution. -/
theorem reflectionCenterNeighborOrbitIndex_involutive
    (base : Fin 3 → V)
    (base_adj : ∀ q : Fin 3, Γ.Adj h.rotationFixedCenter (base q))
    (base_pairwise_disjoint :
      ∀ q r : Fin 3, q ≠ r →
        Disjoint (h.rotationOrbitFinset (base q))
          (h.rotationOrbitFinset (base r)))
    (base_cover :
      Γ.neighborFinset h.rotationFixedCenter = h.orbitFamilyUnion base)
    (k : ZMod 19) :
    Function.Involutive
      (reflectionCenterNeighborOrbitIndex
        (h := h) base base_adj base_cover k) := by
  intro q
  exact reflectionCenterNeighborOrbitIndex_eq_of_mem
    (h := h) base base_adj base_pairwise_disjoint base_cover
    (reflectionCenterNeighborOrbitIndex_reflected_target_mem_source
      (h := h) base base_adj base_cover k q)

/-- The reflection-induced map on the three center-neighbor orbit indices is
bijective. -/
theorem reflectionCenterNeighborOrbitIndex_bijective
    (base : Fin 3 → V)
    (base_adj : ∀ q : Fin 3, Γ.Adj h.rotationFixedCenter (base q))
    (base_pairwise_disjoint :
      ∀ q r : Fin 3, q ≠ r →
        Disjoint (h.rotationOrbitFinset (base q))
          (h.rotationOrbitFinset (base r)))
    (base_cover :
      Γ.neighborFinset h.rotationFixedCenter = h.orbitFamilyUnion base)
    (k : ZMod 19) :
    Function.Bijective
      (reflectionCenterNeighborOrbitIndex
        (h := h) base base_adj base_cover k) :=
  (reflectionCenterNeighborOrbitIndex_involutive
    (h := h) base base_adj base_pairwise_disjoint base_cover k).bijective

/-- The reflection-induced map packaged as a permutation of `Fin 3`. -/
noncomputable def reflectionCenterNeighborOrbitPerm
    (base : Fin 3 → V)
    (base_adj : ∀ q : Fin 3, Γ.Adj h.rotationFixedCenter (base q))
    (base_pairwise_disjoint :
      ∀ q r : Fin 3, q ≠ r →
        Disjoint (h.rotationOrbitFinset (base q))
          (h.rotationOrbitFinset (base r)))
    (base_cover :
      Γ.neighborFinset h.rotationFixedCenter = h.orbitFamilyUnion base)
    (k : ZMod 19) : Equiv.Perm (Fin 3) :=
  Equiv.ofBijective
    (reflectionCenterNeighborOrbitIndex
      (h := h) base base_adj base_cover k)
    (reflectionCenterNeighborOrbitIndex_bijective
      (h := h) base base_adj base_pairwise_disjoint base_cover k)

@[simp] theorem reflectionCenterNeighborOrbitPerm_apply
    (base : Fin 3 → V)
    (base_adj : ∀ q : Fin 3, Γ.Adj h.rotationFixedCenter (base q))
    (base_pairwise_disjoint :
      ∀ q r : Fin 3, q ≠ r →
        Disjoint (h.rotationOrbitFinset (base q))
          (h.rotationOrbitFinset (base r)))
    (base_cover :
      Γ.neighborFinset h.rotationFixedCenter = h.orbitFamilyUnion base)
    (k : ZMod 19) (q : Fin 3) :
    reflectionCenterNeighborOrbitPerm
        (h := h) base base_adj base_pairwise_disjoint base_cover k q =
      reflectionCenterNeighborOrbitIndex
        (h := h) base base_adj base_cover k q :=
  rfl

/-- The reflection-induced map on the three center-neighbor orbit indices has
a fixed index. -/
theorem exists_reflectionCenterNeighborOrbitIndex_eq_self
    (base : Fin 3 → V)
    (base_adj : ∀ q : Fin 3, Γ.Adj h.rotationFixedCenter (base q))
    (base_pairwise_disjoint :
      ∀ q r : Fin 3, q ≠ r →
        Disjoint (h.rotationOrbitFinset (base q))
          (h.rotationOrbitFinset (base r)))
    (base_cover :
      Γ.neighborFinset h.rotationFixedCenter = h.orbitFamilyUnion base)
    (k : ZMod 19) :
    ∃ q : Fin 3,
      reflectionCenterNeighborOrbitIndex
        (h := h) base base_adj base_cover k q = q :=
  exists_fixed_of_involutive_fin3
    (reflectionCenterNeighborOrbitIndex
      (h := h) base base_adj base_cover k)
    (reflectionCenterNeighborOrbitIndex_involutive
      (h := h) base base_adj base_pairwise_disjoint base_cover k)

end BranchOrbitABCReflectionLabeling

namespace D19ActsOnMoore57

variable (h : D19ActsOnMoore57 V Γ)

/-- For any three-orbit decomposition of the neighbors of
`rotationFixedCenter`, every reflection fixes exactly one vertex in at least
one of the three selected rotation orbits. -/
theorem exists_reflection_fixed_center_neighbor_orbit_card_eq_one_of_decomposition
    (base : Fin 3 → V)
    (base_adj : ∀ q : Fin 3, Γ.Adj h.rotationFixedCenter (base q))
    (base_pairwise_disjoint :
      ∀ q r : Fin 3, q ≠ r →
        Disjoint (h.rotationOrbitFinset (base q))
          (h.rotationOrbitFinset (base r)))
    (base_cover :
      Γ.neighborFinset h.rotationFixedCenter = h.orbitFamilyUnion base)
    (k : ZMod 19) :
    ∃ q : Fin 3,
      ((h.rotationOrbitFinset (base q)).filter
        fun z => h.smul (DihedralGroup.sr k) z = z).card = 1 := by
  rcases
    BranchOrbitABCReflectionLabeling.exists_reflectionCenterNeighborOrbitIndex_eq_self
        (h := h) base base_adj base_pairwise_disjoint base_cover k with
    ⟨q, hq⟩
  exact ⟨q,
    h.reflection_fixed_center_neighbor_orbit_card_eq_one_of_index_eq
      base base_adj base_cover hq⟩

/-- Existence form using the canonical three-orbit decomposition supplied by
`exists_three_rotationOrbitFinset_neighbors_rotationFixedCenter`. -/
theorem exists_reflection_fixed_center_neighbor_orbit_card_eq_one
    (k : ZMod 19) :
    ∃ base : Fin 3 → V, ∃ q : Fin 3,
      (∀ q : Fin 3, Γ.Adj h.rotationFixedCenter (base q)) ∧
      (∀ q r : Fin 3, q ≠ r →
        Disjoint (h.rotationOrbitFinset (base q))
          (h.rotationOrbitFinset (base r))) ∧
      Γ.neighborFinset h.rotationFixedCenter = h.orbitFamilyUnion base ∧
      ((h.rotationOrbitFinset (base q)).filter
        fun z => h.smul (DihedralGroup.sr k) z = z).card = 1 := by
  rcases h.exists_three_rotation_orbits_on_rotationFixedCenter_neighbors with
    ⟨base, base_adj, _base_card, base_pairwise_disjoint, base_cover⟩
  rcases h.exists_reflection_fixed_center_neighbor_orbit_card_eq_one_of_decomposition
      base base_adj base_pairwise_disjoint base_cover k with
    ⟨q, hq⟩
  exact ⟨base, q, base_adj, base_pairwise_disjoint, base_cover, hq⟩

end D19ActsOnMoore57

end

end Moore57
