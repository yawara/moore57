import Mathlib.Tactic
import Moore57.D19OnMoore57.LinearCharacter.Input
import Moore57.D19OnMoore57.Reflection.RegularBranchExclusion
import Moore57.D19OnMoore57.Reflection.RemainingCandidateGeometryBoundary

/-!
# Arithmetic consequences of the regular-10 reflection branch

This file keeps the regular-`10` branch consequences local: from the
all-center-neighbor-orbits-preserved boundary it derives the fixed count,
regular fixed-induced degree, fixed-induced edge count, adjacent-moved count,
and the resulting Higman trace value.
-/

namespace Moore57

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

namespace ReflectionRegularTenAllCenterNeighborOrbitsPreserved

variable {h : D19ActsOnMoore57 V Γ} {k : ZMod 19}

/-- Projection of the fixed-count field from the regular-`10` branch. -/
theorem fixedVertexCount_eq_ten
    (hreg : ReflectionRegularTenAllCenterNeighborOrbitsPreserved h k) :
    fixedVertexCount (h.smulEquiv (DihedralGroup.sr k)) = 10 :=
  hreg.1

/-- Projection of the center-degree field from the regular-`10` branch. -/
theorem fixedInducedGraph_rotationFixedCenter_degree_eq_three
    (hreg : ReflectionRegularTenAllCenterNeighborOrbitsPreserved h k) :
    (h.fixedInducedGraph (DihedralGroup.sr k)).degree
        (D19ActsOnMoore57.reflectionRotationFixedCenter h k) = 3 := by
  rcases hreg with
    ⟨_hcount, _base, _base_adj, _base_pairwise_disjoint, _base_cover,
      hdegree, _hneighbors, _hpreserved, _hcards⟩
  exact hdegree

/-- The regular-`10` branch makes the full fixed-induced graph cubic. -/
theorem fixedInducedGraph_degree_eq_three
    (hreg : ReflectionRegularTenAllCenterNeighborOrbitsPreserved h k)
    (x : fixedVertexSet (h.smulEquiv (DihedralGroup.sr k))) :
    (h.fixedInducedGraph (DihedralGroup.sr k)).degree x = 3 := by
  classical
  let Gfix := h.fixedInducedGraph (DihedralGroup.sr k)
  let c : fixedVertexSet (h.smulEquiv (DihedralGroup.sr k)) :=
    D19ActsOnMoore57.reflectionRotationFixedCenter h k
  have hcdeg : Gfix.degree c = 3 := by
    simpa [Gfix, c] using
      hreg.fixedInducedGraph_rotationFixedCenter_degree_eq_three
  by_contra hxdeg_ne
  have hnotRegular :
      ¬ ∃ d : ℕ,
        ∀ y : fixedVertexSet (h.smulEquiv (DihedralGroup.sr k)),
          (h.fixedInducedGraph (DihedralGroup.sr k)).degree y = d := by
    rintro ⟨d, hd⟩
    have hxd : Gfix.degree x = d := by simpa [Gfix] using hd x
    have hcd : Gfix.degree c = d := by simpa [Gfix, c] using hd c
    exact hxdeg_ne (hxd.trans hcd.symm |>.trans hcdeg)
  have hstrong := h.fixedInducedGraph_isStrongZeroOne (DihedralGroup.sr k)
  rcases hstrong.exists_isStarWithCenter_of_not_regular hnotRegular with
    ⟨s, hstar⟩
  have hcard : Fintype.card (fixedVertexSet (h.smulEquiv (DihedralGroup.sr k))) = 10 := by
    simpa [fixedVertexCount_eq_card_fixedVertexSet] using hreg.fixedVertexCount_eq_ten
  by_cases hcs : c = s
  · have hcstar : Gfix.degree c = 9 := by
      rw [hcs]
      calc
        Gfix.degree s = Fintype.card (fixedVertexSet (h.smulEquiv (DihedralGroup.sr k))) - 1 := by
          simpa [Gfix] using hstar.degree_center_eq_card_sub_one
        _ = 9 := by omega
    omega
  · have hcstar : Gfix.degree c = 1 := by
      simpa [Gfix] using hstar.degree_noncenter_eq_one hcs
    omega

/-- Constant-degree regularity form of the regular-`10` branch. -/
theorem fixedInducedGraph_regular_degree_three
    (hreg : ReflectionRegularTenAllCenterNeighborOrbitsPreserved h k) :
    ∀ x : fixedVertexSet (h.smulEquiv (DihedralGroup.sr k)),
      (h.fixedInducedGraph (DihedralGroup.sr k)).degree x = 3 :=
  hreg.fixedInducedGraph_degree_eq_three

/-- The fixed-induced graph has fifteen edges in the regular-`10` branch. -/
theorem fixedInducedGraph_edgeFinset_card_eq_fifteen
    (hreg : ReflectionRegularTenAllCenterNeighborOrbitsPreserved h k) :
    (h.fixedInducedGraph (DihedralGroup.sr k)).edgeFinset.card = 15 := by
  have htwice :=
    h.fixedInducedGraph_twice_card_edgeFinset_eq_fixedVertexCount_mul_degree
      (DihedralGroup.sr k) 3 hreg.fixedInducedGraph_regular_degree_three
  rw [hreg.fixedVertexCount_eq_ten] at htwice
  omega

/-- The regular-`10` branch gives adjacent-moved count `2700`. -/
theorem adjacentMovedCount_eq_2700
    (hreg : ReflectionRegularTenAllCenterNeighborOrbitsPreserved h k) :
    adjacentMovedCount Γ (h.smulEquiv (DihedralGroup.sr k)) = 2700 := by
  have hformula :
      (adjacentMovedCount Γ (h.smulEquiv (DihedralGroup.sr k)) : ℤ) =
        3250 -
          58 * (fixedVertexCount (h.smulEquiv (DihedralGroup.sr k)) : ℤ) +
            2 * ((h.fixedInducedGraph (DihedralGroup.sr k)).edgeFinset.card : ℤ) :=
    adjacentMovedCount_eq_involution_fixed_edge_formula
      (Γ := Γ) h.isMoore
      (h.reflection_smulEquiv_involutive k)
      (h.reflection_smulEquiv_automorphism k)
  rw [hreg.fixedVertexCount_eq_ten,
    hreg.fixedInducedGraph_edgeFinset_card_eq_fifteen] at hformula
  norm_num at hformula
  exact_mod_cast hformula

/-- Higman's trace formula evaluates to `181` on the regular-`10` branch. -/
theorem trace_E7Matrix_mul_permMatrix_eq_181
    (hreg : ReflectionRegularTenAllCenterNeighborOrbitsPreserved h k) :
    Matrix.trace (E7Matrix Γ * permMatrix (h.smulEquiv (DihedralGroup.sr k))) =
      (181 : ℚ) := by
  rw [h.isMoore.higman_trace_formula,
    hreg.fixedVertexCount_eq_ten,
    hreg.adjacentMovedCount_eq_2700]
  norm_num

end ReflectionRegularTenAllCenterNeighborOrbitsPreserved

namespace D19ActsOnMoore57

variable {h : D19ActsOnMoore57 V Γ}

/-- D19 namespace wrapper for the regular-`10` fixed count. -/
theorem reflectionRegularTen_fixedVertexCount_eq_ten
    (k : ZMod 19)
    (hreg : ReflectionRegularTenAllCenterNeighborOrbitsPreserved h k) :
    fixedVertexCount (h.smulEquiv (DihedralGroup.sr k)) = 10 :=
  hreg.fixedVertexCount_eq_ten

/-- D19 namespace wrapper for cubic regularity of the fixed-induced graph. -/
theorem reflectionRegularTen_fixedInducedGraph_degree_eq_three
    (k : ZMod 19)
    (hreg : ReflectionRegularTenAllCenterNeighborOrbitsPreserved h k)
    (x : fixedVertexSet (h.smulEquiv (DihedralGroup.sr k))) :
    (h.fixedInducedGraph (DihedralGroup.sr k)).degree x = 3 :=
  hreg.fixedInducedGraph_degree_eq_three x

/-- D19 namespace wrapper for the fixed-induced edge count. -/
theorem reflectionRegularTen_fixedInducedGraph_edgeFinset_card_eq_fifteen
    (k : ZMod 19)
    (hreg : ReflectionRegularTenAllCenterNeighborOrbitsPreserved h k) :
    (h.fixedInducedGraph (DihedralGroup.sr k)).edgeFinset.card = 15 :=
  hreg.fixedInducedGraph_edgeFinset_card_eq_fifteen

/-- D19 namespace wrapper for the adjacent-moved count. -/
theorem reflectionRegularTen_adjacentMovedCount_eq_2700
    (k : ZMod 19)
    (hreg : ReflectionRegularTenAllCenterNeighborOrbitsPreserved h k) :
    adjacentMovedCount Γ (h.smulEquiv (DihedralGroup.sr k)) = 2700 :=
  hreg.adjacentMovedCount_eq_2700

/-- D19 namespace wrapper for the Higman trace value. -/
theorem reflectionRegularTen_trace_E7Matrix_mul_permMatrix_eq_181
    (k : ZMod 19)
    (hreg : ReflectionRegularTenAllCenterNeighborOrbitsPreserved h k) :
    Matrix.trace (E7Matrix Γ * permMatrix (h.smulEquiv (DihedralGroup.sr k))) =
      (181 : ℚ) :=
  hreg.trace_E7Matrix_mul_permMatrix_eq_181

end D19ActsOnMoore57

end

end Moore57

/-!
# Character boundary for the regular-10 reflection branch

The regular-`10` branch has E7 trace `181` on a reflection.  Any full D19
linear-character description of the E7 trace would therefore force
`alpha - beta = 181` on that reflection.  This file records that boundary and
the immediate incompatibility with the current `TraceMultiplicityData`, whose
reflection equation is `alpha - beta = 33`.
-/

namespace Moore57

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

namespace ReflectionRegularTenAllCenterNeighborOrbitsPreserved

variable {h : D19ActsOnMoore57 V Γ} {k : ZMod 19}

/-- If the E7 trace is a full D19 linear character, the regular-`10` branch
forces reflection character value `181`. -/
theorem alpha_sub_beta_eq_181_of_e7_linear_character
    (hreg : ReflectionRegularTenAllCenterNeighborOrbitsPreserved h k)
    (alpha beta gamma : ℕ)
    (h7 : ∀ g : DihedralGroup 19,
      Matrix.trace (E7Matrix Γ * permMatrix (h.smulEquiv g)) =
        (d19LinearCharacter alpha beta gamma g : ℚ)) :
    (alpha : ℤ) - (beta : ℤ) = 181 := by
  have htrace := hreg.trace_E7Matrix_mul_permMatrix_eq_181
  have hchar := h7 (DihedralGroup.sr k)
  rw [d19LinearCharacter_reflection] at hchar
  have hq : (((alpha : ℤ) - (beta : ℤ) : ℤ) : ℚ) = (181 : ℚ) := by
    linarith
  exact_mod_cast hq

/-- The regular-`10` branch is incompatible with a full
`D19LinearCharacterInput`, whose packaged reflection character value is `33`. -/
theorem not_d19LinearCharacterInput
    (hreg : ReflectionRegularTenAllCenterNeighborOrbitsPreserved h k) :
    ¬ Nonempty (D19ActsOnMoore57.D19LinearCharacterInput h) := by
  rintro ⟨hin⟩
  have h181 :
      (hin.multiplicity.alpha : ℤ) - (hin.multiplicity.beta : ℤ) = 181 :=
    hreg.alpha_sub_beta_eq_181_of_e7_linear_character
      hin.multiplicity.alpha hin.multiplicity.beta hin.multiplicity.gamma
      hin.linear_character
  have h33 :
      (hin.multiplicity.alpha : ℤ) - (hin.multiplicity.beta : ℤ) = 33 :=
    hin.multiplicity.reflection
  have hbad : (181 : ℤ) = 33 := h181.symm.trans h33
  norm_num at hbad

end ReflectionRegularTenAllCenterNeighborOrbitsPreserved

namespace D19ActsOnMoore57

variable {h : D19ActsOnMoore57 V Γ}

/-- D19 namespace wrapper for the regular-`10` reflection character value. -/
theorem reflectionRegularTen_alpha_sub_beta_eq_181_of_e7_linear_character
    (k : ZMod 19)
    (hreg : ReflectionRegularTenAllCenterNeighborOrbitsPreserved h k)
    (alpha beta gamma : ℕ)
    (h7 : ∀ g : DihedralGroup 19,
      Matrix.trace (E7Matrix Γ * permMatrix (h.smulEquiv g)) =
        (d19LinearCharacter alpha beta gamma g : ℚ)) :
    (alpha : ℤ) - (beta : ℤ) = 181 :=
  hreg.alpha_sub_beta_eq_181_of_e7_linear_character alpha beta gamma h7

/-- D19 namespace wrapper: regular-`10` contradicts full linear-character
input. -/
theorem reflectionRegularTen_not_d19LinearCharacterInput
    (k : ZMod 19)
    (hreg : ReflectionRegularTenAllCenterNeighborOrbitsPreserved h k) :
    ¬ Nonempty (D19ActsOnMoore57.D19LinearCharacterInput h) :=
  hreg.not_d19LinearCharacterInput

end D19ActsOnMoore57

end

end Moore57

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

/-!
# Strong-graph boundary for the regular-10 reflection branch

This file packages the graph-theoretic consequences of the
`ReflectionRegularTenAllCenterNeighborOrbitsPreserved` boundary.  The proofs
only specialize the fixed-induced graph API and the already-proved regular-ten
degree theorem.
-/

namespace Moore57

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

namespace ReflectionRegularTenAllCenterNeighborOrbitsPreserved

variable {h : D19ActsOnMoore57 V Γ} {k : ZMod 19}

/-- The fixed-induced graph in the regular-`10` branch is strongly regular
with parameters `(10, 3, 0, 1)`. -/
theorem fixedInducedGraph_isSRGWith_10_3_0_1
    (hreg : ReflectionRegularTenAllCenterNeighborOrbitsPreserved h k) :
    (h.fixedInducedGraph (DihedralGroup.sr k)).IsSRGWith 10 3 0 1 := by
  have hsrg :=
    h.fixedInducedGraph_isSRGWith_of_regular
      (DihedralGroup.sr k) 3 hreg.fixedInducedGraph_regular_degree_three
  simpa [hreg.fixedVertexCount_eq_ten] using hsrg

/-- The fixed-induced graph inherits the strong `(λ, μ) = (0, 1)` condition. -/
theorem fixedInducedGraph_isStrongZeroOne
    (_hreg : ReflectionRegularTenAllCenterNeighborOrbitsPreserved h k) :
    IsStrongZeroOne (h.fixedInducedGraph (DihedralGroup.sr k)) :=
  h.fixedInducedGraph_isStrongZeroOne (DihedralGroup.sr k)

/-- Adjacent vertices in the fixed-induced graph have no common neighbor. -/
theorem fixedInducedGraph_not_commonNeighbor_of_adj
    (hreg : ReflectionRegularTenAllCenterNeighborOrbitsPreserved h k)
    {x y z : fixedVertexSet (h.smulEquiv (DihedralGroup.sr k))}
    (hxy : (h.fixedInducedGraph (DihedralGroup.sr k)).Adj x y) :
    ¬ ((h.fixedInducedGraph (DihedralGroup.sr k)).Adj x z ∧
        (h.fixedInducedGraph (DihedralGroup.sr k)).Adj y z) :=
  hreg.fixedInducedGraph_isStrongZeroOne.not_commonNeighbor_of_adj hxy

/-- Triangle-free form for the fixed-induced graph. -/
theorem fixedInducedGraph_triangleFree
    (hreg : ReflectionRegularTenAllCenterNeighborOrbitsPreserved h k)
    {a b c : fixedVertexSet (h.smulEquiv (DihedralGroup.sr k))}
    (hab : (h.fixedInducedGraph (DihedralGroup.sr k)).Adj a b)
    (hac : (h.fixedInducedGraph (DihedralGroup.sr k)).Adj a c) :
    ¬ (h.fixedInducedGraph (DihedralGroup.sr k)).Adj b c :=
  hreg.fixedInducedGraph_isStrongZeroOne.not_adj_of_adj_of_adj hab hac

/-- Distinct non-adjacent vertices in the fixed-induced graph have a unique
common neighbor. -/
theorem fixedInducedGraph_existsUnique_commonNeighbor_of_not_adj
    (hreg : ReflectionRegularTenAllCenterNeighborOrbitsPreserved h k)
    {x y : fixedVertexSet (h.smulEquiv (DihedralGroup.sr k))}
    (hxy_ne : x ≠ y)
    (hxy_not : ¬ (h.fixedInducedGraph (DihedralGroup.sr k)).Adj x y) :
    ∃! z : fixedVertexSet (h.smulEquiv (DihedralGroup.sr k)),
      (h.fixedInducedGraph (DihedralGroup.sr k)).Adj x z ∧
        (h.fixedInducedGraph (DihedralGroup.sr k)).Adj y z :=
  hreg.fixedInducedGraph_isStrongZeroOne.existsUnique_commonNeighbor_of_not_adj
    hxy_ne hxy_not

end ReflectionRegularTenAllCenterNeighborOrbitsPreserved

namespace D19ActsOnMoore57

variable {h : D19ActsOnMoore57 V Γ}

/-- D19 namespace wrapper for the regular-`10` strongly-regular fixed graph. -/
theorem reflectionRegularTen_fixedInducedGraph_isSRGWith_10_3_0_1
    (k : ZMod 19)
    (hreg : ReflectionRegularTenAllCenterNeighborOrbitsPreserved h k) :
    (h.fixedInducedGraph (DihedralGroup.sr k)).IsSRGWith 10 3 0 1 :=
  hreg.fixedInducedGraph_isSRGWith_10_3_0_1

/-- D19 namespace wrapper for the strong `(λ, μ) = (0, 1)` fixed graph. -/
theorem reflectionRegularTen_fixedInducedGraph_isStrongZeroOne
    (k : ZMod 19)
    (hreg : ReflectionRegularTenAllCenterNeighborOrbitsPreserved h k) :
    IsStrongZeroOne (h.fixedInducedGraph (DihedralGroup.sr k)) :=
  hreg.fixedInducedGraph_isStrongZeroOne

/-- D19 namespace wrapper: adjacent fixed vertices have no common neighbor. -/
theorem reflectionRegularTen_fixedInducedGraph_not_commonNeighbor_of_adj
    (k : ZMod 19)
    (hreg : ReflectionRegularTenAllCenterNeighborOrbitsPreserved h k)
    {x y z : fixedVertexSet (h.smulEquiv (DihedralGroup.sr k))}
    (hxy : (h.fixedInducedGraph (DihedralGroup.sr k)).Adj x y) :
    ¬ ((h.fixedInducedGraph (DihedralGroup.sr k)).Adj x z ∧
        (h.fixedInducedGraph (DihedralGroup.sr k)).Adj y z) :=
  hreg.fixedInducedGraph_not_commonNeighbor_of_adj hxy

/-- D19 namespace wrapper: triangle-free form for the fixed-induced graph. -/
theorem reflectionRegularTen_fixedInducedGraph_triangleFree
    (k : ZMod 19)
    (hreg : ReflectionRegularTenAllCenterNeighborOrbitsPreserved h k)
    {a b c : fixedVertexSet (h.smulEquiv (DihedralGroup.sr k))}
    (hab : (h.fixedInducedGraph (DihedralGroup.sr k)).Adj a b)
    (hac : (h.fixedInducedGraph (DihedralGroup.sr k)).Adj a c) :
    ¬ (h.fixedInducedGraph (DihedralGroup.sr k)).Adj b c :=
  hreg.fixedInducedGraph_triangleFree hab hac

/-- D19 namespace wrapper: distinct non-adjacent fixed vertices have a unique
common neighbor. -/
theorem reflectionRegularTen_fixedInducedGraph_existsUnique_commonNeighbor_of_not_adj
    (k : ZMod 19)
    (hreg : ReflectionRegularTenAllCenterNeighborOrbitsPreserved h k)
    {x y : fixedVertexSet (h.smulEquiv (DihedralGroup.sr k))}
    (hxy_ne : x ≠ y)
    (hxy_not : ¬ (h.fixedInducedGraph (DihedralGroup.sr k)).Adj x y) :
    ∃! z : fixedVertexSet (h.smulEquiv (DihedralGroup.sr k)),
      (h.fixedInducedGraph (DihedralGroup.sr k)).Adj x z ∧
        (h.fixedInducedGraph (DihedralGroup.sr k)).Adj y z :=
  hreg.fixedInducedGraph_existsUnique_commonNeighbor_of_not_adj hxy_ne hxy_not

end D19ActsOnMoore57

end

end Moore57

