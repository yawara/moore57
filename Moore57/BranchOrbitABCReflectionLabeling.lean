import Moore57.BranchOrbitABCReflectionChoice
import Moore57.FixedInducedDegree
import Moore57.ZMod19Lemmas

/-!
# Reflection-compatible A/B/C branch labeling

This file packages fixed-center branch data whose B and C representatives are
chosen compatibly with one reflection.  The automatic three-orbit constructor
in `BranchOrbitABCFromCenter` labels the neighbor orbits arbitrarily; the
constructors below make the extra reflection-pair choice explicit.
-/

namespace Moore57

open Finset

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- Fixed-center A/B/C data together with a reflection sending the chosen
B representative exactly to the chosen C representative. -/
structure BranchOrbitABCReflectionLabeling
    (h : D19ActsOnMoore57 V Γ) where
  /-- The underlying fixed-center branch data. -/
  data : BranchOrbitABCFromCenter h
  /-- Reflection parameter. -/
  k : ZMod 19
  /-- The chosen reflection exchanges the B representative with the C
  representative, up to the exact representatives stored in `data`. -/
  reflection_b0_eq_c0 :
    h.smul (DihedralGroup.sr k) data.b0 = data.c0

namespace BranchOrbitABCReflectionLabeling

variable {h : D19ActsOnMoore57 V Γ}

/-- The minimal labeled-orbit hypothesis needed to build an exact
reflection-compatible labeling: there is some fixed-center A/B/C labeling for
which a reflection sends `b0` into the rotation orbit of `c0`. -/
def HasLabeledReflectionPair (h : D19ActsOnMoore57 V Γ) : Prop :=
  ∃ data : BranchOrbitABCFromCenter h, ∃ k : ZMod 19,
    h.smul (DihedralGroup.sr k) data.b0 ∈ h.rotationOrbitFinset data.c0

/-- Any reflection sends a selected center-neighbor rotation orbit into one of
the three selected center-neighbor rotation orbits.  This is the quotient-level
permutation statement; proving that it is nontrivial for some reflection is
the remaining reflection-pair gap. -/
theorem reflection_smul_center_neighbor_base_mem_rotationOrbitFinset
    (base : Fin 3 → V)
    (base_adj : ∀ q : Fin 3, Γ.Adj h.rotationFixedCenter (base q))
    (base_cover :
      Γ.neighborFinset h.rotationFixedCenter = h.orbitFamilyUnion base)
    (k : ZMod 19) (q : Fin 3) :
    ∃ r : Fin 3,
      h.smul (DihedralGroup.sr k) (base q) ∈
        h.rotationOrbitFinset (base r) := by
  classical
  let y : V := h.smul (DihedralGroup.sr k) (base q)
  have hyAdj : Γ.Adj h.rotationFixedCenter y := by
    have hAdj :
        Γ.Adj (h.smul (DihedralGroup.sr k) h.rotationFixedCenter)
          (h.smul (DihedralGroup.sr k) (base q)) :=
      (h.smul_adj (DihedralGroup.sr k) h.rotationFixedCenter (base q)).mp
        (base_adj q)
    simpa [y, h.reflection_smul_rotationFixedCenter k] using hAdj
  have hyNeighbor : y ∈ Γ.neighborFinset h.rotationFixedCenter := by
    simpa [SimpleGraph.mem_neighborFinset] using hyAdj
  have hyUnion : y ∈ h.orbitFamilyUnion base := by
    simpa [base_cover] using hyNeighbor
  rcases (h.mem_orbitFamilyUnion base y).mp hyUnion with ⟨r, i, hi⟩
  exact ⟨r, (h.mem_rotationOrbitFinset (base r) y).mpr ⟨i, hi⟩⟩

/-- The target center-neighbor orbit of a reflected selected base point is
unique, provided the three selected orbits are pairwise disjoint. -/
theorem reflection_smul_center_neighbor_base_orbit_index_unique
    (base : Fin 3 → V)
    (base_pairwise_disjoint :
      ∀ q r : Fin 3, q ≠ r →
        Disjoint (h.rotationOrbitFinset (base q))
          (h.rotationOrbitFinset (base r)))
    {k : ZMod 19} {q r s : Fin 3}
    (hr :
      h.smul (DihedralGroup.sr k) (base q) ∈
        h.rotationOrbitFinset (base r))
    (hs :
      h.smul (DihedralGroup.sr k) (base q) ∈
        h.rotationOrbitFinset (base s)) :
    r = s := by
  by_contra hrs
  exact (Finset.disjoint_left.mp (base_pairwise_disjoint r s hrs)) hr hs

/-- The index of the center-neighbor rotation orbit containing the reflected
image of `base q`. -/
noncomputable def reflectionCenterNeighborOrbitIndex
    (base : Fin 3 → V)
    (base_adj : ∀ q : Fin 3, Γ.Adj h.rotationFixedCenter (base q))
    (base_cover :
      Γ.neighborFinset h.rotationFixedCenter = h.orbitFamilyUnion base)
    (k : ZMod 19) (q : Fin 3) : Fin 3 :=
  Classical.choose
    (reflection_smul_center_neighbor_base_mem_rotationOrbitFinset
      (h := h) base base_adj base_cover k q)

/-- The reflected selected base point lies in the orbit indexed by
`reflectionCenterNeighborOrbitIndex`. -/
theorem reflectionCenterNeighborOrbitIndex_mem
    (base : Fin 3 → V)
    (base_adj : ∀ q : Fin 3, Γ.Adj h.rotationFixedCenter (base q))
    (base_cover :
      Γ.neighborFinset h.rotationFixedCenter = h.orbitFamilyUnion base)
    (k : ZMod 19) (q : Fin 3) :
    h.smul (DihedralGroup.sr k) (base q) ∈
      h.rotationOrbitFinset
        (base (reflectionCenterNeighborOrbitIndex
          (h := h) base base_adj base_cover k q)) :=
  Classical.choose_spec
    (reflection_smul_center_neighbor_base_mem_rotationOrbitFinset
      (h := h) base base_adj base_cover k q)

/-- Any orbit-membership witness identifies the reflected-orbit index. -/
theorem reflectionCenterNeighborOrbitIndex_eq_of_mem
    (base : Fin 3 → V)
    (base_adj : ∀ q : Fin 3, Γ.Adj h.rotationFixedCenter (base q))
    (base_pairwise_disjoint :
      ∀ q r : Fin 3, q ≠ r →
        Disjoint (h.rotationOrbitFinset (base q))
          (h.rotationOrbitFinset (base r)))
    (base_cover :
      Γ.neighborFinset h.rotationFixedCenter = h.orbitFamilyUnion base)
    {k : ZMod 19} {q r : Fin 3}
    (hr :
      h.smul (DihedralGroup.sr k) (base q) ∈
        h.rotationOrbitFinset (base r)) :
    reflectionCenterNeighborOrbitIndex (h := h) base base_adj base_cover k q =
      r :=
  reflection_smul_center_neighbor_base_orbit_index_unique
    (h := h) base base_pairwise_disjoint
    (reflectionCenterNeighborOrbitIndex_mem
      (h := h) base base_adj base_cover k q)
    hr

/-- If a reflection sends a point into its own rotation orbit, then that
rotation orbit contains a point fixed by the reflection.  Algebraically, if
`sr k • x = r^i • x`, the midpoint `r^(i/2) • x` is fixed. -/
theorem exists_reflection_fixed_point_mem_rotationOrbitFinset_of_mem
    {k : ZMod 19} {x : V}
    (hrefOrbit :
      h.smul (DihedralGroup.sr k) x ∈ h.rotationOrbitFinset x) :
    ∃ y : V, y ∈ h.rotationOrbitFinset x ∧
      h.smul (DihedralGroup.sr k) y = y := by
  rcases (h.mem_rotationOrbitFinset x (h.smul (DihedralGroup.sr k) x)).mp
      hrefOrbit with ⟨i, hi⟩
  let t : ZMod 19 := (2 : ZMod 19)⁻¹ * i
  have htwo_t : (2 : ZMod 19) * t = i := by
    dsimp [t]
    rw [← mul_assoc, mul_inv_cancel₀ two_ne_zero_zmod19, one_mul]
  have ht_add : t + t = i := by
    rw [← two_mul, htwo_t]
  have hneg_add : -t + i = t := by
    rw [← ht_add]
    abel
  refine ⟨h.rotation t x, ?_, ?_⟩
  · exact (h.mem_rotationOrbitFinset x (h.rotation t x)).mpr ⟨t, rfl⟩
  · calc
      h.smul (DihedralGroup.sr k) (h.rotation t x)
          = h.rotation (-t) (h.smul (DihedralGroup.sr k) x) := by
              exact h.reflection_smul_rotation k t x
      _ = h.rotation (-t) (h.rotation i x) := by
              rw [← hi]
      _ = h.rotation ((-t) + i) x := by
              simpa [Equiv.Perm.mul_apply] using
                congrArg (fun σ : Equiv.Perm V => σ x)
                  (h.rotation_add (-t) i).symm
      _ = h.rotation t x := by
              rw [hneg_add]

/-- Among three indices, if `b` and `c` are distinct there is a remaining
index distinct from both. -/
theorem exists_fin3_ne_ne {b c : Fin 3} (hbc : b ≠ c) :
    ∃ a : Fin 3, a ≠ b ∧ a ≠ c := by
  fin_cases b <;> fin_cases c <;> simp at hbc ⊢
  · exact ⟨2, by decide, by decide⟩
  · exact ⟨1, by decide, by decide⟩
  · exact ⟨2, by decide, by decide⟩
  · exact ⟨0, by decide, by decide⟩
  · exact ⟨1, by decide, by decide⟩
  · exact ⟨0, by decide, by decide⟩

/-- Pack the standard three-orbit center-neighbor decomposition together with
the fact that every reflection preserves the set of these three quotient
orbits. -/
theorem exists_three_center_neighbor_orbits_reflection_smul_mem_rotationOrbitFinset
    (h : D19ActsOnMoore57 V Γ) :
    ∃ base : Fin 3 → V,
      (∀ q : Fin 3, Γ.Adj h.rotationFixedCenter (base q)) ∧
      (∀ q : Fin 3, (h.rotationOrbitFinset (base q)).card = 19) ∧
      (∀ q r : Fin 3, q ≠ r →
        Disjoint (h.rotationOrbitFinset (base q))
          (h.rotationOrbitFinset (base r))) ∧
      Γ.neighborFinset h.rotationFixedCenter = h.orbitFamilyUnion base ∧
      ∀ k : ZMod 19, ∀ q : Fin 3,
        ∃ r : Fin 3,
          h.smul (DihedralGroup.sr k) (base q) ∈
            h.rotationOrbitFinset (base r) := by
  classical
  rcases h.exists_three_rotationOrbitFinset_neighbors_rotationFixedCenter with
    ⟨base, base_adj, base_card, base_pairwise_disjoint, base_cover⟩
  exact
    ⟨base, base_adj, base_card, base_pairwise_disjoint, base_cover, by
      intro k q
      exact reflection_smul_center_neighbor_base_mem_rotationOrbitFinset
        (h := h) base base_adj base_cover k q⟩

/-- The exact reflection equality stored in a reflection-compatible labeling
implies the orbit-level reflection-pair condition. -/
theorem reflection_b0_mem_c0_orbit
    (labeling : BranchOrbitABCReflectionLabeling h) :
    h.smul (DihedralGroup.sr labeling.k) labeling.data.b0 ∈
      h.rotationOrbitFinset labeling.data.c0 := by
  rw [labeling.reflection_b0_eq_c0]
  exact (h.mem_rotationOrbitFinset labeling.data.c0 labeling.data.c0).mpr
    ⟨0, by simp⟩

/-- In a reflection-compatible labeling, the reflection preserving the exact
B/C representatives necessarily preserves the remaining A rotation orbit. -/
theorem reflection_a0_mem_a0_orbit
    (labeling : BranchOrbitABCReflectionLabeling h) :
    h.smul (DihedralGroup.sr labeling.k) labeling.data.a0 ∈
      h.rotationOrbitFinset labeling.data.a0 := by
  classical
  let data := labeling.data
  let y : V := h.smul (DihedralGroup.sr labeling.k) data.a0
  have hyAdj : Γ.Adj h.rotationFixedCenter y := by
    have hAdj :
        Γ.Adj (h.smul (DihedralGroup.sr labeling.k) data.u)
          (h.smul (DihedralGroup.sr labeling.k) data.a0) :=
      (h.smul_adj (DihedralGroup.sr labeling.k) data.u data.a0).mp
        data.a0_adj
    simpa [y, data.u_eq_rotationFixedCenter,
      h.reflection_smul_rotationFixedCenter labeling.k] using hAdj
  have hyNeighbor : y ∈ Γ.neighborFinset h.rotationFixedCenter := by
    simpa [SimpleGraph.mem_neighborFinset] using hyAdj
  have hcover0 :
      Γ.neighborFinset h.rotationFixedCenter =
        h.orbitFamilyUnion data.base := by
    rw [← data.u_eq_rotationFixedCenter]
    simpa [BranchOrbitABCFromCenter.base] using data.cover_neighbors
  have hyUnion : y ∈ h.orbitFamilyUnion data.base := by
    simpa [hcover0] using hyNeighbor
  rcases (h.mem_orbitFamilyUnion data.base y).mp hyUnion with ⟨q, i, hi⟩
  have hyOrbit :
      y ∈ h.rotationOrbitFinset (data.base q) :=
    (h.mem_rotationOrbitFinset (data.base q) y).mpr ⟨i, hi⟩
  fin_cases q
  · simpa [data, y] using hyOrbit
  · rcases (h.mem_rotationOrbitFinset data.b0 y).mp (by
        simpa [data] using hyOrbit) with ⟨j, hj⟩
    have ha0_eq :
        h.rotation (-j) data.c0 = data.a0 := by
      calc
        h.rotation (-j) data.c0
            = h.smul (DihedralGroup.sr labeling.k) (h.rotation j data.b0) := by
              simpa [data, labeling.reflection_b0_eq_c0] using
                h.rotation_neg_reflection_smul labeling.k j data.b0
        _ = h.smul (DihedralGroup.sr labeling.k) y := by
              rw [hj]
        _ = data.a0 := by
              simpa [data, y] using
                h.reflection_smul_reflection_smul labeling.k data.a0
    have ha0_mem_a :
        data.a0 ∈ h.rotationOrbitFinset data.a0 :=
      (h.mem_rotationOrbitFinset data.a0 data.a0).mpr ⟨0, by simp⟩
    have ha0_mem_c :
        data.a0 ∈ h.rotationOrbitFinset data.c0 :=
      (h.mem_rotationOrbitFinset data.c0 data.a0).mpr ⟨-j, ha0_eq⟩
    have hdis :
        Disjoint (h.rotationOrbitFinset data.a0)
          (h.rotationOrbitFinset data.c0) := by
      simpa [BranchOrbitABCFromCenter.base] using
        data.pairwise_disjoint 0 2 (by decide)
    exact False.elim ((Finset.disjoint_left.mp hdis) ha0_mem_a ha0_mem_c)
  · rcases (h.mem_rotationOrbitFinset data.c0 y).mp (by
        simpa [data] using hyOrbit) with ⟨j, hj⟩
    have href_c0 :
        h.smul (DihedralGroup.sr labeling.k) data.c0 = data.b0 :=
      data.reflection_smul_c0_eq_b0_of_reflection_smul_b0_eq_c0
        labeling.reflection_b0_eq_c0
    have ha0_eq :
        h.rotation (-j) data.b0 = data.a0 := by
      calc
        h.rotation (-j) data.b0
            = h.smul (DihedralGroup.sr labeling.k) (h.rotation j data.c0) := by
              simpa [href_c0] using
                h.rotation_neg_reflection_smul labeling.k j data.c0
        _ = h.smul (DihedralGroup.sr labeling.k) y := by
              rw [hj]
        _ = data.a0 := by
              simpa [data, y] using
                h.reflection_smul_reflection_smul labeling.k data.a0
    have ha0_mem_a :
        data.a0 ∈ h.rotationOrbitFinset data.a0 :=
      (h.mem_rotationOrbitFinset data.a0 data.a0).mpr ⟨0, by simp⟩
    have ha0_mem_b :
        data.a0 ∈ h.rotationOrbitFinset data.b0 :=
      (h.mem_rotationOrbitFinset data.b0 data.a0).mpr ⟨-j, ha0_eq⟩
    have hdis :
        Disjoint (h.rotationOrbitFinset data.a0)
          (h.rotationOrbitFinset data.b0) := by
      simpa [BranchOrbitABCFromCenter.base] using
        data.pairwise_disjoint 0 1 (by decide)
    exact False.elim ((Finset.disjoint_left.mp hdis) ha0_mem_a ha0_mem_b)

/-- Package an orbit-level reflected B/C statement into exact representative
equality by shifting the reflection parameter. -/
noncomputable def ofReflectionOrbit
    (data : BranchOrbitABCFromCenter h) {k : ZMod 19}
    (hrefOrbit :
      h.smul (DihedralGroup.sr k) data.b0 ∈
        h.rotationOrbitFinset data.c0) :
    BranchOrbitABCReflectionLabeling h := by
  classical
  let hexists :=
    data.exists_reflection_smul_b0_eq_c0_of_reflection_smul_b0_mem_c0_orbit
      hrefOrbit
  let k' : ZMod 19 := Classical.choose hexists
  have hk' : h.smul (DihedralGroup.sr k') data.b0 = data.c0 :=
    Classical.choose_spec hexists
  exact
    { data := data
      k := k'
      reflection_b0_eq_c0 := hk' }

/-- Build reflection-compatible labeling from the minimal labeled-orbit
existence hypothesis. -/
noncomputable def ofHasLabeledReflectionPair
    (hp : HasLabeledReflectionPair h) :
    BranchOrbitABCReflectionLabeling h := by
  classical
  let data : BranchOrbitABCFromCenter h := Classical.choose hp
  have hdata : ∃ k : ZMod 19,
      h.smul (DihedralGroup.sr k) data.b0 ∈
        h.rotationOrbitFinset data.c0 :=
    Classical.choose_spec hp
  let k : ZMod 19 := Classical.choose hdata
  have hrefOrbit :
      h.smul (DihedralGroup.sr k) data.b0 ∈
        h.rotationOrbitFinset data.c0 :=
    Classical.choose_spec hdata
  exact ofReflectionOrbit data (k := k) hrefOrbit

/-- A reflection-compatible relabeling of an explicit three-orbit
center-neighbor decomposition.

The input `base` is any `Fin 3` family satisfying the fixed-center neighbor
decomposition.  The indices `a`, `b`, and `c` choose the A orbit, the B orbit,
and the C orbit.  The C representative is replaced by the reflected B
representative itself, so the resulting record has exact
`sr k • b0 = c0` by construction. -/
noncomputable def ofNeighborOrbitBaseReflectionPair
    (base : Fin 3 → V)
    (base_adj : ∀ q : Fin 3, Γ.Adj h.rotationFixedCenter (base q))
    (base_pairwise_disjoint :
      ∀ q r : Fin 3, q ≠ r →
        Disjoint (h.rotationOrbitFinset (base q))
          (h.rotationOrbitFinset (base r)))
    (a b c : Fin 3)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (k : ZMod 19)
    (hrefOrbit :
      h.smul (DihedralGroup.sr k) (base b) ∈
        h.rotationOrbitFinset (base c)) :
    BranchOrbitABCReflectionLabeling h := by
  classical
  let c0 : V := h.smul (DihedralGroup.sr k) (base b)
  let newBase : Fin 3 → V := branchABCBase (base a) (base b) c0
  have hc0_adj : Γ.Adj h.rotationFixedCenter c0 := by
    have hAdj :
        Γ.Adj (h.smul (DihedralGroup.sr k) h.rotationFixedCenter)
          (h.smul (DihedralGroup.sr k) (base b)) :=
      (h.smul_adj (DihedralGroup.sr k) h.rotationFixedCenter (base b)).mp
        (base_adj b)
    simpa [c0, h.reflection_smul_rotationFixedCenter k] using hAdj
  have hnew_adj :
      ∀ q : Fin 3, Γ.Adj h.rotationFixedCenter (newBase q) := by
    intro q
    fin_cases q <;> simp [newBase, base_adj, hc0_adj]
  have hnew_card :
      ∀ q : Fin 3, (h.rotationOrbitFinset (newBase q)).card = 19 := by
    intro q
    exact h.rotationOrbitFinset_card_neighbor_rotationFixedCenter
      (hnew_adj q)
  have hc0_orbit_eq :
      h.rotationOrbitFinset c0 = h.rotationOrbitFinset (base c) :=
    h.rotationOrbitFinset_eq_of_mem hrefOrbit
  have hnew_pairwise :
      ∀ q r : Fin 3, q ≠ r →
        Disjoint (h.rotationOrbitFinset (newBase q))
          (h.rotationOrbitFinset (newBase r)) := by
    intro q r hqr
    fin_cases q <;> fin_cases r <;>
      simp [newBase] at hqr ⊢
    · exact base_pairwise_disjoint a b hab
    · simpa [hc0_orbit_eq] using base_pairwise_disjoint a c hac
    · exact base_pairwise_disjoint b a hab.symm
    · simpa [hc0_orbit_eq] using base_pairwise_disjoint b c hbc
    · simpa [hc0_orbit_eq] using base_pairwise_disjoint c a hac.symm
    · simpa [hc0_orbit_eq] using base_pairwise_disjoint c b hbc.symm
  have hUnion_subset :
      h.orbitFamilyUnion newBase ⊆
        Γ.neighborFinset h.rotationFixedCenter := by
    intro y hy
    rcases (h.mem_orbitFamilyUnion newBase y).mp hy with ⟨q, i, hi⟩
    have hyOrbit : y ∈ h.rotationOrbitFinset (newBase q) :=
      (h.mem_rotationOrbitFinset (newBase q) y).mpr ⟨i, hi⟩
    exact h.rotationOrbitFinset_subset_neighborFinset_rotationFixedCenter
      (hnew_adj q) hyOrbit
  have hUnion_card : (h.orbitFamilyUnion newBase).card = 57 := by
    have hcard :=
      h.orbitFamilyUnion_card_eq_nineteen_mul_card newBase
        (by
          intro q r hqr
          exact hnew_pairwise q r hqr)
        hnew_card
    simpa using hcard
  have hcover :
      Γ.neighborFinset h.rotationFixedCenter = h.orbitFamilyUnion newBase := by
    exact
      (Finset.eq_of_subset_of_card_le hUnion_subset (by
        rw [h.neighborFinset_rotationFixedCenter_card, hUnion_card])).symm
  let data : BranchOrbitABCFromCenter h :=
    { u := h.rotationFixedCenter
      a0 := base a
      b0 := base b
      c0 := c0
      u_eq_rotationFixedCenter := rfl
      u_fixed := h.rotationFixedCenter_fixed_rotation
      a0_adj := base_adj a
      b0_adj := base_adj b
      c0_adj := hc0_adj
      a0_moved := h.rotationFixedCenter_neighbor_moved (base_adj a)
      b0_moved := h.rotationFixedCenter_neighbor_moved (base_adj b)
      c0_moved := h.rotationFixedCenter_neighbor_moved hc0_adj
      orbit_card := by
        intro q
        change (h.rotationOrbitFinset (newBase q)).card = 19
        exact hnew_card q
      pairwise_disjoint := by
        intro q r hqr
        change Disjoint (h.rotationOrbitFinset (newBase q))
          (h.rotationOrbitFinset (newBase r))
        exact hnew_pairwise q r hqr
      cover_neighbors := by
        change Γ.neighborFinset h.rotationFixedCenter =
          h.orbitFamilyUnion newBase
        exact hcover }
  exact
    { data := data
      k := k
      reflection_b0_eq_c0 := rfl }

/-- The explicit reflected-orbit constructor also supplies the minimal
`HasLabeledReflectionPair` boundary. -/
noncomputable def hasLabeledReflectionPair_ofNeighborOrbitBaseReflectionPair
    (base : Fin 3 → V)
    (base_adj : ∀ q : Fin 3, Γ.Adj h.rotationFixedCenter (base q))
    (base_pairwise_disjoint :
      ∀ q r : Fin 3, q ≠ r →
        Disjoint (h.rotationOrbitFinset (base q))
          (h.rotationOrbitFinset (base r)))
    (a b c : Fin 3)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (k : ZMod 19)
    (hrefOrbit :
      h.smul (DihedralGroup.sr k) (base b) ∈
        h.rotationOrbitFinset (base c)) :
    HasLabeledReflectionPair h := by
  classical
  let labeling :=
    ofNeighborOrbitBaseReflectionPair (h := h) base base_adj
      base_pairwise_disjoint a b c hab hac hbc k hrefOrbit
  exact ⟨labeling.data, labeling.k, labeling.reflection_b0_mem_c0_orbit⟩

/-- If the induced reflected-orbit index moves one of the three
center-neighbor orbits, then the minimal labeled reflection-pair boundary
holds.  This is the finite quotient action form of the remaining reflection
gap. -/
noncomputable def hasLabeledReflectionPair_of_reflectionCenterNeighborOrbitIndex_ne
    (base : Fin 3 → V)
    (base_adj : ∀ q : Fin 3, Γ.Adj h.rotationFixedCenter (base q))
    (base_pairwise_disjoint :
      ∀ q r : Fin 3, q ≠ r →
        Disjoint (h.rotationOrbitFinset (base q))
          (h.rotationOrbitFinset (base r)))
    (base_cover :
      Γ.neighborFinset h.rotationFixedCenter = h.orbitFamilyUnion base)
    {k : ZMod 19} {b : Fin 3}
    (hmove :
      reflectionCenterNeighborOrbitIndex
        (h := h) base base_adj base_cover k b ≠ b) :
    HasLabeledReflectionPair h := by
  classical
  let c : Fin 3 :=
    reflectionCenterNeighborOrbitIndex (h := h) base base_adj base_cover k b
  have hbc : b ≠ c := by
    intro hbc_eq
    exact hmove hbc_eq.symm
  rcases exists_fin3_ne_ne hbc with ⟨a, hab, hac⟩
  exact hasLabeledReflectionPair_ofNeighborOrbitBaseReflectionPair
    (h := h) base base_adj base_pairwise_disjoint a b c hab hac hbc k
    (by
      simpa [c] using
        reflectionCenterNeighborOrbitIndex_mem
          (h := h) base base_adj base_cover k b)

/-- If a reflection has at most one fixed neighbor of the rotation-fixed
center, then it must move at least one of the three center-neighbor rotation
orbits. -/
theorem exists_reflectionCenterNeighborOrbitIndex_ne_of_fixed_neighbors_card_le_one
    (base : Fin 3 → V)
    (base_adj : ∀ q : Fin 3, Γ.Adj h.rotationFixedCenter (base q))
    (base_pairwise_disjoint :
      ∀ q r : Fin 3, q ≠ r →
        Disjoint (h.rotationOrbitFinset (base q))
          (h.rotationOrbitFinset (base r)))
    (base_cover :
      Γ.neighborFinset h.rotationFixedCenter = h.orbitFamilyUnion base)
    (k : ZMod 19)
    (hfixed_le :
      ((Γ.neighborFinset h.rotationFixedCenter).filter fun y =>
        h.smul (DihedralGroup.sr k) y = y).card ≤ 1) :
    ∃ b : Fin 3,
      reflectionCenterNeighborOrbitIndex
        (h := h) base base_adj base_cover k b ≠ b := by
  classical
  by_contra hnone
  have hsame :
      ∀ q : Fin 3,
        reflectionCenterNeighborOrbitIndex
          (h := h) base base_adj base_cover k q = q := by
    intro q
    by_contra hneq
    exact hnone ⟨q, hneq⟩
  have hrefOrbit :
      ∀ q : Fin 3,
        h.smul (DihedralGroup.sr k) (base q) ∈
          h.rotationOrbitFinset (base q) := by
    intro q
    simpa [hsame q] using
      reflectionCenterNeighborOrbitIndex_mem
        (h := h) base base_adj base_cover k q
  let fixedPoint : Fin 3 → V := fun q =>
    Classical.choose
      (exists_reflection_fixed_point_mem_rotationOrbitFinset_of_mem
        (h := h) (hrefOrbit q))
  have fixedPoint_mem_orbit :
      ∀ q : Fin 3, fixedPoint q ∈ h.rotationOrbitFinset (base q) := by
    intro q
    exact
      (Classical.choose_spec
        (exists_reflection_fixed_point_mem_rotationOrbitFinset_of_mem
          (h := h) (hrefOrbit q))).1
  have fixedPoint_fixed :
      ∀ q : Fin 3,
        h.smul (DihedralGroup.sr k) (fixedPoint q) = fixedPoint q := by
    intro q
    exact
      (Classical.choose_spec
        (exists_reflection_fixed_point_mem_rotationOrbitFinset_of_mem
          (h := h) (hrefOrbit q))).2
  have fixedPoint_mem_filter :
      ∀ q : Fin 3,
        fixedPoint q ∈
          (Γ.neighborFinset h.rotationFixedCenter).filter fun y =>
            h.smul (DihedralGroup.sr k) y = y := by
    intro q
    have hneighbor :
        fixedPoint q ∈ Γ.neighborFinset h.rotationFixedCenter :=
      h.rotationOrbitFinset_subset_neighborFinset_rotationFixedCenter
        (base_adj q) (fixedPoint_mem_orbit q)
    exact Finset.mem_filter.mpr ⟨hneighbor, fixedPoint_fixed q⟩
  have fixedPoint_injective : Function.Injective fixedPoint := by
    intro q r hqr
    by_contra hqne
    exact
      (Finset.disjoint_left.mp (base_pairwise_disjoint q r hqne))
        (fixedPoint_mem_orbit q)
        (by simpa [hqr] using fixedPoint_mem_orbit r)
  have himage_subset :
      (Finset.univ.image fixedPoint) ⊆
        (Γ.neighborFinset h.rotationFixedCenter).filter fun y =>
          h.smul (DihedralGroup.sr k) y = y := by
    intro y hy
    rcases Finset.mem_image.mp hy with ⟨q, _hq, rfl⟩
    exact fixedPoint_mem_filter q
  have himage_card : (Finset.univ.image fixedPoint).card = 3 := by
    rw [Finset.card_image_of_injective _ fixedPoint_injective]
    simp
  have hthree :
      3 ≤ ((Γ.neighborFinset h.rotationFixedCenter).filter fun y =>
        h.smul (DihedralGroup.sr k) y = y).card := by
    rw [← himage_card]
    exact Finset.card_le_card himage_subset
  omega

/-- Uniform fixed-neighbor bound form of
`exists_reflectionCenterNeighborOrbitIndex_ne_of_fixed_neighbors_card_le_one`. -/
theorem forall_exists_reflectionCenterNeighborOrbitIndex_ne_of_fixed_neighbors_card_le_one
    (base : Fin 3 → V)
    (base_adj : ∀ q : Fin 3, Γ.Adj h.rotationFixedCenter (base q))
    (base_pairwise_disjoint :
      ∀ q r : Fin 3, q ≠ r →
        Disjoint (h.rotationOrbitFinset (base q))
          (h.rotationOrbitFinset (base r)))
    (base_cover :
      Γ.neighborFinset h.rotationFixedCenter = h.orbitFamilyUnion base)
    (hfixed_le :
      ∀ k : ZMod 19,
        ((Γ.neighborFinset h.rotationFixedCenter).filter fun y =>
          h.smul (DihedralGroup.sr k) y = y).card ≤ 1) :
    ∀ k : ZMod 19,
      ∃ b : Fin 3,
        reflectionCenterNeighborOrbitIndex
          (h := h) base base_adj base_cover k b ≠ b := by
  intro k
  exact exists_reflectionCenterNeighborOrbitIndex_ne_of_fixed_neighbors_card_le_one
    (h := h) base base_adj base_pairwise_disjoint base_cover k
    (hfixed_le k)

/-- A fixed-induced-degree bound at the rotation fixed center supplies the
fixed-neighbor bound used to force nontrivial action on the three
center-neighbor rotation orbits. -/
theorem reflection_fixed_center_neighbors_card_le_one_of_fixedInducedDegree_le_one
    (k : ZMod 19)
    (hdegree :
      (h.fixedInducedGraph (DihedralGroup.sr k)).degree
          ⟨h.rotationFixedCenter, by
            change h.smul (DihedralGroup.sr k) h.rotationFixedCenter =
              h.rotationFixedCenter
            exact h.reflection_smul_rotationFixedCenter k⟩ ≤ 1) :
    ((Γ.neighborFinset h.rotationFixedCenter).filter fun y =>
        h.smul (DihedralGroup.sr k) y = y).card ≤ 1 := by
  let x : fixedVertexSet (h.smulEquiv (DihedralGroup.sr k)) :=
    ⟨h.rotationFixedCenter, by
      change h.smul (DihedralGroup.sr k) h.rotationFixedCenter =
        h.rotationFixedCenter
      exact h.reflection_smul_rotationFixedCenter k⟩
  have hdeg_eq :
      (h.fixedInducedGraph (DihedralGroup.sr k)).degree x =
        ((Γ.neighborFinset h.rotationFixedCenter).filter fun y =>
          h.smul (DihedralGroup.sr k) y = y).card := by
    simpa [x, D19ActsOnMoore57.smulEquiv] using
      h.fixedInducedGraph_degree_eq_fixedNeighborFinset_card
        (DihedralGroup.sr k) x
  exact hdeg_eq ▸ hdegree

/-- Uniform fixed-induced-degree bound form. -/
theorem fixed_center_neighbors_card_le_one_of_forall_fixedInducedDegree_le_one
    (hdegree :
      ∀ k : ZMod 19,
        (h.fixedInducedGraph (DihedralGroup.sr k)).degree
            ⟨h.rotationFixedCenter, by
              change h.smul (DihedralGroup.sr k) h.rotationFixedCenter =
                h.rotationFixedCenter
              exact h.reflection_smul_rotationFixedCenter k⟩ ≤ 1) :
    ∀ k : ZMod 19,
      ((Γ.neighborFinset h.rotationFixedCenter).filter fun y =>
        h.smul (DihedralGroup.sr k) y = y).card ≤ 1 := by
  intro k
  exact reflection_fixed_center_neighbors_card_le_one_of_fixedInducedDegree_le_one
    (h := h) k (hdegree k)

end BranchOrbitABCReflectionLabeling

end

end Moore57
