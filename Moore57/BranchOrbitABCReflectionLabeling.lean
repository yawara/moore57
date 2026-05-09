import Moore57.BranchOrbitABCReflectionChoice

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

end BranchOrbitABCReflectionLabeling

end

end Moore57
