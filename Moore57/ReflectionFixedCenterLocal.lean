import Moore57.BranchOrbitABCFromCenter
import Moore57.BranchOrbitABCReflectionLabeling

/-!
# Local reflection facts around the rotation-fixed center

This file exposes thin, warning-free aliases for raw D19 reflection facts near
the unique rotation-fixed center.  The exact fixed-neighbor count is stated in
the orbit-local form: if a reflection preserves one of the center-neighbor
rotation orbits, then that orbit contains exactly one fixed vertex.
-/

namespace Moore57

open Finset

noncomputable section

namespace D19ActsOnMoore57

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- Alias: every reflection fixes the rotation-fixed center. -/
theorem rotationFixedCenter_fixed_reflection
    (h : D19ActsOnMoore57 V Γ) (k : ZMod 19) :
    h.smul (DihedralGroup.sr k) h.rotationFixedCenter =
      h.rotationFixedCenter :=
  h.reflection_smul_rotationFixedCenter k

/-- Alias: the rotation-fixed center has degree `57`. -/
theorem rotationFixedCenter_neighbor_card_eq_57
    (h : D19ActsOnMoore57 V Γ) :
    (Γ.neighborFinset h.rotationFixedCenter).card = 57 :=
  h.neighborFinset_rotationFixedCenter_card

/-- Alias: the neighbors of the rotation-fixed center split into three
rotation orbits of size `19`. -/
theorem exists_three_rotation_orbits_on_rotationFixedCenter_neighbors
    (h : D19ActsOnMoore57 V Γ) :
    ∃ base : Fin 3 → V,
      (∀ q : Fin 3, Γ.Adj h.rotationFixedCenter (base q)) ∧
      (∀ q : Fin 3, (h.rotationOrbitFinset (base q)).card = 19) ∧
      (∀ q r : Fin 3, q ≠ r →
        Disjoint (h.rotationOrbitFinset (base q))
          (h.rotationOrbitFinset (base r))) ∧
      Γ.neighborFinset h.rotationFixedCenter = h.orbitFamilyUnion base :=
  h.exists_three_rotationOrbitFinset_neighbors_rotationFixedCenter

/-- If a reflection preserves the rotation orbit of `x`, then the fixed
vertices in that orbit form a singleton. -/
theorem reflection_fixed_points_in_rotationOrbitFinset_eq_singleton_of_mem
    (h : D19ActsOnMoore57 V Γ) {k : ZMod 19} {x : V}
    (hmove : h.rotation 1 x ≠ x)
    (hrefOrbit :
      h.smul (DihedralGroup.sr k) x ∈ h.rotationOrbitFinset x) :
    ∃ y : V,
      (h.rotationOrbitFinset x).filter
          (fun z => h.smul (DihedralGroup.sr k) z = z) = {y} := by
  classical
  rcases (h.mem_rotationOrbitFinset x
      (h.smul (DihedralGroup.sr k) x)).mp hrefOrbit with ⟨i, hi⟩
  let t : ZMod 19 := (2 : ZMod 19)⁻¹ * i
  let y : V := h.rotation t x
  refine ⟨y, ?_⟩
  apply Finset.eq_singleton_iff_unique_mem.mpr
  constructor
  · refine Finset.mem_filter.mpr ⟨?_, ?_⟩
    · exact (h.mem_rotationOrbitFinset x y).mpr ⟨t, rfl⟩
    · dsimp [y]
      have htwo :
          (2 : ZMod 19) * t = i := by
        dsimp [t]
        rw [← mul_assoc, mul_inv_cancel₀ two_ne_zero_zmod19, one_mul]
      have htwo_add :
          t + t = i := by
        rw [← two_mul, htwo]
      have hneg_add :
          -t + i = t := by
        calc
          -t + i
              = -t + (t + t) := by
                  rw [htwo_add]
          _ = t := by
                  abel
      calc
        h.smul (DihedralGroup.sr k)
            (h.rotation t x)
            = h.rotation (-t)
                (h.smul (DihedralGroup.sr k) x) := by
                exact h.reflection_smul_rotation k t x
        _ = h.rotation (-t) (h.rotation i x) := by
                rw [← hi]
        _ = h.rotation (-t + i) x := by
                simpa [Equiv.Perm.mul_apply] using
                  congrArg (fun σ : Equiv.Perm V => σ x)
                    (h.rotation_add (-t) i).symm
        _ = h.rotation t x := by
                rw [hneg_add]
  · intro z hz
    rcases Finset.mem_filter.mp hz with ⟨hzOrbit, hzFixed⟩
    rcases (h.mem_rotationOrbitFinset x z).mp hzOrbit with ⟨j, hj⟩
    have hinj :
        Function.Injective (fun n : ZMod 19 => h.rotation n x) :=
      h.rotationOrbitW_injective_of_nonzero_moved (by decide) hmove
    have hcoord :
        -j + i = j := by
      apply hinj
      calc
        h.rotation (-j + i) x
            = h.rotation (-j) (h.rotation i x) := by
                simpa [Equiv.Perm.mul_apply] using
                  congrArg (fun σ : Equiv.Perm V => σ x)
                    (h.rotation_add (-j) i)
        _ = h.rotation (-j) (h.smul (DihedralGroup.sr k) x) := by
                rw [hi]
        _ = h.smul (DihedralGroup.sr k) (h.rotation j x) := by
                exact h.rotation_neg_reflection_smul k j x
        _ = h.rotation j x := by
                rw [hj, hzFixed]
    have htwo_j : (2 : ZMod 19) * j = i := by
      calc
        (2 : ZMod 19) * j = j + j := by ring
        _ = (-j + i) + j := by rw [hcoord]
        _ = i := by abel
    have hj_eq : j = t := by
      calc
        j = (2 : ZMod 19)⁻¹ * ((2 : ZMod 19) * j) := by
              rw [← mul_assoc, inv_mul_cancel₀ two_ne_zero_zmod19, one_mul]
        _ = (2 : ZMod 19)⁻¹ * i := by rw [htwo_j]
        _ = t := by rfl
    rw [← hj, hj_eq]

/-- Cardinal form of
`reflection_fixed_points_in_rotationOrbitFinset_eq_singleton_of_mem`. -/
theorem reflection_fixed_points_in_rotationOrbitFinset_card_eq_one_of_mem
    (h : D19ActsOnMoore57 V Γ) {k : ZMod 19} {x : V}
    (hmove : h.rotation 1 x ≠ x)
    (hrefOrbit :
      h.smul (DihedralGroup.sr k) x ∈ h.rotationOrbitFinset x) :
    ((h.rotationOrbitFinset x).filter
        fun z => h.smul (DihedralGroup.sr k) z = z).card = 1 := by
  rcases h.reflection_fixed_points_in_rotationOrbitFinset_eq_singleton_of_mem
      hmove hrefOrbit with ⟨y, hy⟩
  rw [hy, Finset.card_singleton]

/-- If a reflection preserves one of the three center-neighbor rotation orbits,
then exactly one vertex in that orbit is fixed by the reflection. -/
theorem reflection_fixed_center_neighbor_orbit_card_eq_one_of_mem
    (h : D19ActsOnMoore57 V Γ)
    (base : Fin 3 → V)
    (base_adj : ∀ q : Fin 3, Γ.Adj h.rotationFixedCenter (base q))
    {k : ZMod 19} {q : Fin 3}
    (hrefOrbit :
      h.smul (DihedralGroup.sr k) (base q) ∈
        h.rotationOrbitFinset (base q)) :
    ((h.rotationOrbitFinset (base q)).filter
        fun z => h.smul (DihedralGroup.sr k) z = z).card = 1 :=
  h.reflection_fixed_points_in_rotationOrbitFinset_card_eq_one_of_mem
    (h.rotationFixedCenter_neighbor_moved (base_adj q)) hrefOrbit

/-- If the quotient-level reflection action fixes a selected center-neighbor
orbit index, then that orbit has exactly one reflection-fixed vertex. -/
theorem reflection_fixed_center_neighbor_orbit_card_eq_one_of_index_eq
    (h : D19ActsOnMoore57 V Γ)
    (base : Fin 3 → V)
    (base_adj : ∀ q : Fin 3, Γ.Adj h.rotationFixedCenter (base q))
    (base_cover :
      Γ.neighborFinset h.rotationFixedCenter = h.orbitFamilyUnion base)
    {k : ZMod 19} {q : Fin 3}
    (hindex :
      BranchOrbitABCReflectionLabeling.reflectionCenterNeighborOrbitIndex
        (h := h) base base_adj base_cover k q = q) :
    ((h.rotationOrbitFinset (base q)).filter
        fun z => h.smul (DihedralGroup.sr k) z = z).card = 1 := by
  exact h.reflection_fixed_center_neighbor_orbit_card_eq_one_of_mem
    base base_adj (by
      simpa [hindex] using
        BranchOrbitABCReflectionLabeling.reflectionCenterNeighborOrbitIndex_mem
          (h := h) base base_adj base_cover k q)

end D19ActsOnMoore57

end

end Moore57
