import Moore57.D19OnMoore57.D19Core.VertexPermutationRepresentation
import Moore57.D19OnMoore57.Reflection.Conjugacy
import Moore57.D19OnMoore57.Rotation.FixedCountOneFrontier
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.Tactic

/-!
# Burnside fixed-count constraints for the D19 action

This file records the orbit-count arithmetic forced by Burnside's lemma for
the concrete `D19ActsOnMoore57` vertex action.  With the proved nontrivial
rotation fixed-counts and the reflection conjugacy count, Burnside reduces to
the parity condition on the common reflection fixed count.
-/

namespace Moore57

noncomputable section

open scoped BigOperators

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

namespace D19ActsOnMoore57

variable (h : D19ActsOnMoore57 V Γ)

/-- The identity term in the Burnside fixed-count sum is the Moore57 vertex
count. -/
theorem fixedVertexCount_smulEquiv_one :
    fixedVertexCount (h.smulEquiv (1 : DihedralGroup 19)) = 3250 := by
  rw [h.smulEquiv_one]
  simp [fixedVertexCount, h.card_vertices]

/-- Split a sum over `D19` into the rotation and reflection coordinates. -/
theorem sum_dihedral_eq_sum_rotations_add_sum_reflections
    (f : DihedralGroup 19 → ℕ) :
    (∑ g : DihedralGroup 19, f g) =
      (∑ d : ZMod 19, f (DihedralGroup.r d)) +
        ∑ k : ZMod 19, f (DihedralGroup.sr k) := by
  rw [Fintype.sum_equiv (DihedralGroup.equivSum (n := 19)) f
      (fun x => f ((DihedralGroup.equivSum (n := 19)).symm x))]
  · simp [DihedralGroup.equivSum]
  · intro x
    cases x <;> rfl

/-- If every nontrivial rotation has one fixed vertex, then the total rotation
part of Burnside's sum is `3250 + 18`. -/
theorem sum_rotation_fixedVertexCount_eq
    (hrot :
      ∀ d : ZMod 19, d ≠ 0 →
        fixedVertexCount (h.smulEquiv (DihedralGroup.r d)) = 1) :
    (∑ d : ZMod 19, fixedVertexCount (h.smulEquiv (DihedralGroup.r d))) =
      3268 := by
  rw [← Finset.add_sum_erase (Finset.univ : Finset (ZMod 19))
    (fun d => fixedVertexCount (h.smulEquiv (DihedralGroup.r d)))
    (Finset.mem_univ 0)]
  have herase :
      (∑ x ∈ (Finset.univ : Finset (ZMod 19)).erase 0,
          fixedVertexCount (h.smulEquiv (DihedralGroup.r x))) = 18 := by
    have hsum :
        (∑ x ∈ (Finset.univ : Finset (ZMod 19)).erase 0,
            fixedVertexCount (h.smulEquiv (DihedralGroup.r x))) =
          (∑ _x ∈ (Finset.univ : Finset (ZMod 19)).erase 0, 1) := by
      refine Finset.sum_congr rfl ?_
      intro x hx
      exact hrot x (Finset.mem_erase.mp hx).1
    rw [hsum]
    rw [Finset.sum_const, nsmul_eq_mul]
    have hcard : ((Finset.univ : Finset (ZMod 19)).erase 0).card = 18 := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ 0)]
      rw [Finset.card_univ, ZMod.card]
    rw [hcard]
    norm_num
  rw [DihedralGroup.r_zero, h.fixedVertexCount_smulEquiv_one, herase]

/-- Reflection conjugacy makes the reflection part of Burnside's sum equal to
`19` times the `sr 0` fixed count. -/
theorem sum_reflection_fixedVertexCount_eq :
    (∑ k : ZMod 19, fixedVertexCount (h.smulEquiv (DihedralGroup.sr k))) =
      19 * fixedVertexCount (h.smulEquiv (DihedralGroup.sr 0)) := by
  calc
    (∑ k : ZMod 19, fixedVertexCount (h.smulEquiv (DihedralGroup.sr k))) =
        ∑ _k : ZMod 19, fixedVertexCount (h.smulEquiv (DihedralGroup.sr 0)) := by
      refine Finset.sum_congr rfl ?_
      intro k _hk
      exact h.fixedVertexCount_reflection_eq_reflection_zero k
    _ = 19 * fixedVertexCount (h.smulEquiv (DihedralGroup.sr 0)) := by
      rw [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul]
      norm_num

/-- Under the rotation fixed-count-one input, the whole Burnside fixed-count
sum is `3268 + 19 c`, where `c` is the common reflection fixed count. -/
theorem sum_fixedVertexCount_eq_3268_add_reflection_zero
    (hrot :
      ∀ d : ZMod 19, d ≠ 0 →
        fixedVertexCount (h.smulEquiv (DihedralGroup.r d)) = 1) :
    (∑ g : DihedralGroup 19, fixedVertexCount (h.smulEquiv g)) =
      3268 + 19 * fixedVertexCount (h.smulEquiv (DihedralGroup.sr 0)) := by
  rw [sum_dihedral_eq_sum_rotations_add_sum_reflections]
  rw [h.sum_rotation_fixedVertexCount_eq hrot]
  rw [h.sum_reflection_fixedVertexCount_eq]

/-- Burnside's lemma for the vertex action, in the divisibility form needed
for the arithmetic constraint. -/
theorem exists_sum_fixedVertexCount_eq_orbit_count_mul_card_group :
    ∃ q : ℕ,
      (∑ g : DihedralGroup 19, fixedVertexCount (h.smulEquiv g)) =
        q * Fintype.card (DihedralGroup 19) := by
  letI : MulAction (DihedralGroup 19) V := h.vertexMulAction
  haveI : Fintype (MulAction.orbitRel.Quotient (DihedralGroup 19) V) :=
    Fintype.ofFinite _
  refine ⟨Fintype.card (MulAction.orbitRel.Quotient (DihedralGroup 19) V), ?_⟩
  rw [← MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group
    (α := DihedralGroup 19) (β := V)]
  refine Finset.sum_congr rfl ?_
  intro g _hg
  rw [fixedVertexCount_eq_card_fixedVertexSet]
  exact Fintype.card_congr (Equiv.setCongr (by ext x; rfl))

/-- The Burnside fixed-count sum is divisible by `|D19| = 38`. -/
theorem thirtyEight_dvd_sum_fixedVertexCount :
    38 ∣ ∑ g : DihedralGroup 19, fixedVertexCount (h.smulEquiv g) := by
  rcases h.exists_sum_fixedVertexCount_eq_orbit_count_mul_card_group with ⟨q, hq⟩
  refine ⟨q, ?_⟩
  rw [hq, DihedralGroup.card]
  rw [Nat.mul_comm]

/-- Burnside plus the rotation fixed-count-one input gives the exact
divisibility constraint on the common reflection fixed count. -/
theorem thirtyEight_dvd_3268_add_nineteen_mul_reflection_zero
    (hrot :
      ∀ d : ZMod 19, d ≠ 0 →
        fixedVertexCount (h.smulEquiv (DihedralGroup.r d)) = 1) :
    38 ∣ 3268 + 19 * fixedVertexCount (h.smulEquiv (DihedralGroup.sr 0)) := by
  have hsum := h.sum_fixedVertexCount_eq_3268_add_reflection_zero hrot
  simpa [hsum] using h.thirtyEight_dvd_sum_fixedVertexCount

/-- Arithmetic consequence: the common reflection fixed count is even. -/
theorem reflection_zero_fixedVertexCount_even_of_rotation_fixed_count_one
    (hrot :
      ∀ d : ZMod 19, d ≠ 0 →
        fixedVertexCount (h.smulEquiv (DihedralGroup.r d)) = 1) :
    Even (fixedVertexCount (h.smulEquiv (DihedralGroup.sr 0))) := by
  let c := fixedVertexCount (h.smulEquiv (DihedralGroup.sr 0))
  have hdiv :
      38 ∣ 3268 + 19 * c :=
    h.thirtyEight_dvd_3268_add_nineteen_mul_reflection_zero hrot
  have htwo : 2 ∣ 3268 + 19 * c :=
    dvd_trans (by norm_num : 2 ∣ 38) hdiv
  rw [Nat.even_iff]
  have hmod : (3268 + 19 * c) % 2 = 0 :=
    Nat.dvd_iff_mod_eq_zero.mp htwo
  simpa [c, Nat.add_mod, Nat.mul_mod] using hmod

/-- The already-proved nontrivial rotation fixed-count theorem specializes the
Burnside arithmetic to the concrete D19 action. -/
theorem reflection_zero_fixedVertexCount_even :
    Even (fixedVertexCount (h.smulEquiv (DihedralGroup.sr 0))) :=
  h.reflection_zero_fixedVertexCount_even_of_rotation_fixed_count_one
    (D19ActsOnMoore57.rotationFixedCountOne_smulEquiv h)

end D19ActsOnMoore57

/-- Burnside's parity constraint does not remove any of the raw small
candidate counts `2, 6, 10, 16, 26, 36, 46`. -/
theorem burnside_constraint_all_raw_small_candidates :
    ∀ c ∈ ({2, 6, 10, 16, 26, 36, 46} : Finset ℕ), Even c := by
  decide

end

end Moore57
