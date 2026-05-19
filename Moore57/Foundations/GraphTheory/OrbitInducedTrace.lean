import Moore57.Foundations.GraphTheory.InducedTrace
import Mathlib.Algebra.Group.Subgroup.Defs
import Mathlib.GroupTheory.GroupAction.Defs

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Induced trace on a transitive orbit

For a vertex subset `O ⊆ V` that is transitively acted on by graph
automorphisms (i.e. for any `v, w ∈ O` there is a graph automorphism
sending `v` to `w` and preserving `O`), the induced trace `Tr(Γ[O])` is
constant on `O` and equals the in-`O` degree of any single vertex.

This is the abstract content underlying Mačaj–Širáň 2010 §3 Lemma 9 (1):
> For an `X`-orbit `O` and `v ∈ O`,  `Tr(O) = deg_{Γ[O]}(v)`.

The full Lemma 9 (1) statement involves the orbit-stabilizer count
`|X| / |Stab_X(v)| = |O|`; the bijection-based proof here only needs
the existence of automorphisms.  See `Moore57.adjMovedSet_card` for
related abstractions on Moore57 graphs.
-/

namespace Moore57

variable {V : Type*} [Fintype V] [DecidableEq V]
  {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- **Induced-degree constancy on transitive orbits.**

For `v, w ∈ O`, if there is a graph automorphism `φ` of `Γ` with
`φ v = w` and `φ` preserves `O` (as a `↔`-style invariance), then the
induced-`O` degree at `v` equals the induced-`O` degree at `w`. -/
theorem inducedDegree_const_of_transitive
    {O : Finset V} {v w : V}
    {φ : Equiv.Perm V}
    (hφ_aut : ∀ a b : V, Γ.Adj a b ↔ Γ.Adj (φ a) (φ b))
    (hφ_vw : φ v = w)
    (hφ_O : ∀ u : V, u ∈ O ↔ φ u ∈ O) :
    (O.filter (fun u => Γ.Adj v u)).card =
      (O.filter (fun u => Γ.Adj w u)).card := by
  classical
  apply Finset.card_bij'
    (fun (u : V) (_ : u ∈ _) => φ u)
    (fun (u : V) (_ : u ∈ _) => φ⁻¹ u)
  · -- u in v-neighborhood ⟹ φ u in w-neighborhood.
    intros u hu
    rw [Finset.mem_filter] at hu ⊢
    refine ⟨(hφ_O u).mp hu.1, ?_⟩
    rw [← hφ_vw]
    exact (hφ_aut v u).mp hu.2
  · -- u' in w-neighborhood ⟹ φ⁻¹ u' in v-neighborhood.
    intros u' hu'
    rw [Finset.mem_filter] at hu' ⊢
    refine ⟨?_, ?_⟩
    · -- φ⁻¹ u' ∈ O via hφ_O.
      rw [hφ_O (φ⁻¹ u')]
      simpa using hu'.1
    · -- Γ.Adj v (φ⁻¹ u')
      have hadj : Γ.Adj (φ v) (φ (φ⁻¹ u')) := by
        have h1 : φ (φ⁻¹ u') = u' := by simp
        rw [h1, hφ_vw]; exact hu'.2
      exact (hφ_aut v (φ⁻¹ u')).mpr hadj
  · -- left inverse: φ⁻¹ (φ u) = u.
    intros u _; simp
  · -- right inverse: φ (φ⁻¹ u') = u'.
    intros u' _; simp

/-- **Induced trace on a transitive orbit equals the in-orbit degree.**

For `O ⊆ V` transitively acted upon by graph automorphisms (each
`w ∈ O` is the `φ_w`-image of `v` for some graph automorphism `φ_w`
preserving `O`), `Tr(Γ[O])` equals the in-`O` degree of `v`.

This abstracts the content of Mačaj–Širáň 2010 §3 Lemma 9 (1):
`Tr(O) = deg_{Γ[O]}(v) = #{x ∈ X : v ~ x v} · |O| / |X|` — the last
equality being the orbit-stabilizer expression for `deg_{Γ[O]}(v)`. -/
theorem inducedTrace_eq_neighborhood_card_of_transitive
    {O : Finset V} {v : V} (hv : v ∈ O)
    (hO_trans : ∀ w ∈ O, ∃ φ : Equiv.Perm V,
        (∀ a b : V, Γ.Adj a b ↔ Γ.Adj (φ a) (φ b)) ∧
        φ v = w ∧
        ∀ u : V, u ∈ O ↔ φ u ∈ O) :
    inducedTrace Γ O = ((O.filter (fun w => Γ.Adj v w)).card : ℚ) := by
  classical
  unfold inducedTrace
  have hO_card_pos : 0 < O.card := Finset.card_pos.mpr ⟨v, hv⟩
  have hO_card_ne_zero : (O.card : ℚ) ≠ 0 := by exact_mod_cast hO_card_pos.ne'
  rw [div_eq_iff hO_card_ne_zero]
  -- Goal: (inducedDegreeSum : ℚ) = (filter card : ℚ) * O.card
  -- Reduce to ℕ: inducedDegreeSum = (filter card) * O.card.
  have h_nat : inducedDegreeSum Γ O =
      (O.filter (fun w => Γ.Adj v w)).card * O.card := by
    unfold inducedDegreeSum
    -- Σ_{w ∈ O} (O.filter (Γ.Adj w ·)).card = deg(v) * |O|.
    rw [show (O.filter (fun w => Γ.Adj v w)).card * O.card
        = ∑ _w ∈ O, (O.filter (fun w => Γ.Adj v w)).card by
        rw [Finset.sum_const, smul_eq_mul, Nat.mul_comm]]
    refine Finset.sum_congr rfl (fun w hw => ?_)
    -- Goal: (O.filter (Γ.Adj w ·)).card = (O.filter (Γ.Adj v ·)).card
    obtain ⟨φ, hφ_aut, hφ_vw, hφ_O⟩ := hO_trans w hw
    exact (inducedDegree_const_of_transitive hφ_aut hφ_vw hφ_O).symm
  exact_mod_cast h_nat

end Moore57
