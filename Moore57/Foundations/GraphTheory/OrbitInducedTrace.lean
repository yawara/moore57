import Moore57.Foundations.GraphTheory.InducedTrace
import Mathlib.Algebra.Group.Subgroup.Defs
import Mathlib.GroupTheory.GroupAction.Defs
import Mathlib.GroupTheory.GroupAction.Basic
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.Tactic.Linarith

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

/-! ### Lemma 9 (1) full count form (abstract orbit-stabilizer hypothesis) -/

/-- **Lemma 9 (1) ℕ-form, abstract** — `|X| · deg = count · |O|`.

Given a `Finset X ⊆ Equiv.Perm V` of automorphisms, a vertex `v ∈ O`,
an orbit `O` of `X` containing `v`, and the orbit-stabilizer fiber-size
constraint (`fiberSize w = stabSize` for each `w ∈ O`), the identity
`|X| · deg_{Γ[O]}(v) = #{y ∈ X : v ~ y v} · |O|` holds.

The full Mačaj–Širáň count form
`Tr(O) = #{x ∈ X : v ∼ x v} · |O| / |X|`
follows by dividing through by `|X|·|O|` (in ℚ) and noting that
`Tr(O) = deg_{Γ[O]}(v)` from `inducedTrace_eq_neighborhood_card_of_transitive`.

The `fiberSize w = stabSize` hypothesis (each `w ∈ O` has the same
number of pre-images in the action `y ↦ y v`) is the standard
orbit-stabilizer theorem applied pointwise; it is taken as a hypothesis
here to keep the lemma independent of any specific group-theoretic
formalization of `Subgroup` action / coset decomposition. -/
theorem orbit_count_identity_of_fiber_uniform
    {O : Finset V} {v : V}
    {Xfs : Finset (Equiv.Perm V)}
    (stabCard : ℕ)
    (h_fiber : ∀ w ∈ O,
        (Xfs.filter (fun y : Equiv.Perm V => y v = w)).card = stabCard)
    (h_orbit_eq : O = Xfs.image (fun y : Equiv.Perm V => y v))
    (h_yv_in_O : ∀ y ∈ Xfs, y v ∈ O) :
    Xfs.card * (O.filter (fun w => Γ.Adj v w)).card =
      (Xfs.filter (fun y : Equiv.Perm V => Γ.Adj v (y v))).card * O.card := by
  classical
  -- Step 1: Xfs.card = O.card * stabCard.
  have h_X_decomp : Xfs.card = O.card * stabCard := by
    -- Partition Xfs by the value of y ↦ y v.
    have hpart : Xfs.card = ∑ w ∈ O,
        (Xfs.filter (fun y => y v = w)).card := by
      rw [h_orbit_eq, ← Finset.card_eq_sum_card_fiberwise (f := fun y => y v) (s := Xfs)
        (t := Xfs.image (fun y => y v)) (H := ?_)]
      intros y hy
      exact Finset.mem_image_of_mem _ hy
    rw [hpart]
    have hsum : ∑ w ∈ O, (Xfs.filter (fun y => y v = w)).card =
        ∑ _w ∈ O, stabCard := Finset.sum_congr rfl h_fiber
    rw [hsum, Finset.sum_const, smul_eq_mul]
  -- Step 2: count = deg · stabCard.
  have h_count : (Xfs.filter (fun y => Γ.Adj v (y v))).card =
      (O.filter (fun w => Γ.Adj v w)).card * stabCard := by
    -- Partition {y : v ~ yv} by yv ∈ O ∩ N(v).
    have h_eq : Xfs.filter (fun y => Γ.Adj v (y v)) =
        (O.filter (fun w => Γ.Adj v w)).biUnion
          (fun w => Xfs.filter (fun y => y v = w)) := by
      ext y
      simp only [Finset.mem_filter, Finset.mem_biUnion]
      constructor
      · intro ⟨hy_in, hy_adj⟩
        exact ⟨y v, ⟨h_yv_in_O y hy_in, hy_adj⟩, hy_in, rfl⟩
      · rintro ⟨w, ⟨_, hwadj⟩, hy_in, hy_eq⟩
        exact ⟨hy_in, hy_eq ▸ hwadj⟩
    rw [h_eq, Finset.card_biUnion]
    · have hsum : ∑ w ∈ O.filter (fun w => Γ.Adj v w),
          (Xfs.filter (fun y => y v = w)).card =
          ∑ _w ∈ O.filter (fun w => Γ.Adj v w), stabCard := by
        apply Finset.sum_congr rfl
        intros w hw
        rw [Finset.mem_filter] at hw
        exact h_fiber w hw.1
      rw [hsum, Finset.sum_const, smul_eq_mul]
    · intros w1 _ w2 _ hne
      simp only [Function.onFun, Finset.disjoint_left, Finset.mem_filter]
      intros y hy1 hy2
      exact hne (hy1.2.symm.trans hy2.2)
  -- Step 3: Combine.
  rw [h_X_decomp, h_count]; ring

/-- **Lemma 9 (1) ℚ-form, abstract** — the orbit trace formula
`Tr(O) = count · |O| / |X|`.

Combines `inducedTrace_eq_neighborhood_card_of_transitive` (giving
`Tr(O) = deg_{Γ[O]}(v)`) with `orbit_count_identity_of_fiber_uniform`
(giving `|X|·deg = count·|O|`). -/
theorem inducedTrace_orbit_count_formula
    {O : Finset V} {v : V} (hv : v ∈ O)
    (hO_trans : ∀ w ∈ O, ∃ φ : Equiv.Perm V,
        (∀ a b : V, Γ.Adj a b ↔ Γ.Adj (φ a) (φ b)) ∧
        φ v = w ∧
        ∀ u : V, u ∈ O ↔ φ u ∈ O)
    {Xfs : Finset (Equiv.Perm V)} (hXfs_nonempty : Xfs.Nonempty)
    (stabCard : ℕ)
    (h_fiber : ∀ w ∈ O,
        (Xfs.filter (fun y : Equiv.Perm V => y v = w)).card = stabCard)
    (h_orbit_eq : O = Xfs.image (fun y : Equiv.Perm V => y v))
    (h_yv_in_O : ∀ y ∈ Xfs, y v ∈ O) :
    inducedTrace Γ O =
      ((Xfs.filter (fun y : Equiv.Perm V => Γ.Adj v (y v))).card : ℚ) *
        (O.card : ℚ) / (Xfs.card : ℚ) := by
  classical
  have h_tr : inducedTrace Γ O = ((O.filter (fun w => Γ.Adj v w)).card : ℚ) :=
    inducedTrace_eq_neighborhood_card_of_transitive (Γ := Γ) hv hO_trans
  have h_nat := orbit_count_identity_of_fiber_uniform (Γ := Γ)
    stabCard h_fiber h_orbit_eq h_yv_in_O
  -- h_nat : Xfs.card * (O.filter (Γ.Adj v ·)).card =
  --         (Xfs.filter ...).card * O.card  in ℕ.
  -- Cast to ℚ, then divide.
  have hX_card_pos : 0 < Xfs.card := Finset.card_pos.mpr hXfs_nonempty
  have hX_ne : (Xfs.card : ℚ) ≠ 0 := by exact_mod_cast hX_card_pos.ne'
  rw [h_tr]
  -- Goal: (filter card)_O = (filter ...)_X * O.card / Xfs.card
  rw [eq_div_iff hX_ne]
  have h_rat : (Xfs.card : ℚ) * (O.filter (fun w => Γ.Adj v w)).card =
      (Xfs.filter (fun y => Γ.Adj v (y v))).card * (O.card : ℚ) := by
    exact_mod_cast h_nat
  linarith

end Moore57
