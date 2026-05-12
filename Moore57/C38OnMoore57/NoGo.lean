import Moore57.C38OnMoore57.Action
import Moore57.Moore57Graph.Aut.FixedCount
import Moore57.Moore57Graph.Aut.InvolutionCandidates
import Mathlib.GroupTheory.Perm.Cycle.Type

/-!
# `C₃₈` cannot act on a Moore57 graph

This file proves `no_C38_acts_on_Moore57_unconditional`: the cyclic group of
order 38 is not a subgroup of `Aut(Γ)` for the Moore graph
`Γ = SRG(3250, 57, 0, 1)`.

The proof is short because two abstract Tier-2 ingredients are already in
place:

* `order19_aut_fixedVertexCount_eq_one` says that the order-`19` automorphism
  `ρ := g²` fixes exactly one vertex `u`.
* Since `τ := g^19` commutes with `ρ`, the involution `τ` fixes `u` and
  preserves `Fix(τ)` under the `ρ`-action. Restricting `ρ` to `Fix(τ)` gives a
  permutation whose `19`-th power is the identity, so
  `Equiv.Perm.card_compl_support_modEq` yields
  `|Fix(τ)| ≡ |Fix(τ) ∩ Fix(ρ)| ≡ 1 (mod 19)`.
* `aut_involution_fixedVertexCount_not_modEq_one` then immediately contradicts
  this congruence.
-/

namespace Moore57

open Finset SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

namespace C38ActsOnMoore57

/-- A witness `u ∈ fixedVertexSet h.rho` (the fixed set has cardinality `1`). -/
noncomputable def uWitness (h : C38ActsOnMoore57 V Γ) : fixedVertexSet h.rho :=
  Classical.choice (Fintype.card_pos_iff.mp (by
    rw [← fixedVertexCount_eq_card_fixedVertexSet]
    rw [order19_aut_fixedVertexCount_eq_one h.isMoore h.rho h.rho_aut
      h.rho_pow_nineteen h.rho_ne_one]
    decide))

/-- The unique vertex fixed by `ρ := g²`. -/
noncomputable def u (h : C38ActsOnMoore57 V Γ) : V := h.uWitness.val

variable (h : C38ActsOnMoore57 V Γ)

theorem rho_u_eq : h.rho h.u = h.u := h.uWitness.property

theorem tau_u_eq : h.tau h.u = h.u := by
  have h_comm := h.rho_mul_tau_eq_tau_mul_rho
  have : h.rho (h.tau h.u) = h.tau h.u := by
    have heq : h.rho (h.tau h.u) = h.tau (h.rho h.u) := by
      have := congr_arg (· h.u) h_comm.symm
      simpa using this
    rw [heq, h.rho_u_eq]
  -- Use uniqueness of `ρ`-fixed point: `|Fix(ρ)| = 1`, so any ρ-fixed vertex equals u.
  have hfix_one : fixedVertexCount h.rho = 1 :=
    order19_aut_fixedVertexCount_eq_one h.isMoore h.rho h.rho_aut
      h.rho_pow_nineteen h.rho_ne_one
  have htau_u_in_fix : h.tau h.u ∈ fixedVertexSet h.rho := this
  have hu_in_fix : h.u ∈ fixedVertexSet h.rho := h.rho_u_eq
  -- `fixedVertexSet h.rho` is a singleton.
  have hcard_one :
      Fintype.card (fixedVertexSet h.rho) = 1 := by
    rw [← fixedVertexCount_eq_card_fixedVertexSet]; exact hfix_one
  rcases Fintype.card_eq_one_iff.mp hcard_one with ⟨v, hv_unique⟩
  have h1 : (⟨h.tau h.u, htau_u_in_fix⟩ : fixedVertexSet h.rho) = v :=
    hv_unique ⟨h.tau h.u, htau_u_in_fix⟩
  have h2 : (⟨h.u, hu_in_fix⟩ : fixedVertexSet h.rho) = v :=
    hv_unique ⟨h.u, hu_in_fix⟩
  have : (⟨h.tau h.u, htau_u_in_fix⟩ : fixedVertexSet h.rho) =
      ⟨h.u, hu_in_fix⟩ := h1.trans h2.symm
  exact congrArg Subtype.val this

/-- `ρ` preserves the fixed set of `τ` (since `ρ` and `τ` commute). -/
theorem rho_preserves_tau_fix (v : V) (hv : h.tau v = v) :
    h.tau (h.rho v) = h.rho v := by
  have h_comm : h.rho * h.tau = h.tau * h.rho := h.rho_mul_tau_eq_tau_mul_rho
  -- ρ ∘ τ = τ ∘ ρ. Apply to v: (ρ τ) v = (τ ρ) v.
  have hcomm_v : h.tau (h.rho v) = h.rho (h.tau v) := by
    have := congr_arg (· v) h_comm.symm
    simpa using this
  rw [hcomm_v, hv]

/-- The restriction of `ρ` to `fixedVertexSet h.tau` is a well-defined
permutation. The `Equiv.Perm.subtypePerm` predicate is `p (f x) ↔ p x`. -/
noncomputable def rhoRestrict : Equiv.Perm (fixedVertexSet h.tau) :=
  h.rho.subtypePerm (fun v => by
    constructor
    · -- mp : (h.rho v ∈ fixedVertexSet h.tau) → (v ∈ fixedVertexSet h.tau)
      -- i.e., h.tau (h.rho v) = h.rho v → h.tau v = v
      intro hv
      have h_comm : h.rho * h.tau = h.tau * h.rho := h.rho_mul_tau_eq_tau_mul_rho
      have hcomm_v : h.rho (h.tau v) = h.tau (h.rho v) := by
        have := congr_arg (· v) h_comm
        simpa using this
      have hgoal : h.rho (h.tau v) = h.rho v := hcomm_v.trans hv
      exact h.rho.injective hgoal
    · -- mpr : v ∈ fixedVertexSet h.tau → h.rho v ∈ fixedVertexSet h.tau
      -- i.e., h.tau v = v → h.tau (h.rho v) = h.rho v
      intro hv
      exact h.rho_preserves_tau_fix v hv)

@[simp] theorem rhoRestrict_pow_nineteen :
    h.rhoRestrict ^ 19 = 1 := by
  ext v
  show (h.rho ^ 19) (v : V) = v
  rw [h.rho_pow_nineteen]
  rfl

/-- The fixed-vertex count of `τ` is congruent to `1` mod `19`. -/
theorem fixedVertexCount_tau_modEq_one :
    fixedVertexCount h.tau ≡ 1 [MOD 19] := by
  classical
  haveI : Fact (Nat.Prime 19) := ⟨by decide⟩
  have hpow : h.rhoRestrict ^ 19 ^ 1 = 1 := by
    simpa using h.rhoRestrict_pow_nineteen
  -- |Fix(τ)| ≡ |Fix(rhoRestrict)| mod 19
  have hmod := Equiv.Perm.card_compl_support_modEq
    (α := fixedVertexSet h.tau) (p := 19) (n := 1)
    (σ := h.rhoRestrict) hpow
  -- |Fix(τ)| = card (fixedVertexSet h.tau)
  have hcard_eq :
      fixedVertexCount h.tau = Fintype.card (fixedVertexSet h.tau) :=
    fixedVertexCount_eq_card_fixedVertexSet h.tau
  -- |Fix(rhoRestrict)| = |Fix(ρ) ∩ Fix(τ)| = |{u}| = 1 (since u ∈ Fix(τ)).
  have hsupp :
      h.rhoRestrict.supportᶜ.card = 1 := by
    -- show `Fix(rhoRestrict) = {⟨u, tau_u_eq⟩}`.
    rw [show h.rhoRestrict.supportᶜ.card =
        Fintype.card {w : fixedVertexSet h.tau // h.rhoRestrict w = w}
      from by
        rw [← Fintype.card_ofFinset h.rhoRestrict.supportᶜ (by intro w; rfl)]
        exact Fintype.card_congr
          { toFun := fun w => ⟨w.1, by simpa [Equiv.Perm.support] using w.2⟩
            invFun := fun w => ⟨w.1, by simpa [Equiv.Perm.support] using w.2⟩
            left_inv := fun w => rfl
            right_inv := fun w => rfl }]
    have hfix_eq :
        Fintype.card {w : fixedVertexSet h.tau // h.rhoRestrict w = w} = 1 := by
      have hfix_rho : fixedVertexCount h.rho = 1 :=
        order19_aut_fixedVertexCount_eq_one h.isMoore h.rho h.rho_aut
          h.rho_pow_nineteen h.rho_ne_one
      have hcard_rho :
          Fintype.card (fixedVertexSet h.rho) = 1 := by
        rw [← fixedVertexCount_eq_card_fixedVertexSet]; exact hfix_rho
      refine Fintype.card_eq_one_iff.mpr ⟨⟨⟨h.u, h.tau_u_eq⟩, ?_⟩, ?_⟩
      · apply Subtype.ext
        exact h.rho_u_eq
      · rintro ⟨⟨v, hv_tau⟩, hv_fix⟩
        have hv_rho : h.rho v = v := by
          show h.rho v = v
          have : h.rhoRestrict ⟨v, hv_tau⟩ = ⟨v, hv_tau⟩ := hv_fix
          exact congrArg Subtype.val this
        -- v ∈ Fix(h.rho) = {u}.
        rcases Fintype.card_eq_one_iff.mp hcard_rho with ⟨w, hw_unique⟩
        have h1 : (⟨v, hv_rho⟩ : fixedVertexSet h.rho) = w := hw_unique _
        have h2 : (⟨h.u, h.rho_u_eq⟩ : fixedVertexSet h.rho) = w := hw_unique _
        have hvu : v = h.u := by
          have : (⟨v, hv_rho⟩ : fixedVertexSet h.rho) = ⟨h.u, h.rho_u_eq⟩ :=
            h1.trans h2.symm
          exact congrArg Subtype.val this
        apply Subtype.ext
        apply Subtype.ext
        exact hvu
    exact hfix_eq
  rw [hcard_eq]
  -- hmod : 1 ≡ Fintype.card (fixedVertexSet h.tau) [MOD 19] after rw
  rw [hsupp] at hmod
  exact hmod.symm

/-- **Main theorem for `C₃₈`**: `C38ActsOnMoore57 V Γ` is uninhabited. -/
theorem false_of_raw_action (h : C38ActsOnMoore57 V Γ) : False := by
  have hmod : fixedVertexCount h.tau ≡ 1 [MOD 19] :=
    h.fixedVertexCount_tau_modEq_one
  exact aut_involution_fixedVertexCount_not_modEq_one h.isMoore h.tau
    h.tau_aut h.tau_involutive h.tau_ne_one hmod

end C38ActsOnMoore57

/-- **Main theorem**: `C38ActsOnMoore57 V Γ` is uninhabited.

The Moore graph of degree `57` (SRG(3250, 57, 0, 1)) does not admit `C₃₈`
(cyclic group of order 38) as a subgroup of its automorphism group. -/
theorem no_C38_acts_on_Moore57_unconditional
    {V : Type*} [Fintype V] [DecidableEq V]
    {Γ : SimpleGraph V} [DecidableRel Γ.Adj] :
    ¬ Nonempty (C38ActsOnMoore57 V Γ) := by
  rintro ⟨h⟩
  exact h.false_of_raw_action

end Moore57
