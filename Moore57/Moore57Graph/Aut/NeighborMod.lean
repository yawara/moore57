import Moore57.Moore57Graph.Moore57Definition
import Moore57.Foundations.GroupAction.FixedPoints
import Mathlib.GroupTheory.Perm.Cycle.Type

/-!
# Modular fixed-neighbour count for a Moore57 automorphism (Tier 2)

Abstract version of `D19OnMoore57/Fixed/NeighborCounts.lean`. For any
permutation `σ : Equiv.Perm V` that is a graph automorphism of a Moore57
graph and satisfies `σ ^ 19 = 1`, the number of σ-fixed neighbours of any
σ-fixed vertex is divisible by `19`.

The proof reduces to `Equiv.Perm.card_compl_support_modEq`, the mathlib fact
that fixing the index set of a `p`-power permutation gives a count ≡ |V|
mod `p`.
-/

namespace Moore57

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- Neighbours of `v` that are fixed by an automorphism `σ`. -/
def autFixedNeighborFinset
    (Γ : SimpleGraph V) [DecidableRel Γ.Adj]
    (σ : V → V) (v : V) : Finset V :=
  (Γ.neighborFinset v).filter fun w => σ w = w

@[simp] theorem mem_autFixedNeighborFinset
    (σ : V → V) {v w : V} :
    w ∈ autFixedNeighborFinset Γ σ v ↔ Γ.Adj v w ∧ σ w = w := by
  simp [autFixedNeighborFinset, SimpleGraph.mem_neighborFinset]

/-- If a vertex `v` is fixed by an automorphism `σ`, the restriction of `σ` to
the neighbours of `v` is a well-defined permutation. -/
noncomputable def autNeighborPerm
    (σ : Equiv.Perm V)
    (smul_adj : ∀ v w : V, Γ.Adj v w ↔ Γ.Adj (σ v) (σ w))
    {v : V} (hv : σ v = v) : Equiv.Perm {w : V // Γ.Adj v w} :=
  σ.subtypePerm fun w => by
    constructor
    · intro hw
      have hw' : Γ.Adj (σ v) (σ w) := by
        simpa [hv] using hw
      exact (smul_adj v w).2 hw'
    · intro hw
      have hw' : Γ.Adj (σ v) (σ w) :=
        (smul_adj v w).1 hw
      simpa [hv] using hw'

/-- For an automorphism `σ` of order dividing `19`, the number of σ-fixed
neighbours of a σ-fixed vertex is congruent to the degree mod `19`. -/
theorem aut_card_fixedNeighborFinset_modEq_degree
    (σ : Equiv.Perm V)
    (smul_adj : ∀ v w : V, Γ.Adj v w ↔ Γ.Adj (σ v) (σ w))
    (pow_nineteen : σ ^ 19 = 1)
    {v : V} (hv : σ v = v) :
    (autFixedNeighborFinset Γ σ v).card ≡ Γ.degree v [MOD 19] := by
  classical
  haveI : Fact (Nat.Prime 19) := ⟨by decide⟩
  let τ := autNeighborPerm σ smul_adj hv
  have hpow : τ ^ 19 ^ 1 = 1 := by
    ext w
    change (σ ^ 19) (w : V) = w
    simp [pow_nineteen]
  have hmod := Equiv.Perm.card_compl_support_modEq
    (α := {w : V // Γ.Adj v w}) (p := 19) (n := 1) (σ := τ) hpow
  have hsupport :
      τ.supportᶜ.card = (autFixedNeighborFinset Γ σ v).card := by
    have hsupportCard :
        τ.supportᶜ.card =
          Fintype.card {w : {w : V // Γ.Adj v w} // τ w = w} := by
      have hcomplCard :
          Fintype.card {w : {w : V // Γ.Adj v w} // w ∈ τ.supportᶜ} =
            τ.supportᶜ.card :=
        Fintype.card_ofFinset τ.supportᶜ (by intro w; rfl)
      refine hcomplCard.symm.trans (Fintype.card_congr ?supportEquiv)
      exact
        { toFun := fun w => ⟨w.1, by simpa [Equiv.Perm.support] using w.2⟩
          invFun := fun w => ⟨w.1, by simpa [Equiv.Perm.support] using w.2⟩
          left_inv := by
            intro w
            rfl
          right_inv := by
            intro w
            rfl }
    have hfixedCard :
        Fintype.card {w : {w : V // Γ.Adj v w} // τ w = w} =
          Fintype.card {w : V // w ∈ autFixedNeighborFinset Γ σ v} := by
      refine Fintype.card_congr ?fixedEquiv
      exact
        { toFun := fun w =>
            ⟨w.1.1, by
              have hwfix : σ w.1.1 = w.1.1 := by
                simpa [τ, autNeighborPerm] using congr_arg Subtype.val w.2
              simp [mem_autFixedNeighborFinset, w.1.2, hwfix]⟩
          invFun := fun w =>
            ⟨⟨w.1, (mem_autFixedNeighborFinset σ).1 w.2 |>.1⟩, by
              ext
              simpa [τ, autNeighborPerm] using
                ((mem_autFixedNeighborFinset σ).1 w.2 |>.2)⟩
          left_inv := by
            intro w
            ext
            rfl
          right_inv := by
            intro w
            ext
            rfl }
    have hfinsetCard :
        Fintype.card {w : V // w ∈ autFixedNeighborFinset Γ σ v} =
          (autFixedNeighborFinset Γ σ v).card := by
      exact Fintype.card_ofFinset (autFixedNeighborFinset Γ σ v) (by intro w; rfl)
    exact hsupportCard.trans (hfixedCard.trans hfinsetCard)
  have hdegree :
      Fintype.card {w : V // Γ.Adj v w} = Γ.degree v := by
    rw [← SimpleGraph.card_neighborFinset_eq_degree]
    have hneighborCard :
        Fintype.card {w : V // w ∈ Γ.neighborFinset v} = (Γ.neighborFinset v).card :=
      Fintype.card_ofFinset (Γ.neighborFinset v) (by intro w; rfl)
    refine (Fintype.card_congr ?neighborEquiv).trans hneighborCard
    exact
      { toFun := fun w =>
          ⟨w.1, (SimpleGraph.mem_neighborFinset (G := Γ) (v := v) w.1).2 w.2⟩
        invFun := fun w =>
          ⟨w.1, (SimpleGraph.mem_neighborFinset (G := Γ) (v := v) w.1).1 w.2⟩
        left_inv := by
          intro w
          rfl
        right_inv := by
          intro w
          rfl }
  simpa [hsupport, hdegree] using hmod

/-- For an automorphism `σ` of a Moore57 graph with `σ ^ 19 = 1`, the number of
σ-fixed neighbours of a σ-fixed vertex is divisible by `19`. -/
theorem aut_card_fixedNeighborFinset_modEq_zero
    (hΓ : IsMoore57 Γ)
    (σ : Equiv.Perm V)
    (smul_adj : ∀ v w : V, Γ.Adj v w ↔ Γ.Adj (σ v) (σ w))
    (pow_nineteen : σ ^ 19 = 1)
    {v : V} (hv : σ v = v) :
    (autFixedNeighborFinset Γ σ v).card ≡ 0 [MOD 19] := by
  have hmod := aut_card_fixedNeighborFinset_modEq_degree σ smul_adj pow_nineteen hv
  have hdeg : Γ.degree v = 57 := hΓ.regular.degree_eq v
  rw [hdeg] at hmod
  exact hmod.trans (by norm_num [Nat.ModEq])

end Moore57
