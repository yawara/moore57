import Moore57.D19OnMoore57.Reflection.InvolutionFixedSetStarFromActionBoundary

/-!
# Fixed-neighbor degree parity for involutions

An involutive graph automorphism preserving a fixed vertex acts on that
vertex's neighbor set by an involution.  Hence non-fixed neighbors are paired,
so the number of fixed neighbors has the same parity as the ambient degree.
-/

namespace Moore57

open Finset

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- Ambient neighbors of `v` fixed by a permutation `σ`. -/
def fixedNeighborFinsetOf
    (Γ : SimpleGraph V) [DecidableRel Γ.Adj]
    (σ : Equiv.Perm V) (v : V) : Finset V :=
  (Γ.neighborFinset v).filter fun w => σ w = w

@[simp] theorem mem_fixedNeighborFinsetOf
    (σ : Equiv.Perm V) (v w : V) :
    w ∈ fixedNeighborFinsetOf Γ σ v ↔ Γ.Adj v w ∧ σ w = w := by
  simp [fixedNeighborFinsetOf, SimpleGraph.mem_neighborFinset]

/-- For an involutive graph automorphism fixing `v`, the fixed-neighbor count
has the same parity as the degree of `v`. -/
theorem fixedNeighborFinsetOf_card_modEq_degree_of_involutive_automorphism
    (σ : Equiv.Perm V)
    (hσ : Function.Involutive σ)
    (haut : ∀ x y : V, Γ.Adj x y ↔ Γ.Adj (σ x) (σ y))
    {v : V} (hv : σ v = v) :
    (fixedNeighborFinsetOf Γ σ v).card ≡ Γ.degree v [MOD 2] := by
  classical
  let N := {w : V // Γ.Adj v w}
  let τ : Equiv.Perm N :=
    { toFun := fun w =>
        ⟨σ w, by
          have hAdj : Γ.Adj (σ v) (σ w) := (haut v w).mp w.property
          simpa [hv] using hAdj⟩
      invFun := fun w =>
        ⟨σ w, by
          have hAdj : Γ.Adj (σ v) (σ w) := (haut v w).mp w.property
          simpa [hv] using hAdj⟩
      left_inv := by
        intro w
        ext
        exact hσ w
      right_inv := by
        intro w
        ext
        exact hσ w }
  have hpow : τ ^ 2 ^ 1 = 1 := by
    ext w
    change (τ (τ w) : V) = (w : V)
    exact hσ w
  haveI : Fact (Nat.Prime 2) := ⟨by decide⟩
  have hmod := Equiv.Perm.card_compl_support_modEq
    (p := 2) (n := 1) (σ := τ) hpow
  have hsupport :
      τ.supportᶜ.card = (fixedNeighborFinsetOf Γ σ v).card := by
    have hsupportCard :
        τ.supportᶜ.card =
          Fintype.card {w : N // τ w = w} := by
      have hcomplCard :
          Fintype.card {w : N // w ∈ τ.supportᶜ} =
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
        Fintype.card {w : N // τ w = w} =
          Fintype.card {w : V // w ∈ fixedNeighborFinsetOf Γ σ v} := by
      refine Fintype.card_congr ?fixedEquiv
      exact
        { toFun := fun w =>
            ⟨w.1.1, by
              have hwfix : σ w.1.1 = w.1.1 := by
                simpa [τ] using congrArg Subtype.val w.2
              simp [fixedNeighborFinsetOf, SimpleGraph.mem_neighborFinset,
                w.1.2, hwfix]⟩
          invFun := fun w =>
            ⟨⟨w.1, (mem_fixedNeighborFinsetOf (Γ := Γ) σ v w.1).1 w.2 |>.1⟩, by
              ext
              simpa [τ] using
                ((mem_fixedNeighborFinsetOf (Γ := Γ) σ v w.1).1 w.2 |>.2)⟩
          left_inv := by
            intro w
            ext
            rfl
          right_inv := by
            intro w
            ext
            rfl }
    have hfinsetCard :
        Fintype.card {w : V // w ∈ fixedNeighborFinsetOf Γ σ v} =
          (fixedNeighborFinsetOf Γ σ v).card :=
      Fintype.card_ofFinset (fixedNeighborFinsetOf Γ σ v) (by intro w; rfl)
    exact hsupportCard.trans (hfixedCard.trans hfinsetCard)
  have hdegree :
      Fintype.card N = Γ.degree v := by
    rw [← SimpleGraph.card_neighborFinset_eq_degree]
    have hneighborCard :
        Fintype.card {w : V // w ∈ Γ.neighborFinset v} =
          (Γ.neighborFinset v).card :=
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

/-- Odd-degree form of
`fixedNeighborFinsetOf_card_modEq_degree_of_involutive_automorphism`. -/
theorem fixedNeighborFinsetOf_card_odd_of_involutive_automorphism
    (σ : Equiv.Perm V)
    (hσ : Function.Involutive σ)
    (haut : ∀ x y : V, Γ.Adj x y ↔ Γ.Adj (σ x) (σ y))
    {v : V} (hv : σ v = v)
    (hdeg : Odd (Γ.degree v)) :
    Odd (fixedNeighborFinsetOf Γ σ v).card := by
  rw [Nat.odd_iff] at hdeg ⊢
  have hdegMod : Γ.degree v ≡ 1 [MOD 2] := by
    rw [Nat.ModEq]
    simpa using hdeg
  have hfixedMod :
      (fixedNeighborFinsetOf Γ σ v).card ≡ 1 [MOD 2] :=
    (fixedNeighborFinsetOf_card_modEq_degree_of_involutive_automorphism
      (Γ := Γ) σ hσ haut hv).trans hdegMod
  simpa [Nat.ModEq] using hfixedMod

/-- In a Moore57 graph, an involutive graph automorphism fixes an odd number of
neighbors of every fixed vertex. -/
theorem fixedNeighborFinsetOf_card_odd_of_moore57
    (hΓ : IsMoore57 Γ)
    (σ : Equiv.Perm V)
    (hσ : Function.Involutive σ)
    (haut : ∀ x y : V, Γ.Adj x y ↔ Γ.Adj (σ x) (σ y))
    {v : V} (hv : σ v = v) :
    Odd (fixedNeighborFinsetOf Γ σ v).card :=
  fixedNeighborFinsetOf_card_odd_of_involutive_automorphism
    (Γ := Γ) σ hσ haut hv (by
      rw [hΓ.regular.degree_eq v]
      norm_num)

namespace D19ActsOnMoore57

variable {h : D19ActsOnMoore57 V Γ}

/-- Reflection-specialized parity for the filtered neighbor finset. -/
theorem reflection_fixedNeighborFinsetOf_card_modEq_degree
    (k : ZMod 19) (v : reflectionFixedVertex h k) :
    (fixedNeighborFinsetOf Γ (h.smulEquiv (DihedralGroup.sr k)) (v : V)).card
      ≡ Γ.degree (v : V) [MOD 2] :=
  fixedNeighborFinsetOf_card_modEq_degree_of_involutive_automorphism
    (Γ := Γ) (h.smulEquiv (DihedralGroup.sr k))
    (h.reflection_smulEquiv_involutive k)
    (h.reflection_smulEquiv_automorphism k)
    v.property

/-- Reflection-specialized parity in the existing action-level finset
`reflectionFixedNeighborFinset`. -/
theorem reflectionFixedNeighborFinset_card_modEq_degree
    (k : ZMod 19) (v : reflectionFixedVertex h k) :
    (reflectionFixedNeighborFinset h k (v : V)).card
      ≡ Γ.degree (v : V) [MOD 2] := by
  simpa [reflectionFixedNeighborFinset, fixedNeighborFinsetOf] using
    h.reflection_fixedNeighborFinsetOf_card_modEq_degree k v

/-- In a Moore57 action, a reflection fixes an odd number of neighbors of every
fixed vertex. -/
theorem reflectionFixedNeighborFinset_card_odd
    (k : ZMod 19) (v : reflectionFixedVertex h k) :
    Odd (reflectionFixedNeighborFinset h k (v : V)).card := by
  rw [Nat.odd_iff]
  have hmod := h.reflectionFixedNeighborFinset_card_modEq_degree k v
  have hdeg : Γ.degree (v : V) % 2 = 1 := by
    rw [h.isMoore.regular.degree_eq (v : V)]
  have hdegMod : Γ.degree (v : V) ≡ 1 [MOD 2] := by
    rw [Nat.ModEq]
    simpa using hdeg
  have hfixedMod :
      (reflectionFixedNeighborFinset h k (v : V)).card ≡ 1 [MOD 2] :=
    hmod.trans hdegMod
  simpa [Nat.ModEq] using hfixedMod

/-- Equivalent induced-degree statement for the fixed induced reflection graph. -/
theorem fixedInducedGraph_reflection_degree_odd
    (k : ZMod 19) (v : reflectionFixedVertex h k) :
    Odd ((h.fixedInducedGraph (DihedralGroup.sr k)).degree v) := by
  have hdegree :=
    h.fixedInducedGraph_degree_eq_fixedNeighborFinset_card
      (DihedralGroup.sr k) v
  rw [hdegree]
  simpa [reflectionFixedNeighborFinset] using
    h.reflectionFixedNeighborFinset_card_odd k v

end D19ActsOnMoore57

end

end Moore57
