import Moore57.FixedPointBasics

namespace Moore57

namespace D19ActsOnMoore57

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- The neighbors of `v` fixed by the rotation `d`. -/
noncomputable def fixedNeighborFinset
    (h : D19ActsOnMoore57 V Γ) (d : ZMod 19) (v : V) : Finset V :=
  (Γ.neighborFinset v).filter fun w => h.rotation d w = w

@[simp] theorem mem_fixedNeighborFinset
    (h : D19ActsOnMoore57 V Γ) (d : ZMod 19) (v w : V) :
    w ∈ h.fixedNeighborFinset d v ↔ Γ.Adj v w ∧ h.rotation d w = w := by
  simp [fixedNeighborFinset, SimpleGraph.mem_neighborFinset]

/-- If `v` is fixed by a rotation, then that rotation permutes the neighbors of `v`. -/
noncomputable def rotationNeighborPerm
    (h : D19ActsOnMoore57 V Γ) (d : ZMod 19) {v : V}
    (hv : h.rotation d v = v) : Equiv.Perm {w : V // Γ.Adj v w} :=
  (h.rotation d).subtypePerm fun w => by
    constructor
    · intro hw
      have hw' : Γ.Adj (h.rotation d v) (h.rotation d w) := by
        simpa [hv] using hw
      exact (h.smul_adj (DihedralGroup.r d) v w).2 hw'
    · intro hw
      have hw' : Γ.Adj (h.rotation d v) (h.rotation d w) :=
        (h.smul_adj (DihedralGroup.r d) v w).1 hw
      simpa [hv] using hw'

theorem card_fixedNeighborFinset_rotation_modEq_degree
    (h : D19ActsOnMoore57 V Γ) (d : ZMod 19) {v : V}
    (hv : h.rotation d v = v) :
    (h.fixedNeighborFinset d v).card ≡ Γ.degree v [MOD 19] := by
  classical
  haveI : Fact (Nat.Prime 19) := ⟨by decide⟩
  let σ := h.rotationNeighborPerm d hv
  have hpow : σ ^ 19 ^ 1 = 1 := by
    ext w
    change ((h.rotation d) ^ 19) (w : V) = w
    simp [h.rotation_pow_nineteen d]
  have hmod := Equiv.Perm.card_compl_support_modEq
    (α := {w : V // Γ.Adj v w}) (p := 19) (n := 1) (σ := σ) hpow
  have hsupport :
      σ.supportᶜ.card = (h.fixedNeighborFinset d v).card := by
    have hsupportCard :
        σ.supportᶜ.card =
          Fintype.card {w : {w : V // Γ.Adj v w} // σ w = w} := by
      have hcomplCard :
          Fintype.card {w : {w : V // Γ.Adj v w} // w ∈ σ.supportᶜ} =
            σ.supportᶜ.card :=
        Fintype.card_ofFinset σ.supportᶜ (by intro w; rfl)
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
        Fintype.card {w : {w : V // Γ.Adj v w} // σ w = w} =
          Fintype.card {w : V // w ∈ h.fixedNeighborFinset d v} := by
      refine Fintype.card_congr ?fixedEquiv
      exact
        { toFun := fun w =>
            ⟨w.1.1, by
              have hwfix : h.rotation d w.1.1 = w.1.1 := by
                simpa [σ, rotationNeighborPerm] using congr_arg Subtype.val w.2
              simp [mem_fixedNeighborFinset, w.1.2, hwfix]⟩
          invFun := fun w =>
            ⟨⟨w.1, (mem_fixedNeighborFinset h d v w.1).1 w.2 |>.1⟩, by
              ext
              simpa [σ, rotationNeighborPerm] using
                ((mem_fixedNeighborFinset h d v w.1).1 w.2 |>.2)⟩
          left_inv := by
            intro w
            ext
            rfl
          right_inv := by
            intro w
            ext
            rfl }
    have hfinsetCard :
        Fintype.card {w : V // w ∈ h.fixedNeighborFinset d v} =
          (h.fixedNeighborFinset d v).card := by
      exact Fintype.card_ofFinset (h.fixedNeighborFinset d v) (by intro w; rfl)
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

theorem card_fixedNeighborFinset_rotation_modEq_zero_of_moore
    (h : D19ActsOnMoore57 V Γ) (d : ZMod 19) {v : V}
    (hv : h.rotation d v = v) :
    (h.fixedNeighborFinset d v).card ≡ 0 [MOD 19] := by
  have hmod := h.card_fixedNeighborFinset_rotation_modEq_degree d hv
  have hdeg : Γ.degree v = 57 := h.isMoore.regular.degree_eq v
  rw [hdeg] at hmod
  exact hmod.trans (by norm_num [Nat.ModEq])

end D19ActsOnMoore57

end Moore57
