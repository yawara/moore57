import Moore57.Foundations.GroupAction.BranchFiberAction

namespace Moore57

namespace D19ActsOnMoore57

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- The vertices in a branch fiber that are fixed by a rotation. -/
noncomputable def fixedBranchFiberFinset
    (h : D19ActsOnMoore57 V Γ) (d : ZMod 19) (u b : V) : Finset V :=
  (branchFiber Γ u b).filter fun x => h.rotation d x = x

@[simp] theorem mem_fixedBranchFiberFinset
    (h : D19ActsOnMoore57 V Γ) (d : ZMod 19) (u b x : V) :
    x ∈ h.fixedBranchFiberFinset d u b ↔
      x ∈ branchFiber Γ u b ∧ h.rotation d x = x := by
  simp [fixedBranchFiberFinset]

/-- If a rotation fixes the center and the branch vertex, then it permutes that branch fiber. -/
noncomputable def rotationBranchFiberPerm
    (h : D19ActsOnMoore57 V Γ) (d : ZMod 19) {u b : V}
    (hu : h.rotation d u = u) (hb : h.rotation d b = b) :
    Equiv.Perm {x : V // x ∈ branchFiber Γ u b} :=
  (h.rotation d).subtypePerm fun x => by
    simpa [hb] using h.rotation_mem_branchFiber_iff d (u := u) (b := b) (x := x) hu

@[simp] theorem rotationBranchFiberPerm_apply_val
    (h : D19ActsOnMoore57 V Γ) (d : ZMod 19) {u b : V}
    (hu : h.rotation d u = u) (hb : h.rotation d b = b)
    (x : {x : V // x ∈ branchFiber Γ u b}) :
    (h.rotationBranchFiberPerm d hu hb x : V) = h.rotation d x :=
  rfl

theorem rotationBranchFiberPerm_apply_eq
    (h : D19ActsOnMoore57 V Γ) (d : ZMod 19) {u b : V}
    (hu : h.rotation d u = u) (hb : h.rotation d b = b)
    (x : {x : V // x ∈ branchFiber Γ u b}) :
    h.rotationBranchFiberPerm d hu hb x =
      ⟨h.rotation d x, by
        have hx' :
            h.rotation d (x : V) ∈ branchFiber Γ u (h.rotation d b) :=
          (h.rotation_mem_branchFiber_iff d (u := u) (b := b) (x := x) hu).2 x.property
        simpa [hb] using hx'⟩ := by
  ext
  rfl

theorem card_fixedBranchFiberFinset_eq_support_compl_card
    (h : D19ActsOnMoore57 V Γ) (d : ZMod 19) {u b : V}
    (hu : h.rotation d u = u) (hb : h.rotation d b = b) :
    (h.fixedBranchFiberFinset d u b).card =
      (h.rotationBranchFiberPerm d hu hb).supportᶜ.card := by
  classical
  let σ := h.rotationBranchFiberPerm d hu hb
  have hsupportCard :
      σ.supportᶜ.card =
        Fintype.card {x : {x : V // x ∈ branchFiber Γ u b} // σ x = x} := by
    have hcomplCard :
        Fintype.card {x : {x : V // x ∈ branchFiber Γ u b} // x ∈ σ.supportᶜ} =
          σ.supportᶜ.card :=
      Fintype.card_ofFinset σ.supportᶜ (by intro x; rfl)
    refine hcomplCard.symm.trans (Fintype.card_congr ?supportEquiv)
    exact
      { toFun := fun x => ⟨x.1, by
          have hxnot : x.1 ∉ σ.support := Finset.mem_compl.mp x.2
          by_contra hxne
          exact hxnot ((Equiv.Perm.mem_support).2 hxne)⟩
        invFun := fun x => ⟨x.1, by
          exact Finset.mem_compl.mpr (by
            intro hxmem
            exact (Equiv.Perm.mem_support.mp hxmem) x.2)⟩
        left_inv := by
          intro x
          rfl
        right_inv := by
          intro x
          rfl }
  have hfixedCard :
      Fintype.card {x : {x : V // x ∈ branchFiber Γ u b} // σ x = x} =
        Fintype.card {x : V // x ∈ h.fixedBranchFiberFinset d u b} := by
    refine Fintype.card_congr ?fixedEquiv
    exact
      { toFun := fun x =>
          ⟨x.1.1, by
            have hxfix : h.rotation d x.1.1 = x.1.1 := by
              simpa [σ, rotationBranchFiberPerm] using congr_arg Subtype.val x.2
            simp [mem_fixedBranchFiberFinset, x.1.2, hxfix]⟩
        invFun := fun x =>
          ⟨⟨x.1, (mem_fixedBranchFiberFinset h d u b x.1).1 x.2 |>.1⟩, by
            ext
            simpa [σ, rotationBranchFiberPerm] using
              ((mem_fixedBranchFiberFinset h d u b x.1).1 x.2 |>.2)⟩
        left_inv := by
          intro x
          ext
          rfl
        right_inv := by
          intro x
          ext
          rfl }
  have hfinsetCard :
      Fintype.card {x : V // x ∈ h.fixedBranchFiberFinset d u b} =
        (h.fixedBranchFiberFinset d u b).card :=
    Fintype.card_ofFinset (h.fixedBranchFiberFinset d u b) (by intro x; rfl)
  exact (hsupportCard.trans (hfixedCard.trans hfinsetCard)).symm

/-- Fixed points of a rotation on a fixed branch fiber are congruent to the fiber size modulo 19. -/
theorem card_fixedBranchFiberFinset_rotation_modEq_branchFiber_card
    (h : D19ActsOnMoore57 V Γ) (d : ZMod 19) {u b : V}
    (hu : h.rotation d u = u) (hb : h.rotation d b = b) :
    (h.fixedBranchFiberFinset d u b).card ≡ (branchFiber Γ u b).card [MOD 19] := by
  classical
  haveI : Fact (Nat.Prime 19) := ⟨by decide⟩
  let σ := h.rotationBranchFiberPerm d hu hb
  have hpow : σ ^ 19 ^ 1 = 1 := by
    ext x
    change ((h.rotation d) ^ 19) (x : V) = x
    simp [h.rotation_pow_nineteen d]
  have hmod := Equiv.Perm.card_compl_support_modEq
    (α := {x : V // x ∈ branchFiber Γ u b}) (p := 19) (n := 1) (σ := σ) hpow
  have hfiberCard :
      Fintype.card {x : V // x ∈ branchFiber Γ u b} = (branchFiber Γ u b).card :=
    Fintype.card_ofFinset (branchFiber Γ u b) (by intro x; rfl)
  have hfixed :=
    h.card_fixedBranchFiberFinset_eq_support_compl_card d hu hb
  calc
    (h.fixedBranchFiberFinset d u b).card ≡ σ.supportᶜ.card [MOD 19] := by
      rw [hfixed]
    _ ≡ Fintype.card {x : V // x ∈ branchFiber Γ u b} [MOD 19] := hmod
    _ ≡ (branchFiber Γ u b).card [MOD 19] := by
      rw [hfiberCard]

/-- In a Moore57 graph, fixed points of the induced branch-fiber rotation are `56 mod 19`. -/
theorem card_fixedBranchFiberFinset_rotation_modEq_fiftySix
    (h : D19ActsOnMoore57 V Γ) (d : ZMod 19) {u b : V}
    (hu : h.rotation d u = u) (hb : h.rotation d b = b) (hub : Γ.Adj u b) :
    (h.fixedBranchFiberFinset d u b).card ≡ 56 [MOD 19] := by
  have hmod := h.card_fixedBranchFiberFinset_rotation_modEq_branchFiber_card d hu hb
  rw [h.isMoore.branchFiber_card hub] at hmod
  exact hmod

end D19ActsOnMoore57

end Moore57
