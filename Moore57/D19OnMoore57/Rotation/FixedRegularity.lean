import Moore57.D19OnMoore57.Rotation.FixedCardEqOne

namespace Moore57

namespace D19ActsOnMoore57

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- For two non-adjacent fixed vertices `p,q`, deleting their common fixed
neighbor `z` gives an injection from the fixed neighbors of `p` to those of
`q`. -/
theorem fixedNeighborFinset_erase_card_le_of_rotation_one_fixed_of_not_adj
    (h : D19ActsOnMoore57 V Γ) {p q z : V}
    (_hp : h.rotation 1 p = p) (hq : h.rotation 1 q = q)
    (hpq : p ≠ q) (hpq_not_adj : ¬ Γ.Adj p q)
    (hpz : Γ.Adj p z) (hqz : Γ.Adj q z)
    (_hz : h.rotation 1 z = z) :
    ((h.fixedNeighborFinset 1 p).erase z).card ≤
      ((h.fixedNeighborFinset 1 q).erase z).card := by
  classical
  let A := ((h.fixedNeighborFinset 1 p).erase z : Set V)
  let B := ((h.fixedNeighborFinset 1 q).erase z : Set V)
  have hExists : ∀ a : A, ∃ b : V,
      b ∈ (h.fixedNeighborFinset 1 q).erase z ∧ Γ.Adj (a : V) b := by
    intro a
    have haErase : (a : V) ∈ (h.fixedNeighborFinset 1 p).erase z := by
      change (a : V) ∈ ((h.fixedNeighborFinset 1 p).erase z : Set V)
      exact a.property
    have ha_ne_z : (a : V) ≠ z := (Finset.mem_erase.mp haErase).1
    have haN : (a : V) ∈ h.fixedNeighborFinset 1 p :=
      (Finset.mem_erase.mp haErase).2
    have hpa : Γ.Adj p (a : V) := (mem_fixedNeighborFinset h 1 p (a : V)).mp haN |>.1
    have haFixed : h.rotation 1 (a : V) = (a : V) :=
      (mem_fixedNeighborFinset h 1 p (a : V)).mp haN |>.2
    have haq : (a : V) ≠ q := by
      intro haq
      exact hpq_not_adj (by simpa [haq] using hpa)
    have haq_not_adj : ¬ Γ.Adj (a : V) q := by
      intro haqAdj
      exact h.isMoore.no_four_cycle
        (x0 := p) (x1 := (a : V)) (x2 := q) (x3 := z)
        (Γ.ne_of_adj hpa) hpq (Γ.ne_of_adj hpz)
        (Γ.ne_of_adj haqAdj) ha_ne_z (Γ.ne_of_adj hqz)
        hpa haqAdj hqz hpz.symm
    have haSmul : h.smul (DihedralGroup.r (1 : ZMod 19)) (a : V) = (a : V) := by
      simpa [rotation] using haFixed
    have hqSmul : h.smul (DihedralGroup.r (1 : ZMod 19)) q = q := by
      simpa [rotation] using hq
    rcases h.exists_fixed_commonNeighbor_of_not_adj
        (DihedralGroup.r (1 : ZMod 19)) haSmul hqSmul haq haq_not_adj with
      ⟨b, hbFixedSmul, hab, hqb⟩
    have hbFixed : h.rotation 1 b = b := by
      simpa [rotation] using hbFixedSmul
    have hb_ne_z : b ≠ z := by
      intro hbz
      have hza : Γ.Adj z (a : V) := by
        simpa [hbz] using hab.symm
      exact h.isMoore.no_triangle hpz hza hpa.symm
    have hbN : b ∈ h.fixedNeighborFinset 1 q :=
      (mem_fixedNeighborFinset h 1 q b).2 ⟨hqb, hbFixed⟩
    exact ⟨b, Finset.mem_erase.mpr ⟨hb_ne_z, hbN⟩, hab⟩
  let f : A → B := fun a =>
    ⟨Classical.choose (hExists a), by
      change Classical.choose (hExists a) ∈
        ((h.fixedNeighborFinset 1 q).erase z : Set V)
      exact (Classical.choose_spec (hExists a)).1⟩
  have hf_inj : Function.Injective f := by
    intro a₁ a₂ hfa
    apply Subtype.ext
    by_contra ha_ne
    have ha₁Erase : (a₁ : V) ∈ (h.fixedNeighborFinset 1 p).erase z := by
      change (a₁ : V) ∈ ((h.fixedNeighborFinset 1 p).erase z : Set V)
      exact a₁.property
    have ha₂Erase : (a₂ : V) ∈ (h.fixedNeighborFinset 1 p).erase z := by
      change (a₂ : V) ∈ ((h.fixedNeighborFinset 1 p).erase z : Set V)
      exact a₂.property
    have ha₁N : (a₁ : V) ∈ h.fixedNeighborFinset 1 p :=
      (Finset.mem_erase.mp ha₁Erase).2
    have ha₂N : (a₂ : V) ∈ h.fixedNeighborFinset 1 p :=
      (Finset.mem_erase.mp ha₂Erase).2
    have hpa₁ : Γ.Adj p (a₁ : V) :=
      (mem_fixedNeighborFinset h 1 p (a₁ : V)).mp ha₁N |>.1
    have hpa₂ : Γ.Adj p (a₂ : V) :=
      (mem_fixedNeighborFinset h 1 p (a₂ : V)).mp ha₂N |>.1
    have ha₁b : Γ.Adj (a₁ : V) (f a₁ : V) :=
      (Classical.choose_spec (hExists a₁)).2
    have ha₂b' : Γ.Adj (a₂ : V) (f a₂ : V) :=
      (Classical.choose_spec (hExists a₂)).2
    have hbEq : (f a₁ : V) = (f a₂ : V) := congrArg Subtype.val hfa
    have hba₂ : Γ.Adj (f a₁ : V) (a₂ : V) := by
      have : Γ.Adj (a₂ : V) (f a₁ : V) := by
        simpa [hbEq] using ha₂b'
      exact this.symm
    have hpb : p ≠ (f a₁ : V) := by
      intro hpb
      have hbErase : (f a₁ : V) ∈ (h.fixedNeighborFinset 1 q).erase z := by
        change (f a₁ : V) ∈ ((h.fixedNeighborFinset 1 q).erase z : Set V)
        exact (f a₁).property
      have hbN : (f a₁ : V) ∈ h.fixedNeighborFinset 1 q :=
        (Finset.mem_erase.mp hbErase).2
      have hqb : Γ.Adj q (f a₁ : V) :=
        (mem_fixedNeighborFinset h 1 q (f a₁ : V)).mp hbN |>.1
      exact hpq_not_adj (by simpa [← hpb] using hqb.symm)
    exact h.isMoore.no_four_cycle
      (x0 := p) (x1 := (a₁ : V)) (x2 := (f a₁ : V)) (x3 := (a₂ : V))
      (Γ.ne_of_adj hpa₁) hpb (Γ.ne_of_adj hpa₂)
      (Γ.ne_of_adj ha₁b) ha_ne (Γ.ne_of_adj hba₂)
      hpa₁ ha₁b hba₂ hpa₂.symm
  have hcard : Fintype.card A ≤ Fintype.card B :=
    Fintype.card_le_of_injective f hf_inj
  have hAcard : Fintype.card A = ((h.fixedNeighborFinset 1 p).erase z).card := by
    change Fintype.card {w : V // w ∈
      (((h.fixedNeighborFinset 1 p).erase z : Finset V) : Set V)} =
        ((h.fixedNeighborFinset 1 p).erase z).card
    exact Fintype.card_ofFinset ((h.fixedNeighborFinset 1 p).erase z) (by intro w; rfl)
  have hBcard : Fintype.card B = ((h.fixedNeighborFinset 1 q).erase z).card := by
    change Fintype.card {w : V // w ∈
      (((h.fixedNeighborFinset 1 q).erase z : Finset V) : Set V)} =
        ((h.fixedNeighborFinset 1 q).erase z).card
    exact Fintype.card_ofFinset ((h.fixedNeighborFinset 1 q).erase z) (by intro w; rfl)
  omega

/-- Non-adjacent vertices fixed by rotation `1` have the same degree in the
fixed induced graph. -/
theorem fixedNeighborFinset_card_eq_of_rotation_one_fixed_of_not_adj
    (h : D19ActsOnMoore57 V Γ) {x y : V}
    (hx : h.rotation 1 x = x) (hy : h.rotation 1 y = y)
    (hxy : x ≠ y) (hxy_not_adj : ¬ Γ.Adj x y) :
    (h.fixedNeighborFinset 1 x).card = (h.fixedNeighborFinset 1 y).card := by
  classical
  have hxSmul : h.smul (DihedralGroup.r (1 : ZMod 19)) x = x := by
    simpa [rotation] using hx
  have hySmul : h.smul (DihedralGroup.r (1 : ZMod 19)) y = y := by
    simpa [rotation] using hy
  rcases h.exists_fixed_commonNeighbor_of_not_adj
      (DihedralGroup.r (1 : ZMod 19)) hxSmul hySmul hxy hxy_not_adj with
    ⟨z, hzSmul, hxz, hyz⟩
  have hz : h.rotation 1 z = z := by
    simpa [rotation] using hzSmul
  have hzNx : z ∈ h.fixedNeighborFinset 1 x :=
    (mem_fixedNeighborFinset h 1 x z).2 ⟨hxz, hz⟩
  have hzNy : z ∈ h.fixedNeighborFinset 1 y :=
    (mem_fixedNeighborFinset h 1 y z).2 ⟨hyz, hz⟩
  have hle :
      ((h.fixedNeighborFinset 1 x).erase z).card ≤
        ((h.fixedNeighborFinset 1 y).erase z).card :=
    h.fixedNeighborFinset_erase_card_le_of_rotation_one_fixed_of_not_adj
      hx hy hxy hxy_not_adj hxz hyz hz
  have hge :
      ((h.fixedNeighborFinset 1 y).erase z).card ≤
        ((h.fixedNeighborFinset 1 x).erase z).card :=
    h.fixedNeighborFinset_erase_card_le_of_rotation_one_fixed_of_not_adj
      hy hx hxy.symm (by intro hyx; exact hxy_not_adj hyx.symm) hyz hxz hz
  have hxErase :
      ((h.fixedNeighborFinset 1 x).erase z).card + 1 =
        (h.fixedNeighborFinset 1 x).card :=
    Finset.card_erase_add_one hzNx
  have hyErase :
      ((h.fixedNeighborFinset 1 y).erase z).card + 1 =
        (h.fixedNeighborFinset 1 y).card :=
    Finset.card_erase_add_one hzNy
  omega

/-- Under `fixedVertexCount (rotation 1) ≠ 1`, a fixed vertex has a fixed
neighbor different from any prescribed vertex. -/
theorem exists_fixedNeighbor_ne_of_rotation_one_fixed_of_count_ne_one
    (h : D19ActsOnMoore57 V Γ)
    (hcount : fixedVertexCount (h.rotation 1) ≠ 1)
    {x y : V} (hx : h.rotation 1 x = x) :
    ∃ z, z ∈ h.fixedNeighborFinset 1 x ∧ z ≠ y := by
  classical
  have hge : 19 ≤ (h.fixedNeighborFinset 1 x).card :=
    h.card_fixedNeighborFinset_ge_nineteen_of_fixedVertexCount_ne_one 1 hx hcount
  have hone : 1 < (h.fixedNeighborFinset 1 x).card := by omega
  rcases Finset.one_lt_card_iff.mp hone with ⟨a, b, ha, hb, hab⟩
  by_cases hay : a = y
  · exact ⟨b, hb, by
      intro hby
      exact hab (hay.trans hby.symm)⟩
  · exact ⟨a, ha, hay⟩

/-- Rotation-`1` fixed vertices have constant fixed-neighbor degree whenever the
rotation has fixed count different from `1`. -/
theorem fixedNeighborFinset_card_eq_of_rotation_one_fixed_of_count_ne_one
    (h : D19ActsOnMoore57 V Γ)
    (hcount : fixedVertexCount (h.rotation 1) ≠ 1)
    {x y : V} (hx : h.rotation 1 x = x) (hy : h.rotation 1 y = y) :
    (h.fixedNeighborFinset 1 x).card = (h.fixedNeighborFinset 1 y).card := by
  classical
  by_cases hxy : x = y
  · subst y
    rfl
  by_cases hxyAdj : Γ.Adj x y
  · rcases h.exists_fixedNeighbor_ne_of_rotation_one_fixed_of_count_ne_one
        hcount hx with ⟨a, haN, ha_ne_y⟩
    rcases h.exists_fixedNeighbor_ne_of_rotation_one_fixed_of_count_ne_one
        hcount hy with ⟨b, hbN, hb_ne_x⟩
    have hxa : Γ.Adj x a := (mem_fixedNeighborFinset h 1 x a).mp haN |>.1
    have haFixed : h.rotation 1 a = a := (mem_fixedNeighborFinset h 1 x a).mp haN |>.2
    have hyb : Γ.Adj y b := (mem_fixedNeighborFinset h 1 y b).mp hbN |>.1
    have hbFixed : h.rotation 1 b = b := (mem_fixedNeighborFinset h 1 y b).mp hbN |>.2
    have hay_not_adj : ¬ Γ.Adj a y := by
      intro hay
      exact h.isMoore.no_triangle hxyAdj hay.symm hxa.symm
    have hxb_not_adj : ¬ Γ.Adj x b := by
      intro hxb
      exact h.isMoore.no_triangle hxyAdj hyb hxb.symm
    have hab_not_adj : ¬ Γ.Adj a b := by
      intro hab
      exact h.isMoore.no_four_cycle
        (x0 := x) (x1 := a) (x2 := b) (x3 := y)
        (Γ.ne_of_adj hxa) (by
          intro hxbEq
          exact hb_ne_x hxbEq.symm)
        hxy
        (Γ.ne_of_adj hab) (by
          intro hayEq
          exact ha_ne_y hayEq)
        (Γ.ne_of_adj hyb).symm
        hxa hab hyb.symm hxyAdj.symm
    have hya :
        (h.fixedNeighborFinset 1 y).card = (h.fixedNeighborFinset 1 a).card := by
      exact h.fixedNeighborFinset_card_eq_of_rotation_one_fixed_of_not_adj
        hy haFixed (by intro hyaEq; exact ha_ne_y hyaEq.symm)
        (by intro hyaAdj; exact hay_not_adj hyaAdj.symm)
    have habEq :
        (h.fixedNeighborFinset 1 a).card = (h.fixedNeighborFinset 1 b).card :=
      h.fixedNeighborFinset_card_eq_of_rotation_one_fixed_of_not_adj
        haFixed hbFixed (by
          intro habEq
          exact h.isMoore.no_triangle hxyAdj (by simpa [← habEq] using hyb) hxa.symm)
        hab_not_adj
    have hxb :
        (h.fixedNeighborFinset 1 x).card = (h.fixedNeighborFinset 1 b).card :=
      h.fixedNeighborFinset_card_eq_of_rotation_one_fixed_of_not_adj
        hx hbFixed (by intro hxbEq; exact hb_ne_x hxbEq.symm) hxb_not_adj
    exact hxb.trans (habEq.symm.trans hya.symm)
  · exact h.fixedNeighborFinset_card_eq_of_rotation_one_fixed_of_not_adj
      hx hy hxy hxyAdj

/-- Rotation by `1` has exactly one fixed vertex. -/
theorem rotation_one_fixedVertexCount_eq_one
    (h : D19ActsOnMoore57 V Γ) :
    fixedVertexCount (h.rotation 1) = 1 :=
  h.rotation_one_fixedVertexCount_eq_one_of_regular_if_not_one (by
    intro hcount
    have hpos : 0 < Fintype.card (fixedVertexSet (h.rotation 1)) := by
      simpa [fixedVertexCount_eq_card_fixedVertexSet] using
        h.fixedVertexCount_rotation_pos 1
    rcases Fintype.card_pos_iff.mp hpos with ⟨x⟩
    let k := (h.fixedNeighborFinset 1 (x : V)).card
    refine ⟨k, ?_, ?_⟩
    · intro y
      exact
        (h.fixedNeighborFinset_card_eq_of_rotation_one_fixed_of_count_ne_one
          hcount y.property x.property).trans rfl
    · exact h.fixedNeighborFinset_card_eq_19_or_38_or_57
        1 hcount x.property)

/-- Every nontrivial rotation has exactly one fixed vertex. -/
theorem rotation_fixed_card_eq_one
    (h : D19ActsOnMoore57 V Γ) {d : ZMod 19} (hd : d ≠ 0) :
    fixedVertexCount (h.rotation d) = 1 := by
  rw [h.fixedVertexCount_rotation_eq_one hd]
  exact h.rotation_one_fixedVertexCount_eq_one

end D19ActsOnMoore57

end Moore57
