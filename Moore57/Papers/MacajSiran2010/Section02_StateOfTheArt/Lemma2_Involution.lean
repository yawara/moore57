import Moore57.Moore57Graph.Aut.InvolutionCandidates
import Moore57.Moore57Graph.Aut.InvolutionFixIsK155
import Moore57.Papers.CameronCh3.Section07_Automorphisms
import Mathlib.GroupTheory.GroupAction.Basic

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Mačaj–Širáň 2010, §2, Lemma 2

> Let `x` be an involutory automorphism of Γ. Then `a₀(x) = 56` and
> `a₁(x) = 112`. Consequently, the order of `Aut(Γ)` is not divisible by 4.

* `lem2_involution_a0`  — wrapped from `aut_involution_fixedVertexCount_eq_56`
  (Cameron's Theorem 3.13 / Higman, fully proved in
  `Moore57.Moore57Graph.Aut.InvolutionFixIsK155`).
* `lem2_involution_a1` — `a₁(x) = 112`. [deferred-heavy]
  The geometric formula `a₁ = 3250 − 58·a₀ + 2·|E(Fix)|` lives in
  `Moore57.Moore57Graph.InvolutionEdgeCountFormula`; combined with
  `|Fix| = 56` and `|E(Fix)| = 55` (K₁,₅₅ has 55 edges) gives 112.
* `lem2_four_not_dvd_aut` — `4 ∤ |Aut(Γ)|`. [deferred-heavy]
-/

open Moore57

namespace Moore57.Papers.MacajSiran2010.S2

variable {V : Type*} [Fintype V] [DecidableEq V]
  {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- Convert `σ ^ 2 = 1` to `Function.Involutive σ`. -/
private theorem _involutive_of_sq_eq_one {σ : Equiv.Perm V} (hσ : σ ^ 2 = 1) :
    Function.Involutive σ := fun x => by
  have h := congrArg (fun (f : Equiv.Perm V) => f x) hσ
  simpa [pow_two, Equiv.Perm.mul_apply] using h

/-- **Lemma 2 (involution `a₀ = 56`).**
The number of fixed points of any involutory automorphism `σ` (with `σ ≠ 1`)
of a Moore57 graph equals 56. -/
theorem lem2_involution_a0 (hΓ : IsMoore57 Γ) (σ : Equiv.Perm V)
    (hσ : σ ^ 2 = 1) (hne : σ ≠ 1)
    (hAut : ∀ a b, Γ.Adj a b ↔ Γ.Adj (σ a) (σ b)) :
    fixedVertexCount σ = 56 :=
  aut_involution_fixedVertexCount_eq_56 hΓ σ hAut (_involutive_of_sq_eq_one hσ) hne

/-- **Lemma 2 (involution `a₁ = 112`).**
For any involutory automorphism `σ ≠ 1`, `adjacentMovedCount Γ σ = 112`. -/
theorem lem2_involution_a1 (hΓ : IsMoore57 Γ) (σ : Equiv.Perm V)
    (hσ : σ ^ 2 = 1) (hne : σ ≠ 1)
    (hAut : ∀ a b, Γ.Adj a b ↔ Γ.Adj (σ a) (σ b)) :
    adjacentMovedCount Γ σ = 112 := by
  have hinv : Function.Involutive σ := _involutive_of_sq_eq_one hσ
  have ha0 : fixedVertexCount σ = 56 :=
    aut_involution_fixedVertexCount_eq_56 hΓ σ hAut hinv hne
  obtain ⟨c, hstar⟩ :=
    aut_involution_fixedInducedGraph_isStarWithCenter hΓ σ hAut hinv hne
  have hformula : (adjacentMovedCount Γ σ : ℤ) =
      3250 - 58 * (fixedVertexCount σ : ℤ) + 2 * ((fixedVertexCount σ : ℤ) - 1) :=
    aut_involution_starEdgeCountFormula hΓ σ hAut hinv hstar
  rw [ha0] at hformula
  -- 3250 - 58·56 + 2·(56-1) = 3250 - 3248 + 110 = 112
  have : (adjacentMovedCount Γ σ : ℤ) = 112 := by push_cast at hformula; linarith
  exact_mod_cast this

/-- **Lemma 2 (corollary: no order-4 automorphism).**

There is no element of `Aut(Γ)` with order 4.

Proof. If `σ ∈ Aut(Γ)` has `orderOf σ = 4`, then `σ ^ 2` is a non-trivial
involution-automorphism, so by
`CameronCh3.step5_moore57_involution_sign`, `sign (σ ^ 2) = −1`. But
`sign (σ ^ 2) = (sign σ) ^ 2 = 1` (since `sign σ ∈ {±1}` and both
square to 1). Contradiction. -/
theorem lem2_no_order_four_aut (hΓ : IsMoore57 Γ) (σ : Equiv.Perm V)
    (hσ_ord : orderOf σ = 4)
    (hAut : ∀ a b, Γ.Adj a b ↔ Γ.Adj (σ a) (σ b)) : False := by
  have hσ4 : σ ^ 4 = 1 := by rw [← hσ_ord]; exact pow_orderOf_eq_one σ
  have hsq2 : (σ ^ 2) ^ 2 = 1 := by rw [← pow_mul]; exact hσ4
  have hsq_ne : σ ^ 2 ≠ 1 := fun h => by
    have hdvd : orderOf σ ∣ 2 := orderOf_dvd_of_pow_eq_one h
    rw [hσ_ord] at hdvd
    omega
  have hsq_aut : ∀ a b, Γ.Adj a b ↔ Γ.Adj ((σ ^ 2) a) ((σ ^ 2) b) := by
    intro a b
    rw [show (σ ^ 2 : Equiv.Perm V) = σ * σ from by rw [pow_two],
        Equiv.Perm.mul_apply, Equiv.Perm.mul_apply]
    rw [hAut a b, hAut (σ a) (σ b)]
  have hsign_sq : Equiv.Perm.sign (σ ^ 2) = -1 :=
    Moore57.Papers.CameronCh3.step5_moore57_involution_sign hΓ (σ ^ 2) hsq2 hsq_ne hsq_aut
  have hsign_eq : Equiv.Perm.sign (σ ^ 2) = (Equiv.Perm.sign σ) ^ 2 := by
    rw [map_pow]
  have hsign_sq_one : (Equiv.Perm.sign σ) ^ 2 = 1 := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;>
      · rw [h]; decide
  rw [hsign_eq, hsign_sq_one] at hsign_sq
  exact absurd hsign_sq (by decide)

/-- **Lemma 2 (corollary: no Klein-4 in Aut(Γ)).**

For two distinct commuting non-trivial involution-automorphisms `σ, τ`,
False follows: `στ` is also a non-trivial involution-automorphism with
`sign (στ) = (sign σ)(sign τ) = (−1)(−1) = +1`, contradicting
`sign(στ) = −1` from `step5_moore57_involution_sign`. -/
theorem lem2_no_klein_four_in_aut (hΓ : IsMoore57 Γ) (σ τ : Equiv.Perm V)
    (hσ_sq : σ ^ 2 = 1) (hσ_ne : σ ≠ 1)
    (hAut_σ : ∀ a b, Γ.Adj a b ↔ Γ.Adj (σ a) (σ b))
    (hτ_sq : τ ^ 2 = 1) (hτ_ne : τ ≠ 1)
    (hAut_τ : ∀ a b, Γ.Adj a b ↔ Γ.Adj (τ a) (τ b))
    (hcomm : σ * τ = τ * σ) (hne : σ ≠ τ) : False := by
  -- στ is a non-trivial involution-automorphism
  have hcom : Commute σ τ := hcomm
  have hστ_sq : (σ * τ) ^ 2 = 1 := by
    rw [hcom.mul_pow, hσ_sq, hτ_sq, mul_one]
  have hστ_ne : σ * τ ≠ 1 := by
    intro h
    have hσ_inv : σ⁻¹ = σ := by
      have hσσ : σ * σ = 1 := by rw [← pow_two]; exact hσ_sq
      exact inv_eq_of_mul_eq_one_right hσσ
    have hστ : σ⁻¹ = τ := mul_eq_one_iff_inv_eq.mp h
    rw [hσ_inv] at hστ
    exact hne hστ
  have hστ_aut : ∀ a b, Γ.Adj a b ↔ Γ.Adj ((σ * τ) a) ((σ * τ) b) := by
    intro a b
    simp only [Equiv.Perm.mul_apply]
    exact (hAut_τ a b).trans (hAut_σ (τ a) (τ b))
  -- Apply step5 to all three
  have hsign_σ := Moore57.Papers.CameronCh3.step5_moore57_involution_sign hΓ σ hσ_sq hσ_ne hAut_σ
  have hsign_τ := Moore57.Papers.CameronCh3.step5_moore57_involution_sign hΓ τ hτ_sq hτ_ne hAut_τ
  have hsign_στ := Moore57.Papers.CameronCh3.step5_moore57_involution_sign hΓ (σ * τ) hστ_sq hστ_ne hστ_aut
  -- But sign(στ) = sign σ · sign τ = (−1)(−1) = 1
  rw [map_mul, hsign_σ, hsign_τ] at hsign_στ
  exact absurd hsign_στ (by decide)

/-- **Lemma 2 (3): `4 ∤ |G|` for any subgroup `G ≤ Aut(Γ)`.**

If `G` is a subgroup of `Equiv.Perm V` whose elements all preserve
adjacency of a Moore57 graph `Γ`, then `4 ∤ Fintype.card G`.

Proof. The sign homomorphism `signG : G →* ℤˣ`, obtained by restricting
`Equiv.Perm.sign` to `G`, has the property that every non-trivial
involution in `G` maps to `−1` (by `step5_moore57_involution_sign`).
Suppose `4 ∣ |G|`. Then:

* By Cauchy (`exists_prime_orderOf_dvd_card`), there is an involution
  `σ ∈ G` with `signG σ = −1`. Hence `signG` is surjective onto `ℤˣ`,
  so `|range signG| = 2`.
* By the first isomorphism theorem
  (`QuotientGroup.quotientKerEquivRange`) and Lagrange
  (`Subgroup.card_eq_card_quotient_mul_card_subgroup`),
  `|G| = 2 · |ker signG|`. So `2 ∣ |ker signG|`.
* By Cauchy on `ker signG`, there is `τ ∈ ker signG` of order 2.
  Lifting `τ` to `G`, `signG τG = −1` by step5. But `τ ∈ ker signG`
  means `signG τG = 1`. Contradiction.

This avoids Sylow theory entirely. -/
theorem lem2_four_not_dvd_aut (hΓ : IsMoore57 Γ)
    (G : Subgroup (Equiv.Perm V)) [DecidablePred (· ∈ G)]
    (hG : ∀ σ ∈ G, ∀ a b, Γ.Adj a b ↔ Γ.Adj (σ a) (σ b)) :
    ¬ (4 ∣ Fintype.card G) := by
  intro h4
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  -- signG = sign restricted to G.
  let signG : G →* ℤˣ := Equiv.Perm.sign.comp G.subtype
  -- Helper: every non-trivial τ : G with τ² = 1 has signG τ = -1.
  have step5G : ∀ τ : G, τ ≠ 1 → τ ^ 2 = 1 →
      signG τ = -1 := by
    intro τ hne hsq
    have hsq' : (τ : Equiv.Perm V) ^ 2 = 1 := by
      have h := congrArg (Subgroup.subtype G) hsq
      simpa using h
    have hne' : (τ : Equiv.Perm V) ≠ 1 := fun h => hne (Subtype.ext h)
    have hAut : ∀ a b, Γ.Adj a b ↔ Γ.Adj ((τ : Equiv.Perm V) a) ((τ : Equiv.Perm V) b) :=
      hG (τ : Equiv.Perm V) τ.property
    exact Moore57.Papers.CameronCh3.step5_moore57_involution_sign hΓ _ hsq' hne' hAut
  -- Step 1: Cauchy on G — get an involution σ.
  have h2G : (2 : ℕ) ∣ Fintype.card G := dvd_trans ⟨2, rfl⟩ h4
  obtain ⟨σ, hσ_ord⟩ := exists_prime_orderOf_dvd_card (G := G) 2 h2G
  have hσ_sq : σ ^ 2 = 1 := by rw [← hσ_ord]; exact pow_orderOf_eq_one σ
  have hσ_ne : σ ≠ 1 := fun h => by
    rw [h, orderOf_one] at hσ_ord
    exact absurd hσ_ord (by decide)
  have hσ_sign : signG σ = -1 := step5G σ hσ_ne hσ_sq
  -- Step 2: signG is surjective (image = ℤˣ).
  have hSurj : Function.Surjective signG := by
    intro u
    rcases Int.units_eq_one_or u with rfl | rfl
    · exact ⟨1, signG.map_one⟩
    · exact ⟨σ, hσ_sign⟩
  -- |G| = 2 · |ker signG| via first iso + Lagrange (using Nat.card).
  have hker_eq_nat : Nat.card G = 2 * Nat.card signG.ker := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup signG.ker]
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange signG).toEquiv]
    rw [MonoidHom.range_eq_top.mpr hSurj]
    rw [Subgroup.card_top]
    rw [Nat.card_eq_fintype_card, Fintype.card_units_int]
  -- 4 ∣ |G| = 2·|ker| ⟹ 2 ∣ |ker|.
  have h4_nat : (4 : ℕ) ∣ Nat.card G := by
    rw [Nat.card_eq_fintype_card]; exact h4
  have h2_ker : (2 : ℕ) ∣ Fintype.card signG.ker := by
    rw [← Nat.card_eq_fintype_card]
    have : (4 : ℕ) ∣ 2 * Nat.card signG.ker := hker_eq_nat ▸ h4_nat
    omega
  -- Step 3: Cauchy on signG.ker — get an involution τ ∈ ker.
  obtain ⟨τ, hτ_ord⟩ := exists_prime_orderOf_dvd_card (G := signG.ker) 2 h2_ker
  have hτ_sq : τ ^ 2 = 1 := by rw [← hτ_ord]; exact pow_orderOf_eq_one τ
  have hτ_ne : τ ≠ 1 := fun h => by
    rw [h, orderOf_one] at hτ_ord
    exact absurd hτ_ord (by decide)
  -- Lift τ : signG.ker to G via the subtype.
  let τG : G := τ.val
  have hτG_sq : τG ^ 2 = 1 := by
    have h := congrArg (signG.ker.subtype) hτ_sq
    simpa [τG] using h
  have hτG_ne : τG ≠ 1 := fun h => hτ_ne (Subtype.ext h)
  -- Two contradictory facts: signG τG = -1 (by step5) and signG τG = 1 (τ ∈ ker).
  have hτG_sign : signG τG = -1 := step5G τG hτG_ne hτG_sq
  have hτG_in_ker : signG τG = 1 := τ.property
  rw [hτG_sign] at hτG_in_ker
  exact absurd hτG_in_ker (by decide)

/-- **Corollary of Lemma 2: no vertex-transitive subgroup of `Aut(Γ)`.**

This is Cameron Ch.3 Theorem 3.13, proved by combining
`lem2_four_not_dvd_aut` with orbit-stabilizer. If `G ≤ Aut(Γ)` acts
transitively on `V`, then `|G| = |V| · |Stab_v|` for any `v`. Cauchy
(`2 ∣ |G|` since `2 ∣ 3250 ∣ |G|`) gives an involution `σ ∈ G`, which has
56 fixed points; pick `v ∈ Fix(σ)`. Then `σ ∈ Stab_v` and `σ ≠ 1`, so
`2 ∣ |Stab_v|`. Combined with `2 ∣ |V|`, this gives `4 ∣ |G|`,
contradicting `lem2_four_not_dvd_aut`. -/
theorem cor_lem2_no_vertex_transitive_aut (hΓ : IsMoore57 Γ)
    (G : Subgroup (Equiv.Perm V)) [DecidablePred (· ∈ G)]
    (hG : ∀ σ ∈ G, ∀ a b, Γ.Adj a b ↔ Γ.Adj (σ a) (σ b))
    (hVtrans : MulAction.IsPretransitive G V) : False := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Nonempty V := Fintype.card_pos_iff.mp (by rw [hΓ.card]; decide)
  -- Step 1: 3250 = |V| ∣ |G| via vertex-transitivity (orbit-stabilizer).
  -- Equivalently: |stabilizer G v|.index = |V|, so |V| ∣ |G|.
  have h2_V : (2 : ℕ) ∣ Fintype.card V := by rw [hΓ.card]; decide
  -- 2 ∣ |V| ∣ |G|, so 2 ∣ |G|. Use index_stabilizer_of_transitive.
  have h2_G : (2 : ℕ) ∣ Fintype.card G := by
    obtain ⟨v₀⟩ := (inferInstance : Nonempty V)
    have hindex : (MulAction.stabilizer G v₀).index = Nat.card V :=
      MulAction.index_stabilizer_of_transitive (G := G) v₀
    have h2V_nat : (2 : ℕ) ∣ Nat.card V := by
      rw [Nat.card_eq_fintype_card]; exact h2_V
    rw [← hindex] at h2V_nat
    have hG_eq : Nat.card G = Nat.card (MulAction.stabilizer G v₀) *
        (MulAction.stabilizer G v₀).index :=
      ((MulAction.stabilizer G v₀).card_mul_index).symm
    have h2G_nat : (2 : ℕ) ∣ Nat.card G := by
      rw [hG_eq]; exact dvd_mul_of_dvd_right h2V_nat _
    rwa [Nat.card_eq_fintype_card] at h2G_nat
  -- Step 2: Cauchy gives involution σ ∈ G.
  obtain ⟨σ, hσ_ord⟩ := exists_prime_orderOf_dvd_card (G := G) 2 h2_G
  have hσ_sq : σ ^ 2 = 1 := by rw [← hσ_ord]; exact pow_orderOf_eq_one σ
  have hσ_ne : σ ≠ 1 := fun h => by
    rw [h, orderOf_one] at hσ_ord; exact absurd hσ_ord (by decide)
  -- σ has 56 fixed points; pick one.
  have hσ_inv : Function.Involutive (σ : Equiv.Perm V) := fun x => by
    have h := congrArg (Subgroup.subtype G) hσ_sq
    have hsq : (σ : Equiv.Perm V) ^ 2 = 1 := by simpa using h
    have h := congrArg (fun (f : Equiv.Perm V) => f x) hsq
    simpa [pow_two, Equiv.Perm.mul_apply] using h
  have hσ_ne_perm : (σ : Equiv.Perm V) ≠ 1 := fun h => hσ_ne (Subtype.ext h)
  have hAut_σ : ∀ a b, Γ.Adj a b ↔ Γ.Adj ((σ : Equiv.Perm V) a) ((σ : Equiv.Perm V) b) :=
    hG _ σ.property
  have hfix_card : fixedVertexCount (σ : Equiv.Perm V) = 56 :=
    aut_involution_fixedVertexCount_eq_56 hΓ _ hAut_σ hσ_inv hσ_ne_perm
  have hfix_nonempty : (Moore57.fixedVertexSet (σ : Equiv.Perm V)).Nonempty := by
    have hcard : Fintype.card (Moore57.fixedVertexSet (σ : Equiv.Perm V)) = 56 := by
      rw [← hfix_card]; exact (Moore57.fixedVertexCount_eq_card_fixedVertexSet _).symm
    rw [← Set.nonempty_coe_sort]
    exact Fintype.card_pos_iff.mp (by rw [hcard]; decide)
  obtain ⟨v, hv⟩ := hfix_nonempty
  have hv_fix : (σ : Equiv.Perm V) v = v := Moore57.mem_fixedVertexSet.mp hv
  have hσ_stab : σ ∈ MulAction.stabilizer G v := by
    rw [MulAction.mem_stabilizer_iff]; exact hv_fix
  -- Step 3: 2 ∣ |stabilizer G v|.
  have h2_stab : (2 : ℕ) ∣ Fintype.card (MulAction.stabilizer G v) := by
    have horder : orderOf (⟨σ, hσ_stab⟩ : MulAction.stabilizer G v) = 2 := by
      apply orderOf_eq_prime
      · apply Subtype.ext
        show (σ : G) ^ 2 = 1
        exact hσ_sq
      · intro h
        apply hσ_ne
        have hsub : ((⟨σ, hσ_stab⟩ : MulAction.stabilizer G v) : G) = (1 : G) := by
          rw [h]; rfl
        simpa using hsub
    rw [← horder]; exact orderOf_dvd_card
  -- Step 4: |G| = |orbit| · |stab| = |V| · |stab|, with 2 ∣ |V| and 2 ∣ |stab|.
  have h_orbit_stab :
      Fintype.card V * Fintype.card (MulAction.stabilizer G v) =
      Fintype.card G := by
    have h_orbit := MulAction.card_orbit_mul_card_stabilizer_eq_card_group
      (α := G) (β := V) v
    have h_orbit_eq_univ : MulAction.orbit G v = Set.univ :=
      MulAction.orbit_eq_univ G v
    have h_orbit_card : Fintype.card (MulAction.orbit G v) = Fintype.card V := by
      have : Fintype.card (MulAction.orbit G v) = Fintype.card (Set.univ : Set V) := by
        apply Fintype.card_congr
        exact Equiv.setCongr h_orbit_eq_univ
      rw [this]
      exact Fintype.card_congr (Equiv.Set.univ V)
    rw [h_orbit_card] at h_orbit
    exact h_orbit
  have h4_G : (4 : ℕ) ∣ Fintype.card G := by
    rw [← h_orbit_stab]
    rcases h2_V with ⟨a, ha⟩
    rcases h2_stab with ⟨b, hb⟩
    refine ⟨a * b, ?_⟩
    rw [ha, hb]; ring
  exact lem2_four_not_dvd_aut hΓ G hG h4_G

end Moore57.Papers.MacajSiran2010.S2
