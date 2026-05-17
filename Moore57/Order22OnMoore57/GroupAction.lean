import Moore57.Order22OnMoore57.NoGo
import Mathlib.GroupTheory.Sylow
import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# Order N group acting on Moore57 (Subgroup form)

外向き interface として「位数 N の (Aut(Γ) の) 部分群」を直接扱う structure
`OrderN_GroupActsOnMoore57 N`. これは既存 raw structure
`Order22ActsOnMoore57` (σ, τ 形式) と:

1. Order22 用 bridge `OrderN 22 → Order22ActsOnMoore57` (Sylow 解析).
2. Order110 用 reduction `OrderN 110 → OrderN 22` (Sylow + Cauchy で
   部分群を取り出す).

を組み合わせて, 位数 22 と位数 110 の Aut(Γ) 部分群が共に存在しないことを
証明する.
-/

namespace Moore57

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- `Aut(Γ)` の部分群: その任意の元が `Γ.Adj` を保つ. -/
def IsAutSubgroup (Γ : SimpleGraph V) [DecidableRel Γ.Adj]
    (G : Subgroup (Equiv.Perm V)) : Prop :=
  ∀ σ : G, ∀ v w : V, Γ.Adj v w ↔ Γ.Adj ((σ : Equiv.Perm V) v) ((σ : Equiv.Perm V) w)

/-- 位数 `N` の `Aut(Γ)` の部分群が Moore57 graph `Γ` 上に作用する状況.

`G : Subgroup (Equiv.Perm V)` の cardinality が `N`, 各元が辺を保つ. -/
structure OrderN_GroupActsOnMoore57
    (N : ℕ) (V : Type*) [Fintype V] [DecidableEq V]
    (Γ : SimpleGraph V) [DecidableRel Γ.Adj] where
  /-- Γ は Moore graph of degree 57. -/
  isMoore : IsMoore57 Γ
  /-- 部分群 G ≤ Aut(Γ) ≤ Perm V. -/
  G : Subgroup (Equiv.Perm V)
  /-- 位数 = N. -/
  G_card : Nat.card G = N
  /-- 各 σ ∈ G は辺を保つ (= G ≤ Aut(Γ)). -/
  G_aut : IsAutSubgroup Γ G

/-! ## 部分群 H ≤ G に対する subgroup form の reduction

`H ≤ G` で `Nat.card H = M` なら `OrderN_GroupActsOnMoore57 M` を得る. -/

/-- 部分群 H ≤ G の Equiv.Perm V 上での image (= H 自体, ≤ G) で
作用が継承される. -/
theorem orderN_of_subgroup_le
    {N M : ℕ} (h : OrderN_GroupActsOnMoore57 N V Γ)
    (H : Subgroup (Equiv.Perm V)) (hH_le : H ≤ h.G) (hH_card : Nat.card H = M) :
    Nonempty (OrderN_GroupActsOnMoore57 M V Γ) := by
  refine ⟨⟨h.isMoore, H, hH_card, ?_⟩⟩
  intro ⟨σ, hσ⟩ v w
  -- σ ∈ H ⟹ σ ∈ G ⟹ σ は Γ.Adj を保つ.
  exact h.G_aut ⟨σ, hH_le hσ⟩ v w

/-! ## Step 2: Order110 → Order22 reduction

|G| = 110 = 2·5·11 で Sylow 11-subgroup は唯一 (n_11 | 10 ∧ n_11 ≡ 1 mod 11
⟹ n_11 = 1), よって normal. 任意の involution τ と Sylow 11 generator σ
を組み合わせると order 11·2/1 = 22 の部分群が得られる. -/

namespace Order110Aux

variable (G : Subgroup (Equiv.Perm V))

/-- |G| = 110 のとき, Sylow 11-subgroup の数は 1. -/
private theorem sylow_eleven_unique_of_card_110 [Fact (Nat.Prime 11)]
    (hG_card : Nat.card G = 110) :
    Nat.card (Sylow 11 G) = 1 := by
  haveI : Finite G := Nat.finite_of_card_ne_zero (by rw [hG_card]; decide)
  haveI : Fintype G := Fintype.ofFinite _
  obtain ⟨Q⟩ := Sylow.nonempty (p := 11) (G := G)
  -- |Q| = 11.
  have hfact : (110 : ℕ).factorization 11 = 1 := by
    have h_decomp : (110 : ℕ) = 11 * 10 := by norm_num
    rw [h_decomp, Nat.factorization_mul (by norm_num) (by norm_num)]
    simp only [Finsupp.coe_add, Pi.add_apply,
      Nat.Prime.factorization_self (by norm_num : Nat.Prime 11),
      Nat.factorization_eq_zero_of_lt (show (10 : ℕ) < 11 by norm_num)]
  have hQ_card : Nat.card Q.toSubgroup = 11 := by
    rw [Sylow.card_eq_multiplicity, hG_card, hfact]; norm_num
  -- Q.index = 10.
  have hQ_idx : Q.toSubgroup.index = 10 := by
    have hLag : Nat.card Q.toSubgroup * Q.toSubgroup.index = Nat.card G :=
      Subgroup.card_mul_index Q.toSubgroup
    rw [hQ_card, hG_card] at hLag
    omega
  -- |Sylow 11 G| ∣ 10.
  have hdvd : Nat.card (Sylow 11 G) ∣ 10 := by
    rw [← hQ_idx]; exact Sylow.card_dvd_index Q
  -- |Sylow 11 G| ≡ 1 mod 11.
  have hmod : Nat.card (Sylow 11 G) ≡ 1 [MOD 11] := card_sylow_modEq_one 11 G
  -- 0 < |Sylow 11 G| ≤ 10, ≡ 1 mod 11 ⟹ = 1.
  have h_pos : 0 < Nat.card (Sylow 11 G) := Nat.card_pos
  have h_le : Nat.card (Sylow 11 G) ≤ 10 := Nat.le_of_dvd (by norm_num) hdvd
  -- 列挙.
  interval_cases (Nat.card (Sylow 11 G))
  all_goals (first | rfl | (exfalso; revert hmod; decide))

end Order110Aux

/-- Order110 → Order22 reduction: |G| = 110 のとき G に位数 22 の部分群がある.

戦略: Sylow 11 unique で P_σ := ⟨σ⟩ ◁ G normal. τ : G involution.
`mul_injective_of_disjoint` で P_σ × P_τ → G mult が injective, image =
`P_σ * P_τ = ↑(P_σ ⊔ P_τ)` (mul_normal). よって |P_σ ⊔ P_τ| = 11·2 = 22. -/
theorem orderN_22_of_orderN_110 (h110 : OrderN_GroupActsOnMoore57 110 V Γ) :
    Nonempty (OrderN_GroupActsOnMoore57 22 V Γ) := by
  classical
  haveI hp11 : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  haveI hp2 : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set G := h110.G with hG_def
  have hG_card : Nat.card G = 110 := h110.G_card
  haveI hGFin : Finite G := Nat.finite_of_card_ne_zero (by rw [hG_card]; decide)
  haveI hGFintype : Fintype G := Fintype.ofFinite _
  have hG_fcard : Fintype.card G = 110 := by
    rw [← Nat.card_eq_fintype_card]; exact hG_card
  -- (1) σ : G of order 11, τ : G of order 2 (Cauchy).
  obtain ⟨σ_g, hσ⟩ : ∃ σ : G, orderOf σ = 11 :=
    exists_prime_orderOf_dvd_card 11 (by rw [hG_fcard]; decide)
  obtain ⟨τ_g, hτ⟩ : ∃ τ : G, orderOf τ = 2 :=
    exists_prime_orderOf_dvd_card 2 (by rw [hG_fcard]; decide)
  -- (2) P_σ := ⟨σ⟩ as Subgroup G with card 11.
  have hfact : (110 : ℕ).factorization 11 = 1 := by
    have h_decomp : (110 : ℕ) = 11 * 10 := by norm_num
    rw [h_decomp, Nat.factorization_mul (by norm_num) (by norm_num)]
    simp only [Finsupp.coe_add, Pi.add_apply,
      Nat.Prime.factorization_self (by norm_num : Nat.Prime 11),
      Nat.factorization_eq_zero_of_lt (show (10 : ℕ) < 11 by norm_num)]
  let P_σ : Subgroup G := Subgroup.zpowers σ_g
  let P_τ : Subgroup G := Subgroup.zpowers τ_g
  have hP_σ_card : Nat.card P_σ = 11 := by
    show Nat.card (Subgroup.zpowers σ_g) = 11
    rw [Nat.card_zpowers, hσ]
  have hP_τ_card : Nat.card P_τ = 2 := by
    show Nat.card (Subgroup.zpowers τ_g) = 2
    rw [Nat.card_zpowers, hτ]
  -- (3) Sylow 11 of G is unique → P_σ is normal.
  have hSyl_card : Nat.card (Sylow 11 G) = 1 :=
    Order110Aux.sylow_eleven_unique_of_card_110 G hG_card
  haveI hSyl_subsingleton : Subsingleton (Sylow 11 G) :=
    (Nat.card_eq_one_iff_unique.mp hSyl_card).1
  let P_σ_syl : Sylow 11 G := Sylow.ofCard P_σ (by
    show Nat.card (Subgroup.zpowers σ_g) = 11 ^ (Nat.card G).factorization 11
    rw [hG_card, hfact, pow_one, Nat.card_zpowers, hσ])
  have hP_σ_normal : P_σ.Normal := Sylow.normal_of_subsingleton P_σ_syl
  -- (4) Disjoint via coprime: P_τ ⊓ P_σ = ⊥.
  have hInf_bot : P_τ ⊓ P_σ = ⊥ :=
    Subgroup.inf_eq_bot_of_coprime (by rw [hP_τ_card, hP_σ_card]; decide)
  -- (5) Card of H_inner := P_τ ⊔ P_σ is 22 via second iso theorem.
  haveI : P_σ.Normal := hP_σ_normal
  -- Bind sup as a local subgroup for clearer type inference.
  set H_sup : Subgroup G := P_τ ⊔ P_σ with hH_sup_def
  set H_inf : Subgroup G := P_τ ⊓ P_σ with hH_inf_def
  have h_inf_le : H_inf ≤ P_τ := inf_le_left
  have h_P_σ_le : P_σ ≤ H_sup := le_sup_right
  have h2iso :=
    Nat.card_congr (QuotientGroup.quotientInfEquivProdNormalQuotient P_τ P_σ).toEquiv
  -- (P_τ ⊓ P_σ).subgroupOf P_τ = P_σ.subgroupOf P_τ (by inf_subgroupOf_left).
  have hInfSubgroupOf_eq : (P_τ ⊓ P_σ).subgroupOf P_τ = P_σ.subgroupOf P_τ :=
    Subgroup.inf_subgroupOf_left P_σ P_τ
  -- LHS subgroupOf card: H_inf ≤ P_τ → card preserved, = card ⊥ = 1.
  have hLHS_subgroupOf_card : Nat.card (P_σ.subgroupOf P_τ) = 1 := by
    rw [← hInfSubgroupOf_eq]
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe h_inf_le).toEquiv]
    rw [show H_inf = ⊥ from hInf_bot]
    exact Nat.card_eq_one_iff_unique.mpr ⟨inferInstance, ⟨1⟩⟩
  have hLHS : Nat.card (P_τ ⧸ P_σ.subgroupOf P_τ) = 2 := by
    have hLag : Nat.card P_τ =
                Nat.card (P_τ ⧸ P_σ.subgroupOf P_τ) *
                Nat.card (P_σ.subgroupOf P_τ) :=
      Subgroup.card_eq_card_quotient_mul_card_subgroup _
    rw [hP_τ_card, hLHS_subgroupOf_card, mul_one] at hLag
    exact hLag.symm
  -- RHS subgroupOf card: P_σ ≤ H_sup → card preserved = 11.
  have hRHS_subgroupOf_card : Nat.card (P_σ.subgroupOf H_sup) = 11 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe h_P_σ_le).toEquiv]
    exact hP_σ_card
  have hCard_inner : Nat.card H_sup = 22 := by
    have hLag : Nat.card H_sup =
                Nat.card (H_sup ⧸ P_σ.subgroupOf H_sup) *
                Nat.card (P_σ.subgroupOf H_sup) :=
      Subgroup.card_eq_card_quotient_mul_card_subgroup _
    rw [hRHS_subgroupOf_card, ← h2iso, hLHS] at hLag
    rw [hLag]
  -- (6) Map H_inner (= P_τ ⊔ P_σ ≤ G) to Subgroup (Equiv.Perm V).
  let H : Subgroup (Equiv.Perm V) := Subgroup.map G.subtype (P_τ ⊔ P_σ)
  have hH_le_G : H ≤ G := by
    intro x ⟨y, _, hy⟩
    rw [← hy]
    exact y.2
  have hH_card : Nat.card H = 22 := by
    show Nat.card (Subgroup.map G.subtype (P_τ ⊔ P_σ)) = 22
    rw [Nat.card_congr (Subgroup.equivMapOfInjective _ _ Subtype.val_injective).symm.toEquiv]
    exact hCard_inner
  exact orderN_of_subgroup_le h110 H hH_le_G hH_card

end Moore57
