import Mathlib.GroupTheory.OrderOfElement
import Mathlib.GroupTheory.Perm.Cycle.Basic

set_option linter.unusedSectionVars false

/-!
# Semi-regular orbit divisibility

For a permutation `σ : Equiv.Perm V` acting σ-invariantly on a finite set
`S : Finset V`, if the action of the cyclic subgroup `⟨σ⟩` is
**semi-regular** on `S` (every non-trivial power moves every element of
`S`), then `orderOf σ ∣ S.card`.

This is the standard orbit-stabilizer consequence: under semi-regularity,
each `⟨σ⟩`-orbit in `S` has cardinality exactly `orderOf σ`, and the
orbits partition `S`.

## Main result

* `Moore57.orderOf_dvd_card_of_semiRegular`: if `S` is σ-invariant and σ
  acts on `S` with trivial stabilizers, then `orderOf σ ∣ S.card`.

The hypothesis "trivial stabilizer of every `v ∈ S`" is phrased
elementarily as `∀ v ∈ S, ∀ k : ℕ, σ^k v = v → orderOf σ ∣ k`.

The proof partitions `S` by removing one orbit at a time and inducting on
`S.card`.
-/

namespace Moore57

variable {V : Type*}

/-- The orbit of `v` under `⟨σ⟩` as a Finset, written as the image of
`Finset.range (orderOf σ)` under `k ↦ σ^k v`. -/
noncomputable def cyclicOrbitFinset [DecidableEq V] (σ : Equiv.Perm V) (v : V) : Finset V :=
  (Finset.range (orderOf σ)).image (fun k => (σ^k : Equiv.Perm V) v)

namespace cyclicOrbitFinset

variable [DecidableEq V]

@[simp] theorem mem_cyclicOrbitFinset (σ : Equiv.Perm V) (v w : V) :
    w ∈ cyclicOrbitFinset σ v ↔ ∃ k, k < orderOf σ ∧ (σ^k) v = w := by
  unfold cyclicOrbitFinset
  simp [Finset.mem_image, Finset.mem_range, eq_comm]

theorem self_mem (σ : Equiv.Perm V) (v : V) (hpos : 0 < orderOf σ) :
    v ∈ cyclicOrbitFinset σ v := by
  rw [mem_cyclicOrbitFinset]
  exact ⟨0, hpos, by simp⟩

/-- `σ^k v ∈ S` for every `k : ℕ`, when `S` is σ-invariant containing `v`. -/
theorem pow_mem_of_invariant (σ : Equiv.Perm V) (S : Finset V)
    (hinv : ∀ v ∈ S, σ v ∈ S) (v : V) (hv : v ∈ S) :
    ∀ k : ℕ, (σ^k) v ∈ S := by
  intro k
  induction k with
  | zero => simpa using hv
  | succ n ihn =>
      have : (σ^(n+1)) v = σ ((σ^n) v) := by
        rw [pow_succ', Equiv.Perm.mul_apply]
      rw [this]
      exact hinv _ ihn

/-- **Orbit is contained in `S`.** If `S` is σ-invariant and `v ∈ S`,
then `cyclicOrbitFinset σ v ⊆ S`. -/
theorem subset_of_invariant (σ : Equiv.Perm V) (S : Finset V)
    (hinv : ∀ v ∈ S, σ v ∈ S) (v : V) (hv : v ∈ S) :
    cyclicOrbitFinset σ v ⊆ S := by
  intro w hw
  rw [mem_cyclicOrbitFinset] at hw
  obtain ⟨k, _, hk⟩ := hw
  rw [← hk]
  exact pow_mem_of_invariant σ S hinv v hv k

/-- **Orbit size = `orderOf σ` under semi-regular action.** If the
stabilizer of `v` in `⟨σ⟩` is trivial (`σ^k v = v ⟹ orderOf σ ∣ k`),
then `|cyclicOrbitFinset σ v| = orderOf σ`. -/
theorem card_eq_orderOf (σ : Equiv.Perm V) (v : V)
    (hsemi : ∀ k : ℕ, (σ^k) v = v → orderOf σ ∣ k) :
    (cyclicOrbitFinset σ v).card = orderOf σ := by
  unfold cyclicOrbitFinset
  rw [Finset.card_image_of_injOn, Finset.card_range]
  intro i hi j hj hij
  simp only [Finset.coe_range, Set.mem_Iio] at hi hj
  change (σ^i) v = (σ^j) v at hij
  -- `σ^i v = σ^j v` with `i, j < orderOf σ` ⟹ `i = j`.
  -- WLOG `j ≤ i`: then `σ^i v = σ^j (σ^(i-j) v)`, and σ^j injectivity
  -- yields `σ^(i-j) v = v`, hence `orderOf σ ∣ (i-j)` by semi-regularity.
  -- Combined with `i - j < orderOf σ`, we get `i - j = 0` ⟹ `i = j`.
  rcases le_total j i with hle | hle
  · -- `j ≤ i` case
    have hcomm : (σ^i) v = (σ^j) ((σ^(i - j)) v) := by
      have heq : i = j + (i - j) := (Nat.add_sub_cancel' hle).symm
      conv_lhs => rw [heq, pow_add, Equiv.Perm.mul_apply]
    rw [hij] at hcomm
    have hsub : (σ^(i - j)) v = v := (σ^j).injective hcomm.symm
    have hdvd : orderOf σ ∣ (i - j) := hsemi (i - j) hsub
    have hlt : i - j < orderOf σ := lt_of_le_of_lt (Nat.sub_le _ _) hi
    have hzero : i - j = 0 := by
      rcases Nat.eq_zero_or_pos (i - j) with h | h
      · exact h
      · exact absurd (Nat.le_of_dvd h hdvd) (not_le.mpr hlt)
    omega
  · -- `i ≤ j` case: symmetric
    have hcomm : (σ^j) v = (σ^i) ((σ^(j - i)) v) := by
      have heq : j = i + (j - i) := (Nat.add_sub_cancel' hle).symm
      conv_lhs => rw [heq, pow_add, Equiv.Perm.mul_apply]
    rw [← hij] at hcomm
    have hsub : (σ^(j - i)) v = v := (σ^i).injective hcomm.symm
    have hdvd : orderOf σ ∣ (j - i) := hsemi (j - i) hsub
    have hlt : j - i < orderOf σ := lt_of_le_of_lt (Nat.sub_le _ _) hj
    have hzero : j - i = 0 := by
      rcases Nat.eq_zero_or_pos (j - i) with h | h
      · exact h
      · exact absurd (Nat.le_of_dvd h hdvd) (not_le.mpr hlt)
    omega

end cyclicOrbitFinset

/-- **Semi-regular orbit divisibility (Finset form).** Let
`σ : Equiv.Perm V` act on a σ-invariant Finset `S` (closed under σ).
If the cyclic action `⟨σ⟩ ↷ S` is **semi-regular** (every non-trivial
power of σ moves every element of `S`), then `orderOf σ ∣ S.card`.

The semi-regular hypothesis is phrased elementarily:
`∀ v ∈ S, ∀ k : ℕ, σ^k v = v → orderOf σ ∣ k`,
i.e. the stabilizer of every `v ∈ S` inside `⟨σ⟩` is trivial.

The proof partitions `S` by repeatedly removing one orbit
(`cyclicOrbitFinset σ v`, of cardinality `orderOf σ`) and inducting on
`S.card`. -/
theorem orderOf_dvd_card_of_semiRegular [Fintype V] [DecidableEq V]
    (σ : Equiv.Perm V) (S : Finset V)
    (hinv : ∀ v ∈ S, σ v ∈ S)
    (hsemi : ∀ v ∈ S, ∀ k : ℕ, (σ^k) v = v → orderOf σ ∣ k) :
    orderOf σ ∣ S.card := by
  -- Strong induction on `S.card`.
  induction hn : S.card using Nat.strong_induction_on generalizing S with
  | _ n ih =>
    rcases Finset.eq_empty_or_nonempty S with rfl | ⟨v, hv⟩
    · simp at hn; simp [← hn]
    have hpos : 0 < orderOf σ := (isOfFinOrder_of_finite σ).orderOf_pos
    let O : Finset V := cyclicOrbitFinset σ v
    have hO_card : O.card = orderOf σ :=
      cyclicOrbitFinset.card_eq_orderOf σ v (hsemi v hv)
    have hO_sub : O ⊆ S :=
      cyclicOrbitFinset.subset_of_invariant σ S hinv v hv
    -- `S \ O` is σ-invariant
    have hSO_inv : ∀ w ∈ S \ O, σ w ∈ S \ O := by
      intro w hw
      rw [Finset.mem_sdiff] at hw
      obtain ⟨hwS, hwO⟩ := hw
      have hsw_S : σ w ∈ S := hinv w hwS
      have hsw_notO : σ w ∉ O := by
        intro hsw
        rw [cyclicOrbitFinset.mem_cyclicOrbitFinset] at hsw
        obtain ⟨k, hk, hkv⟩ := hsw
        -- σ w = σ^k v.  Apply σ⁻¹ to get w = σ^(k-1) v (mod orderOf σ),
        -- which means w ∈ O — contradicting `w ∉ O`.
        apply hwO
        rw [cyclicOrbitFinset.mem_cyclicOrbitFinset]
        rcases Nat.eq_zero_or_pos k with rfl | hk_pos
        · -- k = 0: σ w = v.  Then w = σ⁻¹ v = σ^(orderOf σ - 1) v.
          refine ⟨orderOf σ - 1, by omega, ?_⟩
          apply σ.injective
          have h1 : σ ((σ^(orderOf σ - 1)) v) = (σ^(orderOf σ - 1 + 1)) v := by
            rw [pow_succ', Equiv.Perm.mul_apply]
          have h2 : orderOf σ - 1 + 1 = orderOf σ := by omega
          rw [h1, h2, pow_orderOf_eq_one]
          have hkv' : v = σ w := by simpa using hkv
          rw [hkv']
          rfl
        · -- k ≥ 1: σ w = σ^k v.  Then w = σ^(k-1) v.
          refine ⟨k - 1, by omega, ?_⟩
          apply σ.injective
          have h1 : σ ((σ^(k - 1)) v) = (σ^(k - 1 + 1)) v := by
            rw [pow_succ', Equiv.Perm.mul_apply]
          have h2 : k - 1 + 1 = k := by omega
          rw [h1, h2]
          exact hkv
      exact Finset.mem_sdiff.mpr ⟨hsw_S, hsw_notO⟩
    -- `S \ O` is still semi-regular
    have hSO_semi : ∀ w ∈ S \ O, ∀ k : ℕ, (σ^k) w = w → orderOf σ ∣ k := by
      intro w hw
      rw [Finset.mem_sdiff] at hw
      exact hsemi w hw.1
    -- `(S \ O).card < S.card`
    have hSO_card_lt : (S \ O).card < S.card := by
      rw [Finset.card_sdiff_of_subset hO_sub, hO_card]
      have hOleS : orderOf σ ≤ S.card := by
        rw [← hO_card]; exact Finset.card_le_card hO_sub
      omega
    -- Apply IH
    have hih : orderOf σ ∣ (S \ O).card := by
      have hcardlt : (S \ O).card < n := hn ▸ hSO_card_lt
      exact ih (S \ O).card hcardlt (S \ O) hSO_inv hSO_semi rfl
    -- `S.card = O.card + (S \ O).card = orderOf σ + (S \ O).card`
    have hcard_split : S.card = O.card + (S \ O).card := by
      rw [Finset.card_sdiff_of_subset hO_sub]
      have hOle : O.card ≤ S.card := Finset.card_le_card hO_sub
      omega
    rw [← hn, hcard_split, hO_card]
    exact Dvd.dvd.add (dvd_refl _) hih

end Moore57
