import Moore57.Foundations.GroupAction.SemiRegularOrbit
import Moore57.Foundations.GroupAction.FixedPoints

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Fixed-point sets under powers, given semi-regularity

This module is the **paper-faithful** companion to `SemiRegularOrbit`.

For `σ : Equiv.Perm V` acting semi-regularly on `V \ Fix(σ)` (i.e. the
stabiliser of every non-fixed point inside `⟨σ⟩` is trivial), the
fixed-point set is invariant under coprime powers — and more — without
appealing to `Equiv.Perm.support_pow_coprime`.  The result is the
MS 2010 §6 *Fix(σ^l) = Fix(σ)* assertion for `0 < l < orderOf σ`.

## Main results

* `fixedVertexSet_pow_subset_of_semiRegular_complement`:
  If σ is semi-regular on `V \ Fix(σ)` and `l : ℕ` is *not* a multiple of
  `orderOf σ`, then `Fix(σ^l) ⊆ Fix(σ)`.  Combined with the trivial
  inclusion this gives equality.
* `fixedVertexSet_pow_eq_of_semiRegular_complement`:
  `Fix(σ^l) = Fix(σ)` for `0 < l < orderOf σ`, given semi-regularity on
  the complement.
* `fixedVertexCount_pow_eq_of_semiRegular_complement`:
  cardinality corollary `a₀(σ^l) = a₀(σ)`.
* `card_eq_fixedVertexCount_add_orderOf_mul_of_semiRegular_complement`:
  total vertex count formula
  `Fintype.card V = fixedVertexCount σ + k * orderOf σ`
  for some `k`, given σ semi-regular on `V \ Fix(σ)`.

The semi-regular hypothesis is phrased elementarily as
`∀ v, σ v ≠ v → ∀ k : ℕ, σ^k v = v → orderOf σ ∣ k`,
matching the form used by `SemiRegularOrbit` and
`SemiRegularComplement`.
-/

namespace Moore57

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **Fix(σ^l) ⊆ Fix(σ) for non-multiple `l`, given semi-regularity on
the complement.**

If σ acts semi-regularly on `V \ Fix(σ)` and `¬(orderOf σ ∣ l)`, then
every fixed point of `σ^l` is already a fixed point of σ.

Proof: contrapositive.  If `(σ^l) v = v` and `σ v ≠ v`, then v is a
non-fixed point and the semi-regular hypothesis at v says
`orderOf σ ∣ l`, contradicting `¬(orderOf σ ∣ l)`. -/
theorem fixedVertexSet_pow_subset_of_semiRegular_complement
    (σ : Equiv.Perm V)
    (hsemi : ∀ v : V, σ v ≠ v → ∀ k : ℕ, (σ^k) v = v → orderOf σ ∣ k)
    {l : ℕ} (hl : ¬ orderOf σ ∣ l) :
    fixedVertexSet (σ ^ l) ⊆ fixedVertexSet σ := by
  intro v hv
  -- `hv : (σ^l) v = v`.  Goal: `σ v = v`.
  rw [mem_fixedVertexSet] at hv ⊢
  by_contra hnotfix
  exact hl (hsemi v hnotfix l hv)

/-- **Fix(σ^l) = Fix(σ) for `0 < l < orderOf σ`, given semi-regularity
on the complement.**

This is MS 2010 §6 Lemma 21 (paper-faithful form): under the
semi-regular hypothesis on `V \ Fix(σ)`, all non-trivial powers of σ
*strictly below* `orderOf σ` have exactly the same fixed-point set as σ
itself. -/
theorem fixedVertexSet_pow_eq_of_semiRegular_complement
    (σ : Equiv.Perm V)
    (hsemi : ∀ v : V, σ v ≠ v → ∀ k : ℕ, (σ^k) v = v → orderOf σ ∣ k)
    {l : ℕ} (hl_pos : 0 < l) (hl_lt : l < orderOf σ) :
    fixedVertexSet (σ ^ l) = fixedVertexSet σ := by
  apply Set.Subset.antisymm
  · -- Fix(σ^l) ⊆ Fix(σ): use the subset lemma with ¬(orderOf σ ∣ l).
    apply fixedVertexSet_pow_subset_of_semiRegular_complement σ hsemi
    intro hdvd
    exact absurd (Nat.le_of_dvd hl_pos hdvd) (not_le.mpr hl_lt)
  · -- Fix(σ) ⊆ Fix(σ^l): trivial, already in `FixedPoints`.
    exact fixedVertexSet_subset_pow σ l

/-- **Cardinality corollary**: `a₀(σ^l) = a₀(σ)` for `0 < l < orderOf σ`,
given semi-regularity on `V \ Fix(σ)`.

This complements `fixedVertexCount_pow_coprime` (which uses
`Equiv.Perm.support_pow_coprime` and needs `Nat.Coprime l (orderOf σ)`)
by giving the stronger conclusion under semi-regularity alone — no
coprime hypothesis required. -/
theorem fixedVertexCount_pow_eq_of_semiRegular_complement
    (σ : Equiv.Perm V)
    (hsemi : ∀ v : V, σ v ≠ v → ∀ k : ℕ, (σ^k) v = v → orderOf σ ∣ k)
    {l : ℕ} (hl_pos : 0 < l) (hl_lt : l < orderOf σ) :
    fixedVertexCount (σ ^ l) = fixedVertexCount σ := by
  classical
  have hset := fixedVertexSet_pow_eq_of_semiRegular_complement σ hsemi hl_pos hl_lt
  rw [fixedVertexCount_eq_card_fixedVertexSet,
      fixedVertexCount_eq_card_fixedVertexSet]
  exact Fintype.card_congr (Equiv.setCongr hset)

/-- The σ-moved Finset `V \ Fix(σ)` (i.e. `σ.support` as a Finset). -/
noncomputable def movedFinset (σ : Equiv.Perm V) : Finset V :=
  σ.support

@[simp] theorem mem_movedFinset (σ : Equiv.Perm V) (v : V) :
    v ∈ movedFinset σ ↔ σ v ≠ v := by
  simp [movedFinset, Equiv.Perm.mem_support]

/-- `movedFinset σ` is σ-invariant. -/
theorem movedFinset_σ_invariant (σ : Equiv.Perm V) :
    ∀ v ∈ movedFinset σ, σ v ∈ movedFinset σ := by
  intro v hv
  rw [mem_movedFinset] at hv ⊢
  intro h
  exact hv (σ.injective h)

/-- **Cardinality of moved set under semi-regularity.**

If σ acts semi-regularly on `V \ Fix(σ)`, then `orderOf σ ∣ |V \ Fix(σ)|`.

Direct application of `orderOf_dvd_card_of_semiRegular` to
`movedFinset σ`. -/
theorem orderOf_dvd_card_movedFinset_of_semiRegular_complement
    (σ : Equiv.Perm V)
    (hsemi : ∀ v : V, σ v ≠ v → ∀ k : ℕ, (σ^k) v = v → orderOf σ ∣ k) :
    orderOf σ ∣ (movedFinset σ).card := by
  refine orderOf_dvd_card_of_semiRegular σ (movedFinset σ)
    (movedFinset_σ_invariant σ) ?_
  intro v hv k hk
  rw [mem_movedFinset] at hv
  exact hsemi v hv k hk

/-- **Total vertex count formula.**

If σ acts semi-regularly on `V \ Fix(σ)`, then
`Fintype.card V = fixedVertexCount σ + k * orderOf σ` for some `k : ℕ`.

This is the paper-faithful partition: the fixed points contribute
`a₀(σ)`, and the remaining vertices partition into orbits of size
exactly `orderOf σ`.  Downstream Lem 14 / Lem 17 / Lem 18 wrappers use
this to read off the number of free orbits. -/
theorem card_eq_fixedVertexCount_add_orderOf_mul_of_semiRegular_complement
    (σ : Equiv.Perm V)
    (hsemi : ∀ v : V, σ v ≠ v → ∀ k : ℕ, (σ^k) v = v → orderOf σ ∣ k) :
    ∃ k : ℕ, Fintype.card V = fixedVertexCount σ + k * orderOf σ := by
  -- Step 1: |V| = a₀(σ) + |support σ| (complement partition).
  have hsplit : Fintype.card V = fixedVertexCount σ + σ.support.card := by
    rw [fixedVertexCount_eq_card_supportCompl]
    have : σ.support.card + σ.supportᶜ.card = Fintype.card V := by
      rw [add_comm, Finset.card_compl_add_card]
    omega
  -- Step 2: orderOf σ divides |support σ|.
  have hdvd : orderOf σ ∣ σ.support.card := by
    have := orderOf_dvd_card_movedFinset_of_semiRegular_complement σ hsemi
    simpa [movedFinset] using this
  obtain ⟨k, hk⟩ := hdvd
  refine ⟨k, ?_⟩
  rw [hsplit, hk, mul_comm]

end Moore57
