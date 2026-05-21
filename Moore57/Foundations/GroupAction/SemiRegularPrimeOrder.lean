import Moore57.Foundations.GroupAction.SemiRegularOrbit
import Mathlib.GroupTheory.Perm.Finite

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Prime-order semi-regular action

For `σ : Equiv.Perm V` with `σ^p = 1` (p prime), the cyclic action of
`⟨σ⟩` on `V \ Fix(σ)` is **semi-regular**: every non-trivial power of
`σ` moves every `w ∈ V \ Fix(σ)`.

This is the prime-order base case of MS 2010 §6 Lemma 21
(`Fix(σ^l) = Fix(σ)` for `0 < l < orderOf σ`).  The general prime-power
case (`σ^{p^k} = 1` with `k ≥ 2`) is **not** a pure group-action fact:
it requires structural input about how `Fix(σ^p)` relates to `Fix(σ)`,
which is paper Lemma 21's content.

## Proof outline

For σ with `σ^p = 1` (p prime) and `σ w ≠ w`:
- The order of σ divides p, so `orderOf σ ∈ {1, p}`.
- `σ w ≠ w` forces `σ ≠ 1`, hence `orderOf σ = p`.
- For `σ^k w = w`: write `k = q p + r` with `0 ≤ r < p`.
  Then `σ^k = σ^r` (since `σ^p = 1`).
- If `r > 0`, then `gcd(r, p) = 1` (p prime), so by
  `Equiv.Perm.support_pow_coprime`,
  `(σ^r).support = σ.support`.  Hence `w ∈ σ.support` implies
  `(σ^r) w ≠ w`, contradicting `σ^k w = w`.
- So `r = 0`, i.e., `p ∣ k`, i.e., `orderOf σ ∣ k`.

## Main result

* `semiRegular_at_movedPoint_of_prime_orderOf`: σ^p = 1 (p prime) and
  σ w ≠ w ⟹ for all k, `σ^k w = w → orderOf σ ∣ k`.

This unstubs the abstract semi-regular hypothesis in
`SemiRegularComplement.orderOf_dvd_card_movedNeighbour_of_semiRegular`
for the prime-order case, removing the need for a separate
`hsemi` argument in Lem 17 / 18 prime-case wrappers.
-/

namespace Moore57

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **Prime-order semi-regular at a moved point.**

For `σ : Equiv.Perm V` of prime order `p` (i.e., `σ^p = 1` with `p`
prime) and `w ∈ V` with `σ w ≠ w`, the cyclic action of `⟨σ⟩` is
semi-regular at `w`: for every `k : ℕ` with `σ^k w = w`, `orderOf σ` divides `k`.

This is MS 2010 §6 Lemma 21 prime-base-case (`Fix(σ^l) = Fix(σ)` for
`0 < l < orderOf σ`, when `orderOf σ` is prime).

Proof: Reduce `k = q·p + r` with `r < p`.  Then `σ^k = σ^r` since
`σ^p = 1`.  If `r > 0`, `gcd(r, p) = 1` so
`Equiv.Perm.support_pow_coprime` gives `(σ^r).support = σ.support`,
hence `σ^r w ≠ w`, contradicting `σ^k w = w`. -/
theorem semiRegular_at_movedPoint_of_prime_orderOf
    (σ : Equiv.Perm V) (p : ℕ) (hp : Nat.Prime p) (hpp : σ ^ p = 1)
    (w : V) (hw : σ w ≠ w) :
    ∀ k : ℕ, (σ ^ k) w = w → orderOf σ ∣ k := by
  intro k hk
  -- orderOf σ divides p
  have horder_dvd : orderOf σ ∣ p := orderOf_dvd_of_pow_eq_one hpp
  -- σ ≠ 1 (since σ moves w), so orderOf σ ≠ 1
  have horder_eq_p : orderOf σ = p := by
    rcases (Nat.dvd_prime hp).mp horder_dvd with h | h
    · -- orderOf σ = 1 ⟹ σ = 1, contradicting hw
      exfalso
      apply hw
      have hσ1 : σ = 1 := orderOf_eq_one_iff.mp h
      rw [hσ1]; rfl
    · exact h
  rw [horder_eq_p]
  by_contra h_not_dvd
  -- Reduce k mod p
  set r := k % p with hr_def
  have hr_lt : r < p := Nat.mod_lt _ hp.pos
  have hr_pos : 0 < r := by
    rcases Nat.eq_zero_or_pos r with h | h
    · exfalso
      apply h_not_dvd
      exact Nat.dvd_of_mod_eq_zero (hr_def ▸ h)
    · exact h
  have hk_div : k = p * (k / p) + r := (Nat.div_add_mod k p).symm
  -- σ^k = σ^r (using σ^p = 1)
  have hkr : (σ ^ k : Equiv.Perm V) = σ ^ r := by
    conv_lhs => rw [hk_div]
    rw [pow_add, pow_mul, hpp, one_pow, one_mul]
  rw [hkr] at hk
  -- gcd(r, p) = 1 since 0 < r < p and p prime
  have hcoprime_pr : Nat.Coprime p r :=
    hp.coprime_iff_not_dvd.mpr fun hpdvd =>
      absurd (Nat.le_of_dvd hr_pos hpdvd) (not_le.mpr hr_lt)
  have hcoprime_rp : Nat.Coprime r p := hcoprime_pr.symm
  have hcoprime_rord : Nat.Coprime r (orderOf σ) := by
    rw [horder_eq_p]; exact hcoprime_rp
  -- support_pow_coprime: (σ^r).support = σ.support
  have hsupp : (σ ^ r).support = σ.support :=
    Equiv.Perm.support_pow_coprime hcoprime_rord
  -- σ moves w ⟹ w ∈ σ.support ⟹ w ∈ (σ^r).support ⟹ σ^r w ≠ w
  have hw_supp_σ : w ∈ σ.support := Equiv.Perm.mem_support.mpr hw
  have hw_supp_σr : w ∈ (σ ^ r).support := by rw [hsupp]; exact hw_supp_σ
  exact (Equiv.Perm.mem_support.mp hw_supp_σr) hk

end Moore57
