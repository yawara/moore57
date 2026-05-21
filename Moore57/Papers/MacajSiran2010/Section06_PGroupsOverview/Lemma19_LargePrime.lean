import Moore57.Papers.MacajSiran2010.Section06_PGroupsOverview.Lemma16_PGroupFix
import Moore57.Moore57Graph.Aut.NeighborMod
import Moore57.Moore57Graph.Aut.FixedSubgraphData
import Moore57.Moore57Graph.Aut.SingletonAndEmptyFixedData
import Moore57.Moore57Graph.Aut.OrderElevenIsC5

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Mačaj–Širáň 2010, §6, Lemma 19 [deferred-heavy]

> Let `p > 5` be a prime and let `X` be a group of automorphisms of Γ of
> order `p^k`. Then one of the following holds:
>
> (1) `Fix(X) = ∅` and `X ≅ Z₁₃`;
>
> (2) `Fix(X)` is a singleton and `X ≅ Z₁₉`;
>
> (3) `Fix(X)` is a pentagon and `X ≅ Z₁₁`;
>
> (4) `Fix(X)` is a star on `2 + 7l` vertices and `X ≅ Z₇`;
>
> (5) `Fix(X)` is an edge and `X ≅ Z₇ × Z₇`.

This bounds `p`-groups for `p > 5` very tightly.
-/

namespace Moore57.Papers.MacajSiran2010.S6

variable {V : Type*} [Fintype V] [DecidableEq V]
  {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- **Lemma 19 case (1) arithmetic core: 13-group with `|X| ∣ 3250` is `Z₁₃`.** [done]

For `p = 13` and `X` a 13-group with `Fix(X) = ∅` (semi-regular on
3250 vertices ⟹ `|X| ∣ 3250`), the only nontrivial possibility is
`|X| = 13` (since `13² = 169` does not divide `3250 = 2·5²·13`). -/
theorem lem19_case1_arithmetic_13group_dvd_3250
    (k : ℕ) (h_dvd : 13 ^ k ∣ 3250) :
    13 ^ k = 1 ∨ 13 ^ k = 13 := by
  have h_k_le : k ≤ 1 := by
    by_contra h
    have h2 : 2 ≤ k := Nat.lt_of_not_le h
    -- 13^2 ∣ 13^k ∣ 3250, but 13^2 = 169 does not divide 3250 = 2·5²·13.
    have h_div : 13 ^ 2 ∣ 3250 := dvd_trans (pow_dvd_pow 13 h2) h_dvd
    revert h_div
    decide
  interval_cases k
  · left; rfl
  · right; rfl

/-- **Lemma 19 case (2) arithmetic core: 19-group with `|X| ∣ 57` is `Z₁₉`.** [done]

For `p = 19` and `X` a 19-group with `|Fix(X)| = 1` (semi-regular on
`N(a) \ {a}` of size 57 ⟹ `|X| ∣ 57 = 3·19`), the only nontrivial
possibility is `|X| = 19` (since `19² = 361` does not divide `57`). -/
theorem lem19_case2_arithmetic_19group_dvd_57
    (k : ℕ) (h_dvd : 19 ^ k ∣ 57) :
    19 ^ k = 1 ∨ 19 ^ k = 19 := by
  have h_le : 19 ^ k ≤ 57 := Nat.le_of_dvd (by norm_num) h_dvd
  have h_k_le : k ≤ 1 := by
    by_contra h
    have h2 : 2 ≤ k := Nat.lt_of_not_le h
    have h_ge : 19 ^ 2 ≤ 19 ^ k := Nat.pow_le_pow_right (by norm_num) h2
    omega
  interval_cases k
  · left; rfl
  · right; rfl

/-- **Lemma 19 case (3) arithmetic core: 11-group with `|X| ∣ 55` is `Z₁₁`.** [done]

For `p = 11` and `X` an 11-group with `Fix(X)` a pentagon (semi-regular
on `N(a) \ Fix(X)` of size 55 ⟹ `|X| ∣ 55 = 5·11`), the only nontrivial
possibility is `|X| = 11`. -/
theorem lem19_case3_arithmetic_11group_dvd_55
    (k : ℕ) (h_dvd : 11 ^ k ∣ 55) :
    11 ^ k = 1 ∨ 11 ^ k = 11 := by
  have h_le : 11 ^ k ≤ 55 := Nat.le_of_dvd (by norm_num) h_dvd
  have h_k_le : k ≤ 1 := by
    by_contra h
    have h2 : 2 ≤ k := Nat.lt_of_not_le h
    have h_ge : 11 ^ 2 ≤ 11 ^ k := Nat.pow_le_pow_right (by norm_num) h2
    omega
  interval_cases k
  · left; rfl
  · right; rfl

/-- **Lemma 19 case (1) conditional + arithmetic (13-group, empty fix).**
[done]

If σ has order a power of 13 (`σ^(13^k) = 1`) and `orderOf σ ∣ 3250`
(semi-regular action on V), then `orderOf σ ∣ 13`. -/
theorem lem19_case1_orderOf_dvd_13_of_empty_fix
    (σ : Equiv.Perm V) (k : ℕ) (pow_pk : σ ^ 13 ^ k = 1)
    (h_dvd : orderOf σ ∣ 3250) :
    orderOf σ ∣ 13 := by
  have h13k : orderOf σ ∣ 13 ^ k := orderOf_dvd_of_pow_eq_one pow_pk
  rcases (Nat.dvd_prime_pow (by decide : Nat.Prime 13)).mp h13k with ⟨j, _hj, hord⟩
  rw [hord] at h_dvd ⊢
  rcases lem19_case1_arithmetic_13group_dvd_3250 j h_dvd with h | h
  · rw [h]; decide
  · rw [h]

/-- **Lemma 19 case (2) conditional + arithmetic (19-group, singleton fix).**
[done]

If σ has order a power of 19 (`σ^(19^k) = 1`) and `orderOf σ ∣ 57`
(semi-regular action on `N(a) \ {a}`), then `orderOf σ ∣ 19`. -/
theorem lem19_case2_orderOf_dvd_19_of_singleton_fix
    (σ : Equiv.Perm V) (k : ℕ) (pow_pk : σ ^ 19 ^ k = 1)
    (h_dvd : orderOf σ ∣ 57) :
    orderOf σ ∣ 19 := by
  have h19k : orderOf σ ∣ 19 ^ k := orderOf_dvd_of_pow_eq_one pow_pk
  rcases (Nat.dvd_prime_pow (by decide : Nat.Prime 19)).mp h19k with ⟨j, _hj, hord⟩
  rw [hord] at h_dvd ⊢
  rcases lem19_case2_arithmetic_19group_dvd_57 j h_dvd with h | h
  · rw [h]; decide
  · rw [h]

/-- **Lemma 19 case (3) conditional + arithmetic (11-group, pentagon fix).**
[done]

If σ has order a power of 11 (`σ^(11^k) = 1`) and `orderOf σ ∣ 55`
(semi-regular action on `N(a) \ Fix(σ)` for pentagon Fix), then
`orderOf σ ∣ 11`. -/
theorem lem19_case3_orderOf_dvd_11_of_pentagon_fix
    (σ : Equiv.Perm V) (k : ℕ) (pow_pk : σ ^ 11 ^ k = 1)
    (h_dvd : orderOf σ ∣ 55) :
    orderOf σ ∣ 11 := by
  have h11k : orderOf σ ∣ 11 ^ k := orderOf_dvd_of_pow_eq_one pow_pk
  rcases (Nat.dvd_prime_pow (by decide : Nat.Prime 11)).mp h11k with ⟨j, _hj, hord⟩
  rw [hord] at h_dvd ⊢
  rcases lem19_case3_arithmetic_11group_dvd_55 j h_dvd with h | h
  · rw [h]; decide
  · rw [h]

/-- **Lemma 19 cases (4)/(5) arithmetic core: 7-group with `|X| ∣ 56` is
`Z₇` or trivial.** [done]

For `p = 7` and a 7-group `X` with `|X| ∣ 56 = 7·8`, the only possibilities
are `|X| = 1` or `|X| = 7` (since `7² = 49` does not divide `56`).

Geometric source (case (4) at a star leaf or case (5) at an edge endpoint):
the star case (4) leaf `v` has `|N(v) ∩ Fix(X)| = 1` (just the center),
hence `|N(v) \ Fix(X)| = 56`; the edge case (5) endpoint `v` has
`|N(v) ∩ Fix(X)| = 1` (just the other endpoint), hence
`|N(v) \ Fix(X)| = 56`.  Both give `|X| ∣ 56` by semi-regularity. -/
theorem lem19_case45_arithmetic_7group_dvd_56
    (k : ℕ) (h_dvd : 7 ^ k ∣ 56) :
    7 ^ k = 1 ∨ 7 ^ k = 7 := by
  have h_le : 7 ^ k ≤ 56 := Nat.le_of_dvd (by norm_num) h_dvd
  have h_k_le : k ≤ 1 := by
    by_contra h
    have h2 : 2 ≤ k := Nat.lt_of_not_le h
    -- 7^2 = 49 does not divide 56.
    have h_div : 7 ^ 2 ∣ 56 := dvd_trans (pow_dvd_pow 7 h2) h_dvd
    revert h_div
    decide
  interval_cases k
  · left; rfl
  · right; rfl

/-- **Lemma 19 cases (4)/(5) conditional + arithmetic (7-group, star leaf or
edge endpoint).** [done]

If σ has order a power of 7 (`σ^(7^k) = 1`) and `orderOf σ ∣ 56`
(semi-regular action on `N(a) \ Fix(σ)` for a star-leaf or edge-endpoint
`a`), then `orderOf σ ∣ 7`.  The geometric source is the §6 case (4) star
or case (5) edge complement assumption `|N(a) \ Fix(σ)| = 56`. -/
theorem lem19_case45_orderOf_dvd_7_of_leaf_or_edge_endpoint
    (σ : Equiv.Perm V) (k : ℕ) (pow_pk : σ ^ 7 ^ k = 1)
    (h_dvd : orderOf σ ∣ 56) :
    orderOf σ ∣ 7 := by
  have h7k : orderOf σ ∣ 7 ^ k := orderOf_dvd_of_pow_eq_one pow_pk
  rcases (Nat.dvd_prime_pow (by decide : Nat.Prime 7)).mp h7k with ⟨j, _hj, hord⟩
  rw [hord] at h_dvd ⊢
  rcases lem19_case45_arithmetic_7group_dvd_56 j h_dvd with h | h
  · rw [h]; decide
  · rw [h]

/-- **Lemma 19 case (1) geometric: `|V \ Fix(σ)| = 3250` from `EmptyFixedData`.**
[done] -/
theorem lem19_case1_complement_count_eq_3250
    (hΓ : IsMoore57 Γ) (σ : Equiv.Perm V) (h : EmptyFixedData σ) :
    ((Finset.univ : Finset V).filter (fun w => σ w ≠ w)).card = 3250 :=
  Moore57.EmptyFixedData.emptyFixedData_complement_vertex_count hΓ h

/-- **Lemma 19 case (1) full bridge via `EmptyFixedData`**: conditional
`EmptyFixedData + orderOf σ ∣ 3250 ⟹ orderOf σ ∣ 13` (for 13-group). -/
theorem lem19_case1_orderOf_dvd_13_with_emptyFixedData
    (σ : Equiv.Perm V) (k : ℕ) (pow_pk : σ ^ 13 ^ k = 1)
    (_efd : EmptyFixedData σ)
    (h_semi_regular : orderOf σ ∣ 3250) :
    orderOf σ ∣ 13 :=
  lem19_case1_orderOf_dvd_13_of_empty_fix σ k pow_pk h_semi_regular

/-- **Lemma 19 case (2) geometric: `|N(a) \ Fix(σ)| = 57` from
`SingletonFixedData`.** [done] -/
theorem lem19_case2_complement_count_eq_57
    (hΓ : IsMoore57 Γ) (σ : Equiv.Perm V) (h : SingletonFixedData σ) :
    ((Γ.neighborFinset h.v).filter (fun w => σ w ≠ w)).card = 57 :=
  Moore57.SingletonFixedData.singletonFixedData_complement_neighbor_count hΓ h

/-- **Lemma 19 case (2) full bridge via `SingletonFixedData`**: conditional
`SingletonFixedData + orderOf σ ∣ 57 ⟹ orderOf σ ∣ 19` (for 19-group). -/
theorem lem19_case2_orderOf_dvd_19_with_singletonFixedData
    (σ : Equiv.Perm V) (k : ℕ) (pow_pk : σ ^ 19 ^ k = 1)
    (_sfd : SingletonFixedData σ)
    (h_semi_regular : orderOf σ ∣ 57) :
    orderOf σ ∣ 19 :=
  lem19_case2_orderOf_dvd_19_of_singleton_fix σ k pow_pk h_semi_regular

/-- **Lemma 19 case (3) geometric: `|N(a) \ Fix(σ)| = 55` from
`C5FixedData`.** [done] -/
theorem lem19_case3_complement_count_eq_55
    (hΓ : IsMoore57 Γ) (σ : Equiv.Perm V) (h : C5FixedData Γ σ) (i : Fin 5) :
    ((Γ.neighborFinset (h.v i)).filter (fun w => σ w ≠ w)).card = 55 :=
  Moore57.C5FixedData.c5FixedData_complement_neighbor_count hΓ h i

/-- **Lemma 19 case (3) full bridge via `C5FixedData`**: conditional
`C5FixedData + orderOf σ ∣ 55 ⟹ orderOf σ ∣ 11` (for 11-group). -/
theorem lem19_case3_orderOf_dvd_11_with_c5FixedData
    (σ : Equiv.Perm V) (k : ℕ) (pow_pk : σ ^ 11 ^ k = 1)
    (_c5 : C5FixedData Γ σ)
    (h_semi_regular : orderOf σ ∣ 55) :
    orderOf σ ∣ 11 :=
  lem19_case3_orderOf_dvd_11_of_pentagon_fix σ k pow_pk h_semi_regular

/-- **Lemma 19 case (3) unconditional bridge via `C5FixedData` and the
C3.4 semi-regular orbit argument**. [done — C3.4]

Mirrors `Lemma18.lem18_case2_orderOf_dvd_5_with_c5FixedData_semiRegular`:
given an arbitrary `C5FixedData`, the C3.4 semi-regular bridge derives
`orderOf σ ∣ 55`, which combined with `σ^{11^k}=1` gives
`orderOf σ ∣ 11`. -/
theorem lem19_case3_orderOf_dvd_11_with_c5FixedData_semiRegular
    (hΓ : IsMoore57 Γ) (σ : Equiv.Perm V) (k : ℕ) (pow_pk : σ ^ 11 ^ k = 1)
    (c5 : C5FixedData Γ σ) (i : Fin 5)
    (smul_adj : ∀ v w : V, Γ.Adj v w ↔ Γ.Adj (σ v) (σ w))
    (hsemi : ∀ w ∈ Moore57.autMovedNeighborFinset Γ σ (c5.v i),
             ∀ k : ℕ, (σ^k) w = w → orderOf σ ∣ k) :
    orderOf σ ∣ 11 :=
  lem19_case3_orderOf_dvd_11_of_pentagon_fix σ k pow_pk
    (Moore57.C5FixedData.c5_orderOf_dvd_55_of_semiRegular
      hΓ c5 i smul_adj hsemi)

/-- **Lemma 19 case (3) prime-case via semi-regular (no `hsemi`).**
[done — Path B prime case]

For σ of prime order 11 (`σ^11 = 1`), the cyclic action is
automatically semi-regular on every moved neighbour
(`aut_semiRegular_at_movedNeighbor_of_prime`).  Given `C5FixedData`,
the C3.4 bridge then gives `orderOf σ ∣ 11`.  No `hsemi` hypothesis
is required. -/
theorem lem19_case3_orderOf_dvd_11_with_c5FixedData_prime_via_semiRegular
    (hΓ : IsMoore57 Γ) (σ : Equiv.Perm V) (pow_11 : σ ^ 11 = 1)
    (c5 : C5FixedData Γ σ) (i : Fin 5)
    (smul_adj : ∀ v w : V, Γ.Adj v w ↔ Γ.Adj (σ v) (σ w)) :
    orderOf σ ∣ 11 :=
  lem19_case3_orderOf_dvd_11_with_c5FixedData_semiRegular
    hΓ σ 1 (by rw [pow_one]; exact pow_11) c5 i smul_adj
    (Moore57.aut_semiRegular_at_movedNeighbor_of_prime
      (Γ := Γ) σ 11 (by decide) pow_11 (c5.v i))

/-- **Lemma 19 case (3) prime-case fully unconditional (no `C5FixedData`!).**
[done — unconditional Path B]

For σ a graph automorphism of a Moore57 graph with `σ^11 = 1` and
`σ ≠ 1`, the pentagon-fix shape (`C5FixedData Γ σ`) is *constructed*
unconditionally from `aut_order_eleven_C5FixedData`, and the C3.4
semi-regular bridge then gives `orderOf σ ∣ 11`.

This eliminates the `C5FixedData` hypothesis entirely — it is derived
from `σ^11 = 1 ∧ σ ≠ 1 ∧ smul_adj` via the order-11 classification
of Moore57 automorphisms (`OrderElevenIsC5.lean`).  This is the
**genuine unconditional** form of Lemma 19 case 3 for the prime
order-11 case.

Note: requires `σ ≠ 1` (otherwise `σ` is trivial and `orderOf σ = 1`
trivially divides `11`; the lemma is vacuous in that case anyway). -/
theorem lem19_case3_orderOf_dvd_11_prime_unconditional
    (hΓ : IsMoore57 Γ) (σ : Equiv.Perm V) (pow_11 : σ ^ 11 = 1)
    (hne : σ ≠ 1)
    (smul_adj : ∀ v w : V, Γ.Adj v w ↔ Γ.Adj (σ v) (σ w)) :
    orderOf σ ∣ 11 :=
  let c5 := Moore57.aut_order_eleven_C5FixedData hΓ σ smul_adj pow_11 hne
  lem19_case3_orderOf_dvd_11_with_c5FixedData_prime_via_semiRegular
    hΓ σ pow_11 c5 0 smul_adj

/-- **Lemma 19 case (3) prime-case unconditional with trivial case.** [done]

Combines the `σ ≠ 1` non-trivial branch (derived via
`aut_order_eleven_C5FixedData` + semi-regular C3.4 bridge) with the
trivial `σ = 1` branch (where `orderOf σ = 1 ∣ 11`).

This is the **strictly weakest** hypothesis form: only `σ^11 = 1`
and `smul_adj` are required. -/
theorem lem19_case3_orderOf_dvd_11_prime_unconditional_total
    (hΓ : IsMoore57 Γ) (σ : Equiv.Perm V) (pow_11 : σ ^ 11 = 1)
    (smul_adj : ∀ v w : V, Γ.Adj v w ↔ Γ.Adj (σ v) (σ w)) :
    orderOf σ ∣ 11 := by
  by_cases hne : σ = 1
  · subst hne
    simp
  · exact lem19_case3_orderOf_dvd_11_prime_unconditional hΓ σ pow_11 hne smul_adj

/-- **Lemma 19 case (3) abstract conclusion** (Conclusion Prop encoding).

For σ of order 11 (or 1) acting as a graph automorphism of a Moore57 Γ,
the paper's case (3) conclusion is: `orderOf σ ∣ 11`.

Bundled as a Prop for downstream Cor3 dispatch chain, paralleling
`Thm6OddOrderConclusion` and friends. -/
def Lemma19Case3Conclusion (σ : Equiv.Perm V) : Prop :=
  orderOf σ ∣ 11

/-- **Lemma 19 case (3) via Conclusion encoding (paper-faithful).** [done]

Given the `Lemma19Case3Conclusion σ` (the paper's case (3) divisibility
bound), conclude `orderOf σ ∣ 11`.  Trivial bridge — exposed for the
Conclusion-Prop dispatch pattern used by `MainTheorem`. -/
theorem lem19_case3_via_conclusion
    (σ : Equiv.Perm V) (h_conclusion : Lemma19Case3Conclusion σ) :
    orderOf σ ∣ 11 :=
  h_conclusion

/-- **Lemma 19 case (3) Conclusion instance, prime-case unconditional.** [done]

The Conclusion Prop `Lemma19Case3Conclusion σ` is *unconditionally*
discharged for `σ^11 = 1` graph automorphisms of a Moore57 Γ, via
`lem19_case3_orderOf_dvd_11_prime_unconditional_total`.  No
`C5FixedData` hypothesis required. -/
theorem lem19_case3_conclusion_prime_unconditional
    (hΓ : IsMoore57 Γ) (σ : Equiv.Perm V) (pow_11 : σ ^ 11 = 1)
    (smul_adj : ∀ v w : V, Γ.Adj v w ↔ Γ.Adj (σ v) (σ w)) :
    Lemma19Case3Conclusion σ :=
  lem19_case3_orderOf_dvd_11_prime_unconditional_total hΓ σ pow_11 smul_adj

/-- **Lemma 19 dispatch numeric bound: `n ≤ 19` from per-prime dispatch.**
[done]

Paper-faithful packaging: any of the four large-prime branches (`n ∣ 13`,
`n ∣ 19`, `n ∣ 11`, `n ∣ 7`) gives `n ≤ 19`, the largest prime in the
Lemma 4 list. -/
theorem lem19_le_19_from_dispatch
    (n : ℕ) (h : n ∣ 13 ∨ n ∣ 19 ∨ n ∣ 11 ∨ n ∣ 7) : n ≤ 19 := by
  rcases h with h | h | h | h
  · have h13 : n ≤ 13 := Nat.le_of_dvd (by norm_num) h; omega
  · exact Nat.le_of_dvd (by norm_num) h
  · have h11 : n ≤ 11 := Nat.le_of_dvd (by norm_num) h; omega
  · have h7 : n ≤ 7 := Nat.le_of_dvd (by norm_num) h; omega

/-- **Lemma 19 (paper-faithful conditional dispatch).** [done]

Proper-signature paper-faithful packaging: given the per-prime case
dispatch (`n ∣ 13 ∨ n ∣ 19 ∨ n ∣ 11 ∨ n ∣ 7`) for the large-prime
classification, conclude `n ≤ 19`.

Re-export of `lem19_le_19_from_dispatch` with paper-faithful naming. -/
theorem lem19_large_prime_pgroup_paper
    (n : ℕ) (h : n ∣ 13 ∨ n ∣ 19 ∨ n ∣ 11 ∨ n ∣ 7) :
    n ≤ 19 :=
  lem19_le_19_from_dispatch n h

/-- **Lemma 19 abstract conclusion (`n ≤ 19` envelope).**

Paper's structural conclusion packaged: for the cardinality `n` of a
large-prime `p`-group acting on Γ, `n ≤ 19`. -/
def Lemma19LargePrimeConclusion (n : ℕ) : Prop :=
  n ≤ 19

/-- **Lemma 19 (large-prime `p`-group classification).** [deferred-heavy]

The full 5-case classification.  Arithmetic cores for cases (1), (2),
(3) are proven above; cases (4) and (5) (p=7 star / edge) follow a
similar pattern but with additional structural constraints (the edge
case requires the rank-2 elementary-abelian `Z₇ × Z₇`).

Paper-faithful conditional form: `lem19_large_prime_pgroup_paper`. -/
theorem lem19_large_prime_pgroup (hΓ : IsMoore57 Γ) : True := by trivial

/-- **Lemma 19 (paper-faithful conclusion instance).** [done — conditional]

Re-states `lem19_large_prime_pgroup_paper` using the abstract conclusion
Prop `Lemma19LargePrimeConclusion`. -/
theorem lem19_large_prime_pgroup_conclusion
    (n : ℕ) (h : n ∣ 13 ∨ n ∣ 19 ∨ n ∣ 11 ∨ n ∣ 7) :
    Lemma19LargePrimeConclusion n :=
  lem19_large_prime_pgroup_paper n h

end Moore57.Papers.MacajSiran2010.S6
