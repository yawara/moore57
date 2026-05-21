import Moore57.Papers.MacajSiran2010.Section06_PGroupsOverview.Lemma18_5Group
import Moore57.Papers.MacajSiran2010.Section03_EquitablePartitions.Lemma5_AdjacencyMatrix

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Mačaj–Širáň 2010, §8, Proposition 3 [deferred-heavy]

> Let `X` be a group of automorphisms of a Moore (57, 2)-graph Γ of order
> a power of 5. If `Fix(X)` is the Hoffman–Singleton graph, then `|X| ≤ 5`.

Proof outline (paper §8):
1. Assume `|X| = 25`. Then `X` acts semi-regularly on `Γ \ Fix(X)`,
   yielding 50 size-1 + 128 size-25 orbits.
2. Two orbits of size 25 lie in the neighbourhood of each fixed point,
   both with trace 0. The trace of `X` is congruent to `6 mod 15` and at
   most 56, so at least one of the remaining 28 orbits has trace 0.
3. Pick `O₁₇₈` an orbit with zero trace. Analyse the entry
   `Σⱼ b²_{178,j}` in `B² + B − 56 I = 1ᵀ s`.
4. Derive the simultaneous equations
   `Σ b_{178,i} = 7` and `Σ b²_{178,i} = 31` (for `i ∈ {151..177}`).
5. No non-negative integer solution exists — contradiction.
-/

namespace Moore57.Papers.MacajSiran2010.S8

variable {V : Type*} [Fintype V] [DecidableEq V]
  {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- **Proposition 3 arithmetic core: no partition of 7 has square-sum 31.**
[done]

For non-negative integers `x_0, ..., x_7` where `x_k` is the count of
parts equal to `k`, the simultaneous constraints

  `1·x_1 + 2·x_2 + 3·x_3 + 4·x_4 + 5·x_5 + 6·x_6 + 7·x_7 = 7`
  `1·x_1 + 4·x_2 + 9·x_3 + 16·x_4 + 25·x_5 + 36·x_6 + 49·x_7 = 31`

have no solution.

This is the §8 Prop 3 arithmetic core (step 5 of the paper proof):
the simultaneous equations
  `Σⱼ b_{178,j} = 7` and `Σⱼ b²_{178,j} = 31` (for the 27 orbits
`j ∈ {151..177}`) have no non-negative integer solution.

The proof packages the multiset of `b_{178,j}` values via their
value-counts `x_k = |{j : b_{178,j} = k}|`.  omega handles the
non-existence directly. -/
theorem prop3_arithmetic_core_no_partition_of_7_with_sq_31
    (x1 x2 x3 x4 x5 x6 x7 : ℕ)
    (h_sum : x1 + 2 * x2 + 3 * x3 + 4 * x4 + 5 * x5 + 6 * x6 + 7 * x7 = 7)
    (h_sq_sum :
      x1 + 4 * x2 + 9 * x3 + 16 * x4 + 25 * x5 + 36 * x6 + 49 * x7 = 31) :
    False := by
  -- Bound each x_i: x_i = 0 forced for i ≥ 4 except small cases.
  have hx7 : x7 = 0 := by omega
  have hx6 : x6 = 0 := by omega
  have hx5 : x5 ≤ 1 := by omega
  have hx4 : x4 ≤ 1 := by omega
  have hx3 : x3 ≤ 2 := by omega
  have hx2 : x2 ≤ 3 := by omega
  subst hx7
  subst hx6
  interval_cases x5 <;> interval_cases x4 <;>
    interval_cases x3 <;> interval_cases x2 <;> omega

/-- **Proposition 3 prime-case unconditional wrapper.** [done]

For σ a graph automorphism of Γ with σ⁵ = 1 (prime base case k = 1)
and `HSFixedData Γ σ`, the bound `orderOf σ ≤ 5` holds trivially since
`orderOf σ ∣ 5`.  This is the `k = 1` base case of Proposition 3.

The composite case (`σ^{5^k} = 1` with `k ≥ 2`) requires the paper §8
step 1-5 (excluding `|X| = 25` via arithmetic core
`prop3_arithmetic_core_no_partition_of_7_with_sq_31`) and is deferred-
heavy. -/
theorem prop3_hs_fix_bound_prime_unconditional
    (hΓ : IsMoore57 Γ) (σ : Equiv.Perm V) (pow_5 : σ ^ 5 = 1)
    (_hsfd : HSFixedData Γ σ) :
    orderOf σ ≤ 5 := by
  have h : orderOf σ ∣ 5 := orderOf_dvd_of_pow_eq_one pow_5
  exact Nat.le_of_dvd (by norm_num) h

/-- **Proposition 3 (Hoffman–Singleton-fix 5-group `|X| ≤ 5`).** [deferred-heavy] -/
theorem prop3_hs_fix_bound (hΓ : IsMoore57 Γ) : True := by trivial

/-- **Proposition 3 arithmetic step: `n ∣ 25 ∧ n ≠ 25 ⟹ n ≤ 5`.**
[done — C3.6]

Since `25 = 5²`, the divisors of 25 are `{1, 5, 25}`.  Excluding 25
leaves `{1, 5}`, both of which are at most 5. -/
theorem prop3_arithmetic_dvd_25_ne_25_le_5
    (n : ℕ) (h_dvd : n ∣ 25) (h_no_25 : n ≠ 25) :
    n ≤ 5 := by
  rcases (Nat.dvd_prime_pow (by decide : Nat.Prime 5)).mp
    (show n ∣ 5 ^ 2 by simpa using h_dvd) with ⟨j, hj, hn⟩
  interval_cases j
  · omega
  · omega
  · exact absurd hn h_no_25

/-- **Proposition 3 conditional bridge via `HSFixedData` (Lem 18 (1) input
form)**. [done — C3.6]

Given:
* `σ ^ 5^k = 1` (σ is a 5-group element),
* `HSFixedData Γ σ` (Fix(σ) = Hoffman–Singleton),
* `h_semi_regular : orderOf σ ∣ 50` (Lem 18 (1) input — semi-regular
  action of σ on `N(a) \ Fix(σ)`),
* `h_no_25 : orderOf σ ≠ 25` (deferred §8 step 1-5 conclusion: paper's
  trace + orbit + arithmetic-core argument excluding `|X| = 25`),

conclude `orderOf σ ≤ 5`.

This packages the §8 Prop 3 conclusion as a proper conditional bridge:
the `|X| = 25` exclusion (deferred) plus the Lem 18 (1) bound combine to
the paper's stated `|X| ≤ 5`. -/
theorem prop3_hs_fix_bound_with_hsFixedData
    (σ : Equiv.Perm V) (k : ℕ) (pow_pk : σ ^ 5 ^ k = 1)
    (hsfd : HSFixedData Γ σ)
    (h_semi_regular : orderOf σ ∣ 50)
    (h_no_25 : orderOf σ ≠ 25) :
    orderOf σ ≤ 5 :=
  prop3_arithmetic_dvd_25_ne_25_le_5 _
    (Moore57.Papers.MacajSiran2010.S6.lem18_case1_orderOf_dvd_25_with_HSFixedData
      σ k pow_pk hsfd h_semi_regular)
    h_no_25

/-- **Proposition 3 unconditional bridge via `HSFixedData` and the C3.4
semi-regular orbit argument**. [done — C3.6]

Replaces the `h_semi_regular : orderOf σ ∣ 50` numeric hypothesis with
the paper-faithful semi-regular hypothesis on `N(a) \ Fix(σ)`.  The
remaining deferred input is `h_no_25` (paper §8 step 1-5 conclusion). -/
theorem prop3_hs_fix_bound_with_hsFixedData_semiRegular
    (hΓ : IsMoore57 Γ) (σ : Equiv.Perm V) (k : ℕ) (pow_pk : σ ^ 5 ^ k = 1)
    (hsfd : HSFixedData Γ σ) (i : Fin 50)
    (smul_adj : ∀ v w : V, Γ.Adj v w ↔ Γ.Adj (σ v) (σ w))
    (hsemi : ∀ w ∈ Moore57.autMovedNeighborFinset Γ σ (hsfd.v i),
             ∀ k : ℕ, (σ^k) w = w → orderOf σ ∣ k)
    (h_no_25 : orderOf σ ≠ 25) :
    orderOf σ ≤ 5 :=
  prop3_arithmetic_dvd_25_ne_25_le_5 _
    (Moore57.Papers.MacajSiran2010.S6.lem18_case1_orderOf_dvd_25_with_HSFixedData_semiRegular
      hΓ σ k pow_pk hsfd i smul_adj hsemi)
    h_no_25

/-- **Proposition 3 abstract conclusion (paper claim)**: for any 5-group
element σ with HS-shape fix, `|X| ≤ 5`.

This is the Tier B finalize-style abstract `Conclusion : Prop` def for
Proposition 3.  Once the `|X| = 25` exclusion (paper §8 step 1-5) is
Lean-internalised, this becomes provable unconditionally via
`prop3_hs_fix_bound_with_hsFixedData_*`. -/
def Proposition3HSFixConclusion (Γ : SimpleGraph V) : Prop :=
  ∀ (σ : Equiv.Perm V) (k : ℕ),
    σ ^ 5 ^ k = 1 → HSFixedData Γ σ → orderOf σ ≤ 5

/-- **Proposition 3 arithmetic core packaged as the §8 step 5
abstract conclusion**. [done — C3.6]

`prop3_arithmetic_core_no_partition_of_7_with_sq_31` repackaged as a
Prop-level non-existence statement, exposing the §8 step 5 conclusion
in the form usable by downstream `Proposition3` bridges. -/
def Proposition3Step5Conclusion : Prop :=
  ¬ ∃ (x1 x2 x3 x4 x5 x6 x7 : ℕ),
    x1 + 2 * x2 + 3 * x3 + 4 * x4 + 5 * x5 + 6 * x6 + 7 * x7 = 7 ∧
    x1 + 4 * x2 + 9 * x3 + 16 * x4 + 25 * x5 + 36 * x6 + 49 * x7 = 31

theorem prop3_step5_conclusion_holds : Proposition3Step5Conclusion := by
  rintro ⟨x1, x2, x3, x4, x5, x6, x7, h_sum, h_sq⟩
  exact prop3_arithmetic_core_no_partition_of_7_with_sq_31
    x1 x2 x3 x4 x5 x6 x7 h_sum h_sq

/-- **Proposition 3 direct-form Diophantine bridge (paper-faithful).** [done — research]

Paper §8 equations (7) and (8) state:
* `∑_{i=151}^{177} b_{178,i} = 7` (eq 7, degree sum)
* `∑_{i=151}^{177} b_{178,i}² = 31` (eq 8, derived from B² + B − 56I)

These 27 non-negative integer variables admit no simultaneous solution
— the §8 step 5 contradiction.  The proof reduces to the partition-
counting form `prop3_arithmetic_core_no_partition_of_7_with_sq_31`:
define `x_k := |{i : b i = k}|` for `k ∈ {1, ..., 7}`, derive the
partition equations, and apply the arithmetic core.

Note: `b i ≤ 7` is forced by `∑ b = 7` with non-negative integers,
so each `b i ∈ {0, 1, 2, ..., 7}` and the partition variables `x_k`
cover all relevant values. -/
theorem prop3_no_solution_direct (b : Fin 27 → ℕ)
    (h_sum : ∑ i, b i = 7) (h_sum_sq : ∑ i, (b i)^2 = 31) :
    False := by
  -- Each b i ≤ 7 (from non-neg + ∑ = 7)
  have hb_le : ∀ i, b i ≤ 7 := by
    intro i
    have h_mem : b i ≤ ∑ j, b j :=
      Finset.single_le_sum (f := b) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
    omega
  -- Define x_k for k = 1, ..., 7
  set x1 := (Finset.univ.filter fun i : Fin 27 => b i = 1).card with hx1
  set x2 := (Finset.univ.filter fun i : Fin 27 => b i = 2).card with hx2
  set x3 := (Finset.univ.filter fun i : Fin 27 => b i = 3).card with hx3
  set x4 := (Finset.univ.filter fun i : Fin 27 => b i = 4).card with hx4
  set x5 := (Finset.univ.filter fun i : Fin 27 => b i = 5).card with hx5
  set x6 := (Finset.univ.filter fun i : Fin 27 => b i = 6).card with hx6
  set x7 := (Finset.univ.filter fun i : Fin 27 => b i = 7).card with hx7
  -- Bridge: ∑ i, b i = 1·x1 + 2·x2 + ... + 7·x7 (via partition)
  -- We express ∑ i, b i = ∑ k ∈ range 8, k · |{i : b i = k}|
  -- using ∀ i, b i ∈ range 8 (i.e., b i ≤ 7)
  -- Express each b i and (b i)^2 as a sum over k ∈ range 8 of indicator·k (resp. k²)
  have hb_eq : ∀ i, b i = ∑ k ∈ Finset.range 8, if b i = k then k else 0 := by
    intro i
    rw [Finset.sum_ite_eq]
    simp [Finset.mem_range, Nat.lt_succ_of_le (hb_le i)]
  have hb_sq_eq : ∀ i, (b i)^2 = ∑ k ∈ Finset.range 8, if b i = k then k^2 else 0 := by
    intro i
    rw [Finset.sum_ite_eq]
    simp [Finset.mem_range, Nat.lt_succ_of_le (hb_le i)]
  have h_partition_sum :
      ∑ i, b i = x1 + 2 * x2 + 3 * x3 + 4 * x4 + 5 * x5 + 6 * x6 + 7 * x7 := by
    -- Swap the sums and convert to k · x_k
    rw [Finset.sum_congr rfl (fun i _ => hb_eq i), Finset.sum_comm]
    have : ∀ k ∈ Finset.range 8,
        ∑ i, (if b i = k then k else 0) =
          k * (Finset.univ.filter fun i : Fin 27 => b i = k).card := by
      intro k _
      rw [← Finset.sum_filter]
      simp [Finset.sum_const, Nat.mul_comm]
    rw [Finset.sum_congr rfl this]
    -- Unfold ∑ k ∈ range 8 = sum of 8 terms (k=0..7)
    rw [show (8 : ℕ) = 7 + 1 from rfl, Finset.sum_range_succ, Finset.sum_range_succ,
        Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
        Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
        Finset.sum_range_zero]
    ring
  have h_partition_sq :
      ∑ i, (b i)^2 = x1 + 4 * x2 + 9 * x3 + 16 * x4 + 25 * x5 + 36 * x6 + 49 * x7 := by
    rw [Finset.sum_congr rfl (fun i _ => hb_sq_eq i), Finset.sum_comm]
    have : ∀ k ∈ Finset.range 8,
        ∑ i, (if b i = k then k^2 else 0) =
          k^2 * (Finset.univ.filter fun i : Fin 27 => b i = k).card := by
      intro k _
      rw [← Finset.sum_filter]
      simp [Finset.sum_const, Nat.mul_comm]
    rw [Finset.sum_congr rfl this]
    rw [show (8 : ℕ) = 7 + 1 from rfl, Finset.sum_range_succ, Finset.sum_range_succ,
        Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
        Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
        Finset.sum_range_zero]
    ring
  -- Now apply the partition arithmetic core
  have h_sum' : x1 + 2 * x2 + 3 * x3 + 4 * x4 + 5 * x5 + 6 * x6 + 7 * x7 = 7 := by
    rw [← h_partition_sum]; exact h_sum
  have h_sq' : x1 + 4 * x2 + 9 * x3 + 16 * x4 + 25 * x5 + 36 * x6 + 49 * x7 = 31 := by
    rw [← h_partition_sq]; exact h_sum_sq
  exact prop3_arithmetic_core_no_partition_of_7_with_sq_31
    x1 x2 x3 x4 x5 x6 x7 h_sum' h_sq'

/-- **Proposition 3 direct-form step 5 conclusion (paper-faithful)**. [done — research]

The paper-faithful statement of paper §8 step 5: there is no
non-negative integer assignment to 27 variables `b_i` with sum 7 and
sum-of-squares 31.  This is the abstract version of
`prop3_no_solution_direct` exposing the contradiction as a `Prop` def
for downstream use. -/
def Proposition3DirectStep5Conclusion : Prop :=
  ¬ ∃ b : Fin 27 → ℕ, (∑ i, b i = 7) ∧ (∑ i, (b i)^2 = 31)

theorem prop3_direct_step5_conclusion_holds : Proposition3DirectStep5Conclusion := by
  rintro ⟨b, h_sum, h_sq⟩
  exact prop3_no_solution_direct b h_sum h_sq

/-! ### Paper §8 Steps 1-4: trace argument & structural scaffold (Path B research)

Steps 1-4 of MS 2010 §8 Prop 3 derive paper equations (7), (8) from the
hypothesis `|X| = 25`.  The chain involves substantial Moore57-specific
structural analysis:

* **Step 1** (orbit decomposition): semi-regular action of X on `Γ \ Fix(X)`
  yields 50 size-1 orbits (= Fix(X) = HS) + 128 size-25 orbits.
  Of the 128 size-25 orbits, 100 are "fix-neighbourhood" orbits (each
  fixed vertex `a` has exactly 2 orbits in `N(a) \ Fix`, and these are
  pairwise disjoint since common neighbours of two fixed points are in
  Fix(X) by Moore graph μ=1).  The remaining 28 are "free" orbits.

* **Step 2** (fix-N-orbits trace = 0): for any orbit `O ⊂ N(a)` with
  `a ∈ Fix(X)`, two distinct vertices `v, v' ∈ O` are not adjacent
  (else `a` would be a common neighbour of two adjacent vertices,
  contradicting Moore57 girth 5 / `λ = 0`).  Hence `Tr(O) = 0`.

* **Step 3** (free orbits trace ∈ {0, 2}): for orbit `O` of size 25,
  Lem 6 (3) gives `Tr(O) ≤ 2` (X abelian ⟹ central, X has odd order).
  Lem 6 (2) gives `Tr(X)` even.  So `Tr(O) ∈ {0, 2}`.

* **Step 4** (∃ free orbit with trace 0): by Lem 8 (trace mod 15),
  `Tr(X) ≡ -8(178 - 10) ≡ -8 · 168 ≡ 6 (mod 15)`.  Combined with
  `Tr(X) ≤ 56` (= 28 · 2) and `Tr(X)` even, the only possible
  `Tr(X)` values are `{6, 36}`, both `< 56`.  Hence at least
  `28 - 18 = 10` free orbits have trace 0.

These are decomposed below as abstract `Prop` defs (Step 1-3) and
the arithmetic core for Step 4 (purely number-theoretic).  Each is
formalisable independently; the chain through to `prop3_no_solution_direct`
is provided as a conditional bridge.
-/

/-- **Step 1 arithmetic core: orbit decomposition `50 + 100 + 28 = 178`.** [done]

For `|X| = 25 + HSFixedData (|Fix| = 50)`, the semi-regular action of `X`
on `V \ Fix(X)` (3200 vertices) yields `3200 / 25 = 128` size-25 orbits.
Of these, `100` are "fix-neighbourhood" orbits (each of the 50 fixed
vertices has 2 size-25 orbits in `N(a) \ Fix`, pairwise disjoint by
Moore graph μ=1) and `128 - 100 = 28` are "free" orbits.

Total orbit count: `50 (size 1) + 100 (size 25 fix-N) + 28 (size 25 free) = 178`. -/
theorem prop3_step1_orbit_decomposition_arithmetic
    (n_fix n_size25 n_fix_N n_free : ℕ)
    (h_n_fix : n_fix = 50)
    (h_size25_count : n_size25 = (3250 - n_fix) / 25)
    (h_fix_N : n_fix_N = 2 * n_fix)
    (h_total_orbits : n_fix_N + n_free = n_size25) :
    n_free = 28 ∧ n_fix + n_fix_N + n_free = 178 := by
  refine ⟨?_, ?_⟩
  · subst h_n_fix; subst h_size25_count; subst h_fix_N
    omega
  · subst h_n_fix; subst h_size25_count; subst h_fix_N
    omega

/-- **Eq (7) arithmetic core: degree split for `v ∈ O_{178}` gives `Σb = 7`.** [done]

Each vertex `v ∈ O_{178}` (a "free" orbit) has degree `57` in Γ.
The 57 neighbours decompose as:
* `0` in `Fix(X)` (paper assumption: `O_{178}` not connected to Fix)
* `50` in fix-N orbits (Moore graph μ=1: for each fixed `a`, `v` has
  exactly 1 neighbour in `O_{50+i} ∪ O_{100+i}`)
* `0` self-loop within `O_{178}` (paper: `Tr(O_{178}) = 0`)
* `7` in free orbits ≠ `O_{178}` (the `b_{178, j}` for `j ∈ 151..177`)

So `Σ b_{178, j} (j ∈ 151..177) = 57 - 0 - 50 - 0 = 7`. -/
theorem prop3_eq7_arithmetic
    (b_fix_sum b_fix_N_sum b_self b_free_sum : ℕ)
    (h_degree : b_fix_sum + b_fix_N_sum + b_self + b_free_sum = 57)
    (h_b_fix : b_fix_sum = 0)
    (h_b_fix_N : b_fix_N_sum = 50)
    (h_b_self : b_self = 0) :
    b_free_sum = 7 := by omega

/-- **Eq (8) arithmetic core: square-sum decomposition gives `Σb² = 31`.** [done]

By Lem 5(5), `(B² + B - 56I)_{178, 178} = s_{178} = 25` (orbit size).
Decomposing `(B²)_{178, 178} = Σ_l b_{178, l} · b_{l, 178}`:
* `l ∈ Fix`: `b_{178, l} = 0`, contributes 0
* `l ∈ fix-N` (100 orbits, indices 51..150): `b_{l, 178} = b_{178, l}`
  (Lem 5(1), same size 25), and each pair `(50+i, 100+i)` contributes
  `b² + b'² = b + b' = 1` (since `b, b' ∈ {0, 1}`).  Total: 50.
* `l = 178`: `b_{178, 178} = 0` (trace), contributes 0
* `l ∈ 151..177` (free orbits): `Σ b²_{178, l}` (what we want)

So `(B²)_{178, 178} = 0 + 50 + 0 + Σ_{free} b² = 50 + Σ_{free} b²`.
Substituting into Lem 5(5): `50 + Σ_{free} b² + 0 - 56 = 25`, hence
`Σ_{free} b² = 31`. -/
theorem prop3_eq8_arithmetic
    (b_fix_sq_sum b_fix_N_sq_sum b_self_sq b_free_sq_sum : ℕ)
    (h_lem5_5 : b_fix_sq_sum + b_fix_N_sq_sum + b_self_sq + b_free_sq_sum
                = 25 + 56)  -- (B² + B - 56I)_{i,i} = s_i ⟹ (B²)_{i,i} = s_i - b_{i,i} + 56
    (h_b_fix_sq : b_fix_sq_sum = 0)
    (h_b_fix_N_sq : b_fix_N_sq_sum = 50)
    (h_b_self_sq : b_self_sq = 0) :
    b_free_sq_sum = 31 := by omega

/-- **Step 2 structural core: σ-orbit in `N(a)` is an independent set.**
[done — Path B Step 2]

For `σ : Equiv.Perm V` automorphism of Moore57 `Γ`, fixed vertex `a`,
and `v ∈ N(a)`: any two distinct σ-iterates of `v` are non-adjacent.

Equivalently, the σ-orbit `{v, σ v, σ² v, ...}` ⊆ N(a) (which is
σ-invariant) is an independent set in `Γ`.

**Proof**: distinct `σ^k v, σ^l v` are both in `N(a)` (since `σ a = a`
implies `σ^n a = a`, and adjacency is preserved by `σ`).  If they
were adjacent, then `a, σ^k v, σ^l v` would form a triangle,
contradicting `λ = 0` (Moore57's `no_triangle`). -/
theorem prop3_step2_orbit_in_N_a_independent
    (hΓ : IsMoore57 Γ) (σ : Equiv.Perm V) {a : V} (ha : σ a = a)
    (smul_adj : ∀ x y : V, Γ.Adj x y ↔ Γ.Adj (σ x) (σ y))
    (v : V) (hv_adj : Γ.Adj a v) (k l : ℕ)
    (hkl : (σ ^ k) v ≠ (σ ^ l) v) :
    ¬ Γ.Adj ((σ ^ k) v) ((σ ^ l) v) := by
  intro h_adj
  -- σ^k a = a (induction on k)
  have h_pow_a : ∀ n : ℕ, (σ ^ n) a = a := by
    intro n
    induction n with
    | zero => rfl
    | succ m ihm => rw [pow_succ, Equiv.Perm.mul_apply, ha, ihm]
  -- σ^n preserves adjacency (induction on n using smul_adj)
  have hsmul_pow : ∀ n x y, Γ.Adj x y → Γ.Adj ((σ ^ n) x) ((σ ^ n) y) := by
    intro n
    induction n with
    | zero =>
        intro x y h; simpa using h
    | succ m ihm =>
        intro x y h
        rw [pow_succ, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply]
        exact ihm (σ x) (σ y) ((smul_adj x y).mp h)
  -- a is adjacent to both σ^k v and σ^l v
  have hk_adj : Γ.Adj a ((σ ^ k) v) := by
    have := hsmul_pow k a v hv_adj
    rwa [h_pow_a k] at this
  have hl_adj : Γ.Adj a ((σ ^ l) v) := by
    have := hsmul_pow l a v hv_adj
    rwa [h_pow_a l] at this
  -- Triangle: a — σ^k v — σ^l v — a, contradicting no_triangle
  exact hΓ.no_triangle hk_adj h_adj hl_adj.symm

/-- **Step 3 arithmetic core: `Tr(O) ≤ 2 ∧ even ⟹ Tr(O) ∈ {0, 2}`.** [done]

For an orbit `O` of size 25, Lem 6 (3) gives `Tr(O) ≤ 2` (X abelian,
central element argument).  Lem 6 (2) gives `Tr(O)` even (X has odd
order).  Together, `Tr(O) ∈ {0, 2}`.

This is a tiny arithmetic step packaging the two Lem 6 inputs. -/
theorem prop3_step3_arithmetic_orbit_trace_in_zero_two
    (n : ℕ) (h_le : n ≤ 2) (h_even : 2 ∣ n) : n = 0 ∨ n = 2 := by
  interval_cases n <;> omega

/-- **Step 4 arithmetic core: 28 trace-2 orbits forces `2 · n_two ≢ 6 [MOD 15]`.** [done]

If we have `n_zero` trace-0 orbits and `n_two` trace-2 orbits among the
28 "free" orbits (with `n_zero + n_two = 28`), and if `2 · n_two ≡ 6 [MOD 15]`
(from Lem 8 + the 100 fix-N orbits contributing 0 to trace), then
`n_zero ≥ 1` (in fact `n_zero ≥ 10`).

Proof: `2 · n_two ≤ 56` and `≡ 6 (mod 15)` ⟹ `2 · n_two ∈ {6, 36}`,
i.e., `n_two ∈ {3, 18}`.  In both cases `n_two ≤ 18 < 28`, so
`n_zero ≥ 10`. -/
theorem prop3_step4_arithmetic_zero_orbit_exists
    (n_zero n_two : ℕ)
    (h_total : n_zero + n_two = 28)
    (h_mod : 2 * n_two ≡ 6 [MOD 15]) :
    10 ≤ n_zero := by
  -- n_two ≤ 28 from h_total
  have h_n_two_le : n_two ≤ 28 := by omega
  -- Enumerate n_two ∈ {0, 1, ..., 28} and check mod 15 constraint
  have h_n_two_le_18 : n_two ≤ 18 := by
    rw [Nat.ModEq] at h_mod
    interval_cases n_two <;> omega
  omega

/-- **Step 4 arithmetic: existence of zero-trace orbit (weak form).** [done]

The weaker version of `prop3_step4_arithmetic_zero_orbit_exists`:
just `n_zero ≥ 1` (matching paper's stated claim). -/
theorem prop3_step4_arithmetic_at_least_one_zero
    (n_zero n_two : ℕ)
    (h_total : n_zero + n_two = 28)
    (h_mod : 2 * n_two ≡ 6 [MOD 15]) :
    1 ≤ n_zero :=
  le_trans (by omega) (prop3_step4_arithmetic_zero_orbit_exists n_zero n_two h_total h_mod)

/-- **Step 4 arithmetic: `n_two ∈ {3, 18}` exactly.** [done]

Strongest form: the modular + bound constraints force `n_two` to be
exactly 3 or 18 (so `Tr(X) ∈ {6, 36}`). -/
theorem prop3_step4_arithmetic_two_count_eq
    (n_two : ℕ)
    (h_le : n_two ≤ 28)
    (h_mod : 2 * n_two ≡ 6 [MOD 15]) :
    n_two = 3 ∨ n_two = 18 := by
  rw [Nat.ModEq] at h_mod
  interval_cases n_two <;> omega

/-- **Proposition 3 Step 1-4 conclusion (abstract paper-faithful)**.

Steps 1-4 combined: from `|X| = 25 + HSFixedData`, produce the eq (7)+(8)
witness `b : Fin 27 → ℕ` for application to `prop3_no_solution_direct`.

This is a paper-faithful encoding of the deferred structural chain
(Moore57 orbit decomposition + trace argument + zero-trace-orbit
selection + quotient adjacency entries).  Once this conclusion is
witnessed in Lean, the §8 step 5 contradiction follows via
`prop3_no_solution_direct`. -/
def Proposition3Step1To4Conclusion (Γ : SimpleGraph V) : Prop :=
  ∀ (σ : Equiv.Perm V), orderOf σ = 25 → HSFixedData Γ σ →
    ∃ b : Fin 27 → ℕ, (∑ i, b i = 7) ∧ (∑ i, (b i)^2 = 31)

/-- **Proposition 3 `|X| ≠ 25` via structural Step 1-4 conclusion**.  [done — bridge]

Combines the deferred `Proposition3Step1To4Conclusion` (witness construction)
with the proven `prop3_no_solution_direct` (no-solution) to derive
`orderOf σ ≠ 25` for any `σ` with `HSFixedData`.

This provides the `h_no_25` hypothesis required by
`prop3_hs_fix_bound_with_hsFixedData_semiRegular` for full Prop 3
unstubbing — conditional on `Proposition3Step1To4Conclusion Γ`. -/
theorem prop3_no_order_25_via_steps_1_to_4
    (σ : Equiv.Perm V) (hsfd : HSFixedData Γ σ)
    (h_steps : Proposition3Step1To4Conclusion Γ) :
    orderOf σ ≠ 25 := by
  intro h_eq
  obtain ⟨b, h_sum, h_sq⟩ := h_steps σ h_eq hsfd
  exact prop3_no_solution_direct b h_sum h_sq

/-- **Proposition 3 full bound via Steps 1-4 + 5**.  [done — bridge]

The final chain: given the (deferred) structural Step 1-4 conclusion,
plus the proven C3.4 semi-regular orbit bridge, derive the paper's
`|X| ≤ 5` bound (Proposition 3 statement) unconditionally on the
arithmetic side.

The remaining deferred work is `Proposition3Step1To4Conclusion`
(the structural Moore57 analysis producing `b` from `|X| = 25`). -/
theorem prop3_hs_fix_bound_via_steps_1_to_4
    (hΓ : IsMoore57 Γ) (σ : Equiv.Perm V) (k : ℕ) (pow_pk : σ ^ 5 ^ k = 1)
    (hsfd : HSFixedData Γ σ) (i : Fin 50)
    (smul_adj : ∀ v w : V, Γ.Adj v w ↔ Γ.Adj (σ v) (σ w))
    (hsemi : ∀ w ∈ Moore57.autMovedNeighborFinset Γ σ (hsfd.v i),
             ∀ k : ℕ, (σ^k) w = w → orderOf σ ∣ k)
    (h_steps : Proposition3Step1To4Conclusion Γ) :
    orderOf σ ≤ 5 :=
  prop3_hs_fix_bound_with_hsFixedData_semiRegular hΓ σ k pow_pk hsfd i smul_adj hsemi
    (prop3_no_order_25_via_steps_1_to_4 σ hsfd h_steps)

end Moore57.Papers.MacajSiran2010.S8
