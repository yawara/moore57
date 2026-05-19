import Moore57.Moore57Graph.Aut.CommonNeighbor
import Moore57.Moore57Graph.Aut.InducedSubgraph
import Moore57.Moore57Graph.Aut.NeighborMod
import Mathlib.Combinatorics.SimpleGraph.StronglyRegular
import Mathlib.Combinatorics.Enumerative.DoubleCounting

/-!
# Fixed-vertex count of an order-19 Moore57 automorphism (Tier 2)

Abstract version of `D19OnMoore57/Rotation/FixedCardinality.lean`. For an
automorphism `σ : Equiv.Perm V` of a Moore57 graph satisfying `σ ^ 19 = 1`
and `σ ≠ 1`, the number of σ-fixed vertices is exactly `1`.

This is the order-19 specialisation of Mačaj–Širáň's Lemma 1 in
`tmp/pdfs/j.laa.2009.07.018.txt`. The proof reuses

* `aut_exists_fixed_commonNeighbor_of_not_adj` — uniqueness of fixed common
  neighbours,
* `aut_card_fixedNeighborFinset_modEq_zero` — mod-19 fixed-neighbour count,
* `autFixedInducedGraph_isSRGWith_of_regular` — SRG inheritance of the fixed
  induced graph,
* mathlib's `SimpleGraph.IsSRGWith.param_eq` and bipartite double counting.

The D₁₉ theorems in `Rotation/FixedCardinality.lean` are specialisations of
the results in this file.
-/

namespace Moore57

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-! ### Modular constraints from `σ ^ p = 1` (general prime p) -/

/-- Generic version. For a permutation `σ : Equiv.Perm V` with `σ ^ p = 1`
(p prime), `fixedVertexCount σ ≡ Fintype.card V [MOD p]`. -/
theorem aut_fixedVertexCount_modEq_card_of_pow_prime
    (σ : Equiv.Perm V) (p : ℕ) [Fact (Nat.Prime p)]
    (pow_p : σ ^ p = 1) :
    fixedVertexCount σ ≡ Fintype.card V [MOD p] := by
  classical
  have hpow : σ ^ p ^ 1 = 1 := by simpa using pow_p
  have hmod := Equiv.Perm.card_compl_support_modEq
    (α := V) (p := p) (n := 1) (σ := σ) hpow
  have hcompl : σ.supportᶜ.card = fixedVertexCount σ := by
    simp [fixedVertexCount, Equiv.Perm.support]
  simpa [hcompl] using hmod

/-- **Prime-power generalisation.** For a permutation `σ : Equiv.Perm V` with
`σ ^ (p ^ n) = 1` (p prime), `fixedVertexCount σ ≡ Fintype.card V [MOD p]`.

This is the natural generalisation of
`aut_fixedVertexCount_modEq_card_of_pow_prime`: instead of `σ` having prime
order, we allow `σ` to have order dividing a prime power.  The
mod-`p` constraint on fixed-point counts is unchanged.

Used in §6 (Lemma 16, 17, 18, 19) where one considers cyclic subgroups of
order `p^k` inside a `p`-group of automorphisms. -/
theorem aut_fixedVertexCount_modEq_card_of_pow_prime_pow
    (σ : Equiv.Perm V) (p n : ℕ) [Fact (Nat.Prime p)]
    (pow_pn : σ ^ p ^ n = 1) :
    fixedVertexCount σ ≡ Fintype.card V [MOD p] := by
  classical
  have hmod := Equiv.Perm.card_compl_support_modEq
    (α := V) (p := p) (n := n) (σ := σ) pow_pn
  have hcompl : σ.supportᶜ.card = fixedVertexCount σ := by
    simp [fixedVertexCount, Equiv.Perm.support]
  simpa [hcompl] using hmod

/-! ### Modular constraints from `σ ^ 19 = 1` -/

/-- For an automorphism `σ` of Moore57 with `σ ^ 19 = 1`, `fixedVertexCount σ ≡
1 (mod 19)`. -/
theorem aut_fixedVertexCount_modEq_one_of_pow_nineteen
    (hΓ : IsMoore57 Γ) (σ : Equiv.Perm V)
    (pow_nineteen : σ ^ 19 = 1) :
    fixedVertexCount σ ≡ 1 [MOD 19] := by
  haveI : Fact (Nat.Prime 19) := ⟨by decide⟩
  have hmod1 : fixedVertexCount σ ≡ Fintype.card V [MOD 19] :=
    aut_fixedVertexCount_modEq_card_of_pow_prime σ 19 pow_nineteen
  have hVmod : Fintype.card V ≡ 1 [MOD 19] := by
    rw [hΓ.card]; decide
  exact hmod1.trans hVmod

/-- Hence the fixed count is positive. -/
theorem aut_fixedVertexCount_pos_of_pow_nineteen
    (hΓ : IsMoore57 Γ) (σ : Equiv.Perm V)
    (pow_nineteen : σ ^ 19 = 1) :
    0 < fixedVertexCount σ := by
  by_contra hpos
  have hzero : fixedVertexCount σ = 0 := Nat.eq_zero_of_not_pos hpos
  have hmod := aut_fixedVertexCount_modEq_one_of_pow_nineteen hΓ σ pow_nineteen
  rw [hzero] at hmod
  exact absurd hmod (by decide)

/-! ### Prime-power-order Moore57 modular constraints

For each prime `p`, an automorphism `σ` with `σ ^ p^k = 1` has
fixed-vertex count `fixedVertexCount σ ≡ 3250 [MOD p]`.  These are
direct corollaries of `aut_fixedVertexCount_modEq_card_of_pow_prime_pow`
specialised to `|V| = 3250` from `IsMoore57`. -/

/-- 13-group fixed count: `3250 = 13 · 250`, hence `fixedVertexCount σ ≡ 0
(mod 13)`. -/
theorem aut_fixedVertexCount_modEq_zero_of_pow_thirteen_pow
    (hΓ : IsMoore57 Γ) (σ : Equiv.Perm V) (k : ℕ)
    (pow_pk : σ ^ 13 ^ k = 1) :
    fixedVertexCount σ ≡ 0 [MOD 13] := by
  haveI : Fact (Nat.Prime 13) := ⟨by decide⟩
  have hmod1 : fixedVertexCount σ ≡ Fintype.card V [MOD 13] :=
    aut_fixedVertexCount_modEq_card_of_pow_prime_pow σ 13 k pow_pk
  have hVmod : Fintype.card V ≡ 0 [MOD 13] := by
    rw [hΓ.card]; decide
  exact hmod1.trans hVmod

/-- 5-group fixed count: `3250 = 5^2 · 130`, hence `fixedVertexCount σ ≡ 0
(mod 5)`. -/
theorem aut_fixedVertexCount_modEq_zero_of_pow_five_pow
    (hΓ : IsMoore57 Γ) (σ : Equiv.Perm V) (k : ℕ)
    (pow_pk : σ ^ 5 ^ k = 1) :
    fixedVertexCount σ ≡ 0 [MOD 5] := by
  haveI : Fact (Nat.Prime 5) := ⟨by decide⟩
  have hmod1 : fixedVertexCount σ ≡ Fintype.card V [MOD 5] :=
    aut_fixedVertexCount_modEq_card_of_pow_prime_pow σ 5 k pow_pk
  have hVmod : Fintype.card V ≡ 0 [MOD 5] := by
    rw [hΓ.card]; decide
  exact hmod1.trans hVmod

/-- 3-group fixed count: `3250 = 3 · 1083 + 1`, hence `fixedVertexCount σ ≡ 1
(mod 3)`.  This is the §6 Lemma 17 modular ingredient: `|Fix(X)|` for
a 3-group `X` must be `≡ 1 (mod 3)`, ruling out empty fix and forcing
case (1) `Fix(X) = Petersen` (10 ≡ 1) or case (2) singleton (1 ≡ 1). -/
theorem aut_fixedVertexCount_modEq_one_of_pow_three_pow
    (hΓ : IsMoore57 Γ) (σ : Equiv.Perm V) (k : ℕ)
    (pow_pk : σ ^ 3 ^ k = 1) :
    fixedVertexCount σ ≡ 1 [MOD 3] := by
  haveI : Fact (Nat.Prime 3) := ⟨by decide⟩
  have hmod1 : fixedVertexCount σ ≡ Fintype.card V [MOD 3] :=
    aut_fixedVertexCount_modEq_card_of_pow_prime_pow σ 3 k pow_pk
  have hVmod : Fintype.card V ≡ 1 [MOD 3] := by
    rw [hΓ.card]; decide
  exact hmod1.trans hVmod

/-- 7-group fixed count: `3250 = 7 · 464 + 2`, hence `fixedVertexCount σ ≡ 2
(mod 7)`.  Used in §6 Lemma 19 case (4): `Fix(X)` is a star
`K_{1, 1+7l}` of size `2 + 7l ≡ 2 (mod 7)`, and case (5): edge of size 2. -/
theorem aut_fixedVertexCount_modEq_two_of_pow_seven_pow
    (hΓ : IsMoore57 Γ) (σ : Equiv.Perm V) (k : ℕ)
    (pow_pk : σ ^ 7 ^ k = 1) :
    fixedVertexCount σ ≡ 2 [MOD 7] := by
  haveI : Fact (Nat.Prime 7) := ⟨by decide⟩
  have hmod1 : fixedVertexCount σ ≡ Fintype.card V [MOD 7] :=
    aut_fixedVertexCount_modEq_card_of_pow_prime_pow σ 7 k pow_pk
  have hVmod : Fintype.card V ≡ 2 [MOD 7] := by
    rw [hΓ.card]; decide
  exact hmod1.trans hVmod

/-- 19-group fixed count: `3250 = 19 · 171 + 1`, hence `fixedVertexCount σ ≡ 1
(mod 19)`.  Used in §6 Lemma 19 case (2): `Fix(X) = {a}` (size 1). -/
theorem aut_fixedVertexCount_modEq_one_of_pow_nineteen_pow
    (hΓ : IsMoore57 Γ) (σ : Equiv.Perm V) (k : ℕ)
    (pow_pk : σ ^ 19 ^ k = 1) :
    fixedVertexCount σ ≡ 1 [MOD 19] := by
  haveI : Fact (Nat.Prime 19) := ⟨by decide⟩
  have hmod1 : fixedVertexCount σ ≡ Fintype.card V [MOD 19] :=
    aut_fixedVertexCount_modEq_card_of_pow_prime_pow σ 19 k pow_pk
  have hVmod : Fintype.card V ≡ 1 [MOD 19] := by
    rw [hΓ.card]; decide
  exact hmod1.trans hVmod

/-- 11-group fixed count: `3250 = 11 · 295 + 5`, hence `fixedVertexCount σ ≡ 5
(mod 11)`.  Used in §6 Lemma 19 case (3): `Fix(X)` is a pentagon
(size 5 ≡ 5). -/
theorem aut_fixedVertexCount_modEq_five_of_pow_eleven_pow
    (hΓ : IsMoore57 Γ) (σ : Equiv.Perm V) (k : ℕ)
    (pow_pk : σ ^ 11 ^ k = 1) :
    fixedVertexCount σ ≡ 5 [MOD 11] := by
  haveI : Fact (Nat.Prime 11) := ⟨by decide⟩
  have hmod1 : fixedVertexCount σ ≡ Fintype.card V [MOD 11] :=
    aut_fixedVertexCount_modEq_card_of_pow_prime_pow σ 11 k pow_pk
  have hVmod : Fintype.card V ≡ 5 [MOD 11] := by
    rw [hΓ.card]; decide
  exact hmod1.trans hVmod

/-- **3-group fix is non-empty.** `0 < fixedVertexCount σ` whenever
`σ ^ 3^k = 1`.  (Since `fixedVertexCount σ ≡ 1 (mod 3) ≠ 0`.) -/
theorem aut_fixedVertexCount_pos_of_pow_three_pow
    (hΓ : IsMoore57 Γ) (σ : Equiv.Perm V) (k : ℕ)
    (pow_pk : σ ^ 3 ^ k = 1) :
    0 < fixedVertexCount σ := by
  by_contra hpos
  have hzero : fixedVertexCount σ = 0 := Nat.eq_zero_of_not_pos hpos
  have hmod := aut_fixedVertexCount_modEq_one_of_pow_three_pow hΓ σ k pow_pk
  rw [hzero] at hmod
  exact absurd hmod (by decide)

/-- **7-group fix has size ≥ 2.** `2 ≤ fixedVertexCount σ` whenever
`σ ^ 7^k = 1`.  (Since `fixedVertexCount σ ≡ 2 (mod 7)` and the values
`0` and `1` violate this congruence.) -/
theorem aut_fixedVertexCount_ge_two_of_pow_seven_pow
    (hΓ : IsMoore57 Γ) (σ : Equiv.Perm V) (k : ℕ)
    (pow_pk : σ ^ 7 ^ k = 1) :
    2 ≤ fixedVertexCount σ := by
  have hmod := aut_fixedVertexCount_modEq_two_of_pow_seven_pow hΓ σ k pow_pk
  by_contra hlt
  have hlt' : fixedVertexCount σ < 2 := Nat.lt_of_not_le hlt
  interval_cases (fixedVertexCount σ) <;> exact absurd hmod (by decide)

/-- **19-group fix is non-empty.** `0 < fixedVertexCount σ` whenever
`σ ^ 19^k = 1`.  (Since `fixedVertexCount σ ≡ 1 (mod 19) ≠ 0`.) -/
theorem aut_fixedVertexCount_pos_of_pow_nineteen_pow
    (hΓ : IsMoore57 Γ) (σ : Equiv.Perm V) (k : ℕ)
    (pow_pk : σ ^ 19 ^ k = 1) :
    0 < fixedVertexCount σ := by
  by_contra hpos
  have hzero : fixedVertexCount σ = 0 := Nat.eq_zero_of_not_pos hpos
  have hmod := aut_fixedVertexCount_modEq_one_of_pow_nineteen_pow hΓ σ k pow_pk
  rw [hzero] at hmod
  exact absurd hmod (by decide)

/-- **11-group fix has size ≥ 5.** `5 ≤ fixedVertexCount σ` whenever
`σ ^ 11^k = 1`.  (Since `fixedVertexCount σ ≡ 5 (mod 11)` and values
`< 5` violate this congruence.) -/
theorem aut_fixedVertexCount_ge_five_of_pow_eleven_pow
    (hΓ : IsMoore57 Γ) (σ : Equiv.Perm V) (k : ℕ)
    (pow_pk : σ ^ 11 ^ k = 1) :
    5 ≤ fixedVertexCount σ := by
  have hmod := aut_fixedVertexCount_modEq_five_of_pow_eleven_pow hΓ σ k pow_pk
  by_contra hlt
  have hlt' : fixedVertexCount σ < 5 := Nat.lt_of_not_le hlt
  interval_cases (fixedVertexCount σ) <;> exact absurd hmod (by decide)

/-! ### Modular constraints from `σ ^ 11 = 1` (Moore57 specialisation) -/

/-- For an automorphism `σ` of Moore57 with `σ ^ 11 = 1`, `fixedVertexCount σ ≡
5 (mod 11)`. (3250 = 11·295 + 5.) -/
theorem aut_fixedVertexCount_modEq_five_of_pow_eleven
    (hΓ : IsMoore57 Γ) (σ : Equiv.Perm V)
    (pow_eleven : σ ^ 11 = 1) :
    fixedVertexCount σ ≡ 5 [MOD 11] := by
  haveI : Fact (Nat.Prime 11) := ⟨by decide⟩
  have hmod1 : fixedVertexCount σ ≡ Fintype.card V [MOD 11] :=
    aut_fixedVertexCount_modEq_card_of_pow_prime σ 11 pow_eleven
  have hVmod : Fintype.card V ≡ 5 [MOD 11] := by
    rw [hΓ.card]; decide
  exact hmod1.trans hVmod

/-- Hence the fixed count is at least 5 (in particular positive). -/
theorem aut_fixedVertexCount_pos_of_pow_eleven
    (hΓ : IsMoore57 Γ) (σ : Equiv.Perm V)
    (pow_eleven : σ ^ 11 = 1) :
    0 < fixedVertexCount σ := by
  by_contra hpos
  have hzero : fixedVertexCount σ = 0 := Nat.eq_zero_of_not_pos hpos
  have hmod := aut_fixedVertexCount_modEq_five_of_pow_eleven hΓ σ pow_eleven
  rw [hzero] at hmod
  exact absurd hmod (by decide)

/-- Stronger: at least 5 fixed vertices. -/
theorem aut_fixedVertexCount_ge_five_of_pow_eleven
    (hΓ : IsMoore57 Γ) (σ : Equiv.Perm V)
    (pow_eleven : σ ^ 11 = 1) :
    5 ≤ fixedVertexCount σ := by
  have hmod := aut_fixedVertexCount_modEq_five_of_pow_eleven hΓ σ pow_eleven
  by_contra hlt
  have hlt' : fixedVertexCount σ < 5 := Nat.lt_of_not_le hlt
  interval_cases (fixedVertexCount σ) <;> exact absurd hmod (by decide)

/-- For a non-identity automorphism, the fixed count is strictly less than
the total vertex count. -/
theorem aut_fixedVertexCount_lt_card
    (σ : Equiv.Perm V) (hne : σ ≠ 1) :
    fixedVertexCount σ < Fintype.card V := by
  classical
  have hle :
      fixedVertexCount σ ≤ Fintype.card V := by
    simpa [fixedVertexCount] using
      (Finset.card_filter_le (Finset.univ : Finset V) (fun v => σ v = v))
  refine lt_of_le_of_ne hle ?_
  intro hcard
  apply hne
  ext v
  have hall :
      ∀ x ∈ (Finset.univ : Finset V), σ x = x := by
    exact (Finset.card_filter_eq_iff
      (s := (Finset.univ : Finset V))
      (p := fun x => σ x = x)).1
        (by simpa [fixedVertexCount] using hcard)
  exact hall v (Finset.mem_univ v)

/-! ### Existence of another fixed vertex, and lower bound for fixed-neighbour
count -/

/-- If the fixed count is not `1`, every fixed vertex has another fixed vertex
to compare with. -/
theorem aut_exists_other_fixed_of_fixedVertexCount_ne_one
    {σ : Equiv.Perm V} {v : V}
    (hv : σ v = v) (hcount : fixedVertexCount σ ≠ 1) :
    ∃ w, w ≠ v ∧ σ w = w := by
  classical
  let S := fixedVertexSet σ
  have hcard_ne : Fintype.card S ≠ 1 := by
    intro hcard
    apply hcount
    simpa [S, fixedVertexCount_eq_card_fixedVertexSet] using hcard
  have hpos : 0 < Fintype.card S := by
    rw [Fintype.card_pos_iff]
    exact ⟨⟨v, hv⟩⟩
  have hone : 1 < Fintype.card S := by omega
  rcases Fintype.one_lt_card_iff.mp hone with ⟨x, y, hxy⟩
  by_cases hxv : (x : V) = v
  · refine ⟨y, ?_, y.property⟩
    intro hyv
    exact hxy (Subtype.ext (hxv.trans hyv.symm))
  · exact ⟨x, hxv, x.property⟩

/-- If `v` is fixed and the fixed count differs from `1`, there is a fixed
neighbour of `v`. -/
theorem aut_exists_mem_fixedNeighborFinset_of_exists_other_fixed
    (hΓ : IsMoore57 Γ) (σ : Equiv.Perm V)
    (smul_adj : ∀ v w : V, Γ.Adj v w ↔ Γ.Adj (σ v) (σ w))
    {v : V} (hv : σ v = v)
    (hother : ∃ w, w ≠ v ∧ σ w = w) :
    ∃ z, z ∈ autFixedNeighborFinset Γ σ v := by
  classical
  rcases hother with ⟨w, hw_ne_v, hw⟩
  by_cases hvw_adj : Γ.Adj v w
  · exact ⟨w, by simp [mem_autFixedNeighborFinset, hvw_adj, hw]⟩
  · have hv_ne_w : v ≠ w := fun hvw => hw_ne_v hvw.symm
    rcases aut_exists_fixed_commonNeighbor_of_not_adj hΓ σ smul_adj
        hv hw hv_ne_w hvw_adj with ⟨z, hz, hzv, _hzw⟩
    exact ⟨z, by simp [mem_autFixedNeighborFinset, hzv, hz]⟩

theorem aut_card_fixedNeighborFinset_pos_of_exists_other_fixed
    (hΓ : IsMoore57 Γ) (σ : Equiv.Perm V)
    (smul_adj : ∀ v w : V, Γ.Adj v w ↔ Γ.Adj (σ v) (σ w))
    {v : V} (hv : σ v = v)
    (hother : ∃ w, w ≠ v ∧ σ w = w) :
    0 < (autFixedNeighborFinset Γ σ v).card := by
  rcases aut_exists_mem_fixedNeighborFinset_of_exists_other_fixed hΓ σ smul_adj
    hv hother with ⟨z, hz⟩
  exact Finset.card_pos.mpr ⟨z, hz⟩

theorem aut_card_fixedNeighborFinset_ge_nineteen_of_exists_other_fixed
    (hΓ : IsMoore57 Γ) (σ : Equiv.Perm V)
    (smul_adj : ∀ v w : V, Γ.Adj v w ↔ Γ.Adj (σ v) (σ w))
    (pow_nineteen : σ ^ 19 = 1)
    {v : V} (hv : σ v = v)
    (hother : ∃ w, w ≠ v ∧ σ w = w) :
    19 ≤ (autFixedNeighborFinset Γ σ v).card := by
  have hpos := aut_card_fixedNeighborFinset_pos_of_exists_other_fixed hΓ σ smul_adj hv hother
  have hmod := aut_card_fixedNeighborFinset_modEq_zero hΓ σ smul_adj pow_nineteen hv
  exact Nat.le_of_dvd hpos (Nat.modEq_zero_iff_dvd.mp hmod)

theorem aut_card_fixedNeighborFinset_ge_nineteen_of_fixedVertexCount_ne_one
    (hΓ : IsMoore57 Γ) (σ : Equiv.Perm V)
    (smul_adj : ∀ v w : V, Γ.Adj v w ↔ Γ.Adj (σ v) (σ w))
    (pow_nineteen : σ ^ 19 = 1)
    {v : V} (hv : σ v = v)
    (hcount : fixedVertexCount σ ≠ 1) :
    19 ≤ (autFixedNeighborFinset Γ σ v).card := by
  rcases aut_exists_other_fixed_of_fixedVertexCount_ne_one hv hcount with ⟨w, hw_ne_v, hw⟩
  exact aut_card_fixedNeighborFinset_ge_nineteen_of_exists_other_fixed hΓ σ smul_adj
    pow_nineteen hv ⟨w, hw_ne_v, hw⟩

/-! ### Upper bound and 19/38/57 dichotomy -/

theorem aut_fixedNeighborFinset_subset_neighborFinset
    (σ : Equiv.Perm V) (v : V) :
    autFixedNeighborFinset Γ σ v ⊆ Γ.neighborFinset v := by
  intro w hw
  exact (Finset.mem_filter.mp hw).1

theorem aut_fixedNeighborFinset_card_le_fiftySeven
    (hΓ : IsMoore57 Γ) (σ : Equiv.Perm V) (v : V) :
    (autFixedNeighborFinset Γ σ v).card ≤ 57 := by
  have hle :
      (autFixedNeighborFinset Γ σ v).card ≤ (Γ.neighborFinset v).card :=
    Finset.card_le_card (aut_fixedNeighborFinset_subset_neighborFinset σ v)
  have hdeg : (Γ.neighborFinset v).card = 57 := by
    rw [SimpleGraph.card_neighborFinset_eq_degree, hΓ.regular.degree_eq v]
  exact hle.trans_eq hdeg

theorem aut_fixedNeighborFinset_card_eq_19_or_38_or_57
    (hΓ : IsMoore57 Γ) (σ : Equiv.Perm V)
    (smul_adj : ∀ v w : V, Γ.Adj v w ↔ Γ.Adj (σ v) (σ w))
    (pow_nineteen : σ ^ 19 = 1)
    (hcount : fixedVertexCount σ ≠ 1)
    {v : V} (hv : σ v = v) :
    (autFixedNeighborFinset Γ σ v).card = 19 ∨
      (autFixedNeighborFinset Γ σ v).card = 38 ∨
        (autFixedNeighborFinset Γ σ v).card = 57 := by
  let n := (autFixedNeighborFinset Γ σ v).card
  have hge : 19 ≤ n := by
    simpa [n] using
      aut_card_fixedNeighborFinset_ge_nineteen_of_fixedVertexCount_ne_one hΓ σ smul_adj
        pow_nineteen hv hcount
  have hle : n ≤ 57 := by
    simpa [n] using aut_fixedNeighborFinset_card_le_fiftySeven hΓ σ v
  have hmod : n ≡ 0 [MOD 19] := by
    simpa [n] using aut_card_fixedNeighborFinset_modEq_zero hΓ σ smul_adj pow_nineteen hv
  change n = 19 ∨ n = 38 ∨ n = 57
  have hdvd : 19 ∣ n := Nat.modEq_zero_iff_dvd.mp hmod
  rcases hdvd with ⟨m, hm⟩
  have hm_pos : 1 ≤ m := by omega
  have hm_le : m ≤ 3 := by omega
  rw [hm]
  interval_cases m <;> omega

/-! ### Lower bound `(fixedNeighbors).card + 1 ≤ fixedVertexCount` -/

theorem aut_fixedVertexCount_ge_fixedNeighborFinset_card_add_one
    (σ : Equiv.Perm V) {v : V} (hv : σ v = v) :
    (autFixedNeighborFinset Γ σ v).card + 1 ≤ fixedVertexCount σ := by
  classical
  let S := fixedVertexSet σ
  let N := autFixedNeighborFinset Γ σ v
  have hv_not_mem : v ∉ N := by
    intro hv_mem
    have hvv : Γ.Adj v v := (mem_autFixedNeighborFinset σ).mp hv_mem |>.1
    exact SimpleGraph.irrefl Γ hvv
  have hsubset : insert v N ⊆ S.toFinset := by
    intro x hx
    rw [Set.mem_toFinset]
    rw [Finset.mem_insert] at hx
    rcases hx with rfl | hxN
    · exact hv
    · exact (mem_autFixedNeighborFinset σ).mp hxN |>.2
  have hle : (insert v N).card ≤ S.toFinset.card := Finset.card_le_card hsubset
  have hcard_insert : (insert v N).card = N.card + 1 := by
    simp [hv_not_mem]
  rw [hcard_insert] at hle
  rw [fixedVertexCount_eq_card_fixedVertexSet, ← Set.toFinset_card]
  exact hle

theorem aut_fixedVertexCount_ge_twenty_of_one_lt
    (hΓ : IsMoore57 Γ) (σ : Equiv.Perm V)
    (smul_adj : ∀ v w : V, Γ.Adj v w ↔ Γ.Adj (σ v) (σ w))
    (pow_nineteen : σ ^ 19 = 1)
    (hcount : 1 < fixedVertexCount σ) :
    20 ≤ fixedVertexCount σ := by
  classical
  have hcard : 1 < Fintype.card (fixedVertexSet σ) := by
    simpa [fixedVertexCount_eq_card_fixedVertexSet] using hcount
  rcases Fintype.one_lt_card_iff.mp hcard with ⟨v, _w, _hvw⟩
  have hcount_ne : fixedVertexCount σ ≠ 1 := by omega
  have hneighbor :
      19 ≤ (autFixedNeighborFinset Γ σ (v : V)).card :=
    aut_card_fixedNeighborFinset_ge_nineteen_of_fixedVertexCount_ne_one hΓ σ smul_adj
      pow_nineteen v.property hcount_ne
  have hcount_lower :
      (autFixedNeighborFinset Γ σ (v : V)).card + 1 ≤ fixedVertexCount σ :=
    aut_fixedVertexCount_ge_fixedNeighborFinset_card_add_one σ v.property
  omega

/-! ### Moved-vertex side: a moved vertex has at most one σ-fixed neighbour -/

/-- Abstract version of `moved_vertex_fixedNeighbor_card_le_one`. -/
theorem aut_moved_vertex_fixedNeighbor_card_le_one
    (hΓ : IsMoore57 Γ) (σ : Equiv.Perm V)
    (smul_adj : ∀ v w : V, Γ.Adj v w ↔ Γ.Adj (σ v) (σ w))
    {y : V} (hy : y ∉ fixedVertexSet σ) :
    ((Γ.neighborFinset y).filter fun x => σ x = x).card ≤ 1 := by
  classical
  rw [Finset.card_le_one_iff]
  intro x z hx hz
  by_contra hxz
  have hyx : Γ.Adj y x := by
    exact (SimpleGraph.mem_neighborFinset (G := Γ) (v := y) (w := x)).1
      (Finset.mem_filter.mp hx).1
  have hyz : Γ.Adj y z := by
    exact (SimpleGraph.mem_neighborFinset (G := Γ) (v := y) (w := z)).1
      (Finset.mem_filter.mp hz).1
  have hxfix : σ x = x := (Finset.mem_filter.mp hx).2
  have hzfix : σ z = z := (Finset.mem_filter.mp hz).2
  by_cases hxz_adj : Γ.Adj x z
  · exact False.elim (hΓ.no_triangle hyx hxz_adj hyz.symm)
  · have hry_ne_y : σ y ≠ y := by
      intro hry
      exact hy hry
    have hy_ne_x : y ≠ x := Γ.ne_of_adj hyx
    have hy_ne_z : y ≠ z := Γ.ne_of_adj hyz
    have hx_ne_ry : x ≠ σ y := by
      intro hxry
      have hrot_eq : σ x = σ y := hxfix.trans hxry
      exact hy_ne_x (σ.injective hrot_eq).symm
    have hz_ne_ry : z ≠ σ y := by
      intro hzry
      have hrot_eq : σ z = σ y := hzfix.trans hzry
      exact hy_ne_z (σ.injective hrot_eq).symm
    have h_x_ry : Γ.Adj x (σ y) := by
      have hrotAdj : Γ.Adj (σ x) (σ y) := (smul_adj x y).mp hyx.symm
      simpa [hxfix] using hrotAdj
    have h_ry_z : Γ.Adj (σ y) z := by
      have hrotAdj : Γ.Adj (σ y) (σ z) := (smul_adj y z).mp hyz
      simpa [hzfix] using hrotAdj
    exact hΓ.no_four_cycle
      (x0 := y) (x1 := x) (x2 := σ y) (x3 := z)
      hy_ne_x (fun hEq => hry_ne_y hEq.symm) hy_ne_z hx_ne_ry hxz
      (fun hEq => hz_ne_ry hEq.symm)
      hyx h_x_ry h_ry_z hyz.symm

/-! ### Cross-edge bound: fixed × (57 − k) ≤ moved -/

theorem aut_fixed_moved_cross_edge_bound
    (hΓ : IsMoore57 Γ) (σ : Equiv.Perm V)
    (smul_adj : ∀ v w : V, Γ.Adj v w ↔ Γ.Adj (σ v) (σ w))
    (k : ℕ)
    (hreg : ∀ x : V, σ x = x →
      (autFixedNeighborFinset Γ σ x).card = k) :
    fixedVertexCount σ * (57 - k) ≤ Fintype.card V - fixedVertexCount σ := by
  classical
  let S : Finset V := (fixedVertexSet σ).toFinset
  let T : Finset V := Sᶜ
  have hS_mem (x : V) : x ∈ S ↔ σ x = x := by
    simp [S, fixedVertexSet]
  have hT_mem (x : V) : x ∈ T ↔ σ x ≠ x := by
    simp [T, S, fixedVertexSet]
  have h_above :
      ∀ x ∈ S, 57 - k ≤ (T.bipartiteAbove Γ.Adj x).card := by
    intro x hxS
    have hxfix : σ x = x := (hS_mem x).mp hxS
    have hfilter :
        T.bipartiteAbove Γ.Adj x =
          (Γ.neighborFinset x).filter fun y => σ y ≠ y := by
      ext y
      simp [Finset.mem_bipartiteAbove, hT_mem,
        SimpleGraph.mem_neighborFinset, and_comm]
    have hfixed :
        ((Γ.neighborFinset x).filter fun y => σ y = y).card = k := by
      simpa [autFixedNeighborFinset] using hreg x hxfix
    have hsum :
        ((Γ.neighborFinset x).filter fun y => σ y = y).card +
          ((Γ.neighborFinset x).filter fun y => σ y ≠ y).card =
            (Γ.neighborFinset x).card := by
      simpa using
        (Finset.card_filter_add_card_filter_not
          (s := Γ.neighborFinset x) (p := fun y => σ y = y))
    have hdeg : (Γ.neighborFinset x).card = 57 := by
      rw [SimpleGraph.card_neighborFinset_eq_degree, hΓ.regular.degree_eq x]
    have hmoved :
        ((Γ.neighborFinset x).filter fun y => σ y ≠ y).card = 57 - k := by
      omega
    rw [hfilter, hmoved]
  have h_below :
      ∀ y ∈ T, (S.bipartiteBelow Γ.Adj y).card ≤ 1 := by
    intro y hyT
    have hymove : y ∉ fixedVertexSet σ := by
      simpa [fixedVertexSet] using (hT_mem y).mp hyT
    have hfilter :
        S.bipartiteBelow Γ.Adj y =
          (Γ.neighborFinset y).filter fun x => σ x = x := by
      ext x
      simp [Finset.mem_bipartiteBelow, hS_mem,
        SimpleGraph.mem_neighborFinset, SimpleGraph.adj_comm, and_comm]
    rw [hfilter]
    exact aut_moved_vertex_fixedNeighbor_card_le_one hΓ σ smul_adj hymove
  have hdouble :
      S.card * (57 - k) ≤ T.card * 1 :=
    Finset.card_mul_le_card_mul Γ.Adj (s := S) (t := T)
      (m := 57 - k) (n := 1) h_above h_below
  have hScard : S.card = fixedVertexCount σ := by
    simp [S, fixedVertexCount, fixedVertexSet_toFinset_eq_filter]
  have hTcard : T.card = Fintype.card V - fixedVertexCount σ := by
    change Sᶜ.card = Fintype.card V - fixedVertexCount σ
    rw [Finset.card_compl, hScard]
  simpa [hScard, hTcard] using hdouble

/-! ### SRG / regular-candidate arithmetic -/

/-- Pure SRG arithmetic: from `IsSRGWith n k 0 1` with positive `n` and
`k ∈ {19, 38, 57}` we get `n = k² + 1`. Used to discharge the regularity
candidate case for both the abstract (raw automorphism) and `D₁₉` rotation
pipelines. -/
theorem srg_n_eq_k_sq_add_one_of_k_in_19_38_57
    {W : Type*} [Fintype W]
    {G : SimpleGraph W} [DecidableRel G.Adj]
    {n k : ℕ} (hsrg : G.IsSRGWith n k 0 1) (hpos : 0 < n)
    (hk : k = 19 ∨ k = 38 ∨ k = 57) :
    n = k * k + 1 := by
  have hparam := SimpleGraph.IsSRGWith.param_eq G hsrg hpos
  rcases hk with rfl | rfl | rfl <;> norm_num at hparam ⊢ <;> omega

/-- If `σ` has a regular fixed induced subgraph of degree `k ∈ {19, 38, 57}`,
then `fixedVertexCount σ = k² + 1`. -/
theorem aut_fixedVertexCount_eq_degree_sq_add_one_of_regular_candidate
    (hΓ : IsMoore57 Γ) (σ : Equiv.Perm V)
    (smul_adj : ∀ v w : V, Γ.Adj v w ↔ Γ.Adj (σ v) (σ w))
    (pow_nineteen : σ ^ 19 = 1)
    (k : ℕ)
    (hreg : ∀ x : fixedVertexSet σ,
      ((Γ.neighborFinset (x : V)).filter fun w => σ w = w).card = k)
    (hk : k = 19 ∨ k = 38 ∨ k = 57) :
    fixedVertexCount σ = k * k + 1 := by
  let Gfix := autFixedInducedGraph Γ σ
  have hsrg :
      Gfix.IsSRGWith (fixedVertexCount σ) k 0 1 := by
    refine autFixedInducedGraph_isSRGWith_of_regular hΓ σ smul_adj k ?_
    intro x
    rw [autFixedInducedGraph_degree_eq_fixedNeighborFinset_card σ x]
    exact hreg x
  have hpos : 0 < fixedVertexCount σ :=
    aut_fixedVertexCount_pos_of_pow_nineteen hΓ σ pow_nineteen
  exact srg_n_eq_k_sq_add_one_of_k_in_19_38_57 hsrg hpos hk

/-! ### Conditional reduction: regular ⇒ fixed count 1 -/

theorem aut_fixedVertexCount_eq_one_of_regular_if_not_one
    (hΓ : IsMoore57 Γ) (σ : Equiv.Perm V)
    (smul_adj : ∀ v w : V, Γ.Adj v w ↔ Γ.Adj (σ v) (σ w))
    (pow_nineteen : σ ^ 19 = 1)
    (ne_one : σ ≠ 1)
    (hregular :
      fixedVertexCount σ ≠ 1 →
        ∃ k : ℕ,
          (∀ x : fixedVertexSet σ,
            ((Γ.neighborFinset (x : V)).filter fun w => σ w = w).card = k) ∧
          (k = 19 ∨ k = 38 ∨ k = 57)) :
    fixedVertexCount σ = 1 := by
  by_contra hne
  rcases hregular hne with ⟨k, hreg, hk⟩
  have hcount : fixedVertexCount σ = k * k + 1 :=
    aut_fixedVertexCount_eq_degree_sq_add_one_of_regular_candidate hΓ σ smul_adj
      pow_nineteen k hreg hk
  have hcross :
      fixedVertexCount σ * (57 - k) ≤ Fintype.card V - fixedVertexCount σ := by
    refine aut_fixed_moved_cross_edge_bound hΓ σ smul_adj k ?_
    intro x hxfix
    have hreg' : ((Γ.neighborFinset x).filter fun w => σ w = w).card = k :=
      hreg ⟨x, hxfix⟩
    simpa [autFixedNeighborFinset] using hreg'
  have hcard : Fintype.card V = 3250 := hΓ.card
  rcases hk with rfl | rfl | rfl
  · omega
  · omega
  · have hlt : fixedVertexCount σ < Fintype.card V :=
      aut_fixedVertexCount_lt_card σ ne_one
    omega

/-! ### Regularity of fixed-neighbour cardinality -/

/-- For two non-adjacent fixed vertices `p, q`, deleting their common fixed
neighbour `z` gives an injection from σ-fixed neighbours of `p` to those of
`q`. -/
theorem aut_fixedNeighborFinset_erase_card_le_of_not_adj
    (hΓ : IsMoore57 Γ) (σ : Equiv.Perm V)
    (smul_adj : ∀ v w : V, Γ.Adj v w ↔ Γ.Adj (σ v) (σ w))
    {p q z : V}
    (_hp : σ p = p) (hq : σ q = q)
    (hpq : p ≠ q) (hpq_not_adj : ¬ Γ.Adj p q)
    (hpz : Γ.Adj p z) (hqz : Γ.Adj q z)
    (_hz : σ z = z) :
    ((autFixedNeighborFinset Γ σ p).erase z).card ≤
      ((autFixedNeighborFinset Γ σ q).erase z).card := by
  classical
  let A := ((autFixedNeighborFinset Γ σ p).erase z : Set V)
  let B := ((autFixedNeighborFinset Γ σ q).erase z : Set V)
  have hExists : ∀ a : A, ∃ b : V,
      b ∈ (autFixedNeighborFinset Γ σ q).erase z ∧ Γ.Adj (a : V) b := by
    intro a
    have haErase : (a : V) ∈ (autFixedNeighborFinset Γ σ p).erase z := by
      change (a : V) ∈ ((autFixedNeighborFinset Γ σ p).erase z : Set V)
      exact a.property
    have ha_ne_z : (a : V) ≠ z := (Finset.mem_erase.mp haErase).1
    have haN : (a : V) ∈ autFixedNeighborFinset Γ σ p :=
      (Finset.mem_erase.mp haErase).2
    have hpa : Γ.Adj p (a : V) := (mem_autFixedNeighborFinset σ).mp haN |>.1
    have haFixed : σ (a : V) = (a : V) :=
      (mem_autFixedNeighborFinset σ).mp haN |>.2
    have haq : (a : V) ≠ q := by
      intro haq
      exact hpq_not_adj (by simpa [haq] using hpa)
    have haq_not_adj : ¬ Γ.Adj (a : V) q := by
      intro haqAdj
      exact hΓ.no_four_cycle
        (x0 := p) (x1 := (a : V)) (x2 := q) (x3 := z)
        (Γ.ne_of_adj hpa) hpq (Γ.ne_of_adj hpz)
        (Γ.ne_of_adj haqAdj) ha_ne_z (Γ.ne_of_adj hqz)
        hpa haqAdj hqz hpz.symm
    rcases aut_exists_fixed_commonNeighbor_of_not_adj hΓ σ smul_adj
        haFixed hq haq haq_not_adj with ⟨b, hbFixed, hab, hqb⟩
    have hb_ne_z : b ≠ z := by
      intro hbz
      have hza : Γ.Adj z (a : V) := by simpa [hbz] using hab.symm
      exact hΓ.no_triangle hpz hza hpa.symm
    have hbN : b ∈ autFixedNeighborFinset Γ σ q :=
      (mem_autFixedNeighborFinset σ).2 ⟨hqb, hbFixed⟩
    exact ⟨b, Finset.mem_erase.mpr ⟨hb_ne_z, hbN⟩, hab⟩
  let f : A → B := fun a =>
    ⟨Classical.choose (hExists a), by
      change Classical.choose (hExists a) ∈
        ((autFixedNeighborFinset Γ σ q).erase z : Set V)
      exact (Classical.choose_spec (hExists a)).1⟩
  have hf_inj : Function.Injective f := by
    intro a₁ a₂ hfa
    apply Subtype.ext
    by_contra ha_ne
    have ha₁Erase : (a₁ : V) ∈ (autFixedNeighborFinset Γ σ p).erase z := by
      change (a₁ : V) ∈ ((autFixedNeighborFinset Γ σ p).erase z : Set V)
      exact a₁.property
    have ha₂Erase : (a₂ : V) ∈ (autFixedNeighborFinset Γ σ p).erase z := by
      change (a₂ : V) ∈ ((autFixedNeighborFinset Γ σ p).erase z : Set V)
      exact a₂.property
    have ha₁N : (a₁ : V) ∈ autFixedNeighborFinset Γ σ p :=
      (Finset.mem_erase.mp ha₁Erase).2
    have ha₂N : (a₂ : V) ∈ autFixedNeighborFinset Γ σ p :=
      (Finset.mem_erase.mp ha₂Erase).2
    have hpa₁ : Γ.Adj p (a₁ : V) := (mem_autFixedNeighborFinset σ).mp ha₁N |>.1
    have hpa₂ : Γ.Adj p (a₂ : V) := (mem_autFixedNeighborFinset σ).mp ha₂N |>.1
    have ha₁b : Γ.Adj (a₁ : V) (f a₁ : V) :=
      (Classical.choose_spec (hExists a₁)).2
    have ha₂b' : Γ.Adj (a₂ : V) (f a₂ : V) :=
      (Classical.choose_spec (hExists a₂)).2
    have hbEq : (f a₁ : V) = (f a₂ : V) := congrArg Subtype.val hfa
    have hba₂ : Γ.Adj (f a₁ : V) (a₂ : V) := by
      have : Γ.Adj (a₂ : V) (f a₁ : V) := by simpa [hbEq] using ha₂b'
      exact this.symm
    have hpb : p ≠ (f a₁ : V) := by
      intro hpb
      have hbErase : (f a₁ : V) ∈ (autFixedNeighborFinset Γ σ q).erase z := by
        change (f a₁ : V) ∈ ((autFixedNeighborFinset Γ σ q).erase z : Set V)
        exact (f a₁).property
      have hbN : (f a₁ : V) ∈ autFixedNeighborFinset Γ σ q :=
        (Finset.mem_erase.mp hbErase).2
      have hqb : Γ.Adj q (f a₁ : V) := (mem_autFixedNeighborFinset σ).mp hbN |>.1
      exact hpq_not_adj (by simpa [← hpb] using hqb.symm)
    exact hΓ.no_four_cycle
      (x0 := p) (x1 := (a₁ : V)) (x2 := (f a₁ : V)) (x3 := (a₂ : V))
      (Γ.ne_of_adj hpa₁) hpb (Γ.ne_of_adj hpa₂)
      (Γ.ne_of_adj ha₁b) ha_ne (Γ.ne_of_adj hba₂)
      hpa₁ ha₁b hba₂ hpa₂.symm
  have hcard : Fintype.card A ≤ Fintype.card B :=
    Fintype.card_le_of_injective f hf_inj
  have hAcard : Fintype.card A = ((autFixedNeighborFinset Γ σ p).erase z).card := by
    change Fintype.card {w : V // w ∈
      (((autFixedNeighborFinset Γ σ p).erase z : Finset V) : Set V)} =
        ((autFixedNeighborFinset Γ σ p).erase z).card
    exact Fintype.card_ofFinset ((autFixedNeighborFinset Γ σ p).erase z) (by intro w; rfl)
  have hBcard : Fintype.card B = ((autFixedNeighborFinset Γ σ q).erase z).card := by
    change Fintype.card {w : V // w ∈
      (((autFixedNeighborFinset Γ σ q).erase z : Finset V) : Set V)} =
        ((autFixedNeighborFinset Γ σ q).erase z).card
    exact Fintype.card_ofFinset ((autFixedNeighborFinset Γ σ q).erase z) (by intro w; rfl)
  omega

/-- Non-adjacent fixed vertices have equal σ-fixed-neighbour counts. -/
theorem aut_fixedNeighborFinset_card_eq_of_not_adj
    (hΓ : IsMoore57 Γ) (σ : Equiv.Perm V)
    (smul_adj : ∀ v w : V, Γ.Adj v w ↔ Γ.Adj (σ v) (σ w))
    {x y : V}
    (hx : σ x = x) (hy : σ y = y)
    (hxy : x ≠ y) (hxy_not_adj : ¬ Γ.Adj x y) :
    (autFixedNeighborFinset Γ σ x).card = (autFixedNeighborFinset Γ σ y).card := by
  classical
  rcases aut_exists_fixed_commonNeighbor_of_not_adj hΓ σ smul_adj
      hx hy hxy hxy_not_adj with ⟨z, hz, hxz, hyz⟩
  have hzNx : z ∈ autFixedNeighborFinset Γ σ x :=
    (mem_autFixedNeighborFinset σ).2 ⟨hxz, hz⟩
  have hzNy : z ∈ autFixedNeighborFinset Γ σ y :=
    (mem_autFixedNeighborFinset σ).2 ⟨hyz, hz⟩
  have hle :
      ((autFixedNeighborFinset Γ σ x).erase z).card ≤
        ((autFixedNeighborFinset Γ σ y).erase z).card :=
    aut_fixedNeighborFinset_erase_card_le_of_not_adj hΓ σ smul_adj
      hx hy hxy hxy_not_adj hxz hyz hz
  have hge :
      ((autFixedNeighborFinset Γ σ y).erase z).card ≤
        ((autFixedNeighborFinset Γ σ x).erase z).card :=
    aut_fixedNeighborFinset_erase_card_le_of_not_adj hΓ σ smul_adj
      hy hx hxy.symm (by intro hyx; exact hxy_not_adj hyx.symm) hyz hxz hz
  have hxErase :
      ((autFixedNeighborFinset Γ σ x).erase z).card + 1 =
        (autFixedNeighborFinset Γ σ x).card :=
    Finset.card_erase_add_one hzNx
  have hyErase :
      ((autFixedNeighborFinset Γ σ y).erase z).card + 1 =
        (autFixedNeighborFinset Γ σ y).card :=
    Finset.card_erase_add_one hzNy
  omega

theorem aut_exists_fixedNeighbor_ne_of_count_ne_one
    (hΓ : IsMoore57 Γ) (σ : Equiv.Perm V)
    (smul_adj : ∀ v w : V, Γ.Adj v w ↔ Γ.Adj (σ v) (σ w))
    (pow_nineteen : σ ^ 19 = 1)
    (hcount : fixedVertexCount σ ≠ 1)
    {x y : V} (hx : σ x = x) :
    ∃ z, z ∈ autFixedNeighborFinset Γ σ x ∧ z ≠ y := by
  classical
  have hge : 19 ≤ (autFixedNeighborFinset Γ σ x).card :=
    aut_card_fixedNeighborFinset_ge_nineteen_of_fixedVertexCount_ne_one hΓ σ smul_adj
      pow_nineteen hx hcount
  have hone : 1 < (autFixedNeighborFinset Γ σ x).card := by omega
  rcases Finset.one_lt_card_iff.mp hone with ⟨a, b, ha, hb, hab⟩
  by_cases hay : a = y
  · exact ⟨b, hb, by
      intro hby
      exact hab (hay.trans hby.symm)⟩
  · exact ⟨a, ha, hay⟩

theorem aut_fixedNeighborFinset_card_eq_of_count_ne_one
    (hΓ : IsMoore57 Γ) (σ : Equiv.Perm V)
    (smul_adj : ∀ v w : V, Γ.Adj v w ↔ Γ.Adj (σ v) (σ w))
    (pow_nineteen : σ ^ 19 = 1)
    (hcount : fixedVertexCount σ ≠ 1)
    {x y : V} (hx : σ x = x) (hy : σ y = y) :
    (autFixedNeighborFinset Γ σ x).card = (autFixedNeighborFinset Γ σ y).card := by
  classical
  by_cases hxy : x = y
  · subst y; rfl
  by_cases hxyAdj : Γ.Adj x y
  · rcases aut_exists_fixedNeighbor_ne_of_count_ne_one hΓ σ smul_adj pow_nineteen hcount hx
      (y := y) with ⟨a, haN, ha_ne_y⟩
    rcases aut_exists_fixedNeighbor_ne_of_count_ne_one hΓ σ smul_adj pow_nineteen hcount hy
      (y := x) with ⟨b, hbN, hb_ne_x⟩
    have hxa : Γ.Adj x a := (mem_autFixedNeighborFinset σ).mp haN |>.1
    have haFixed : σ a = a := (mem_autFixedNeighborFinset σ).mp haN |>.2
    have hyb : Γ.Adj y b := (mem_autFixedNeighborFinset σ).mp hbN |>.1
    have hbFixed : σ b = b := (mem_autFixedNeighborFinset σ).mp hbN |>.2
    have hay_not_adj : ¬ Γ.Adj a y := by
      intro hay
      exact hΓ.no_triangle hxyAdj hay.symm hxa.symm
    have hxb_not_adj : ¬ Γ.Adj x b := by
      intro hxb
      exact hΓ.no_triangle hxyAdj hyb hxb.symm
    have hab_not_adj : ¬ Γ.Adj a b := by
      intro hab
      exact hΓ.no_four_cycle
        (x0 := x) (x1 := a) (x2 := b) (x3 := y)
        (Γ.ne_of_adj hxa) (by intro hxbEq; exact hb_ne_x hxbEq.symm)
        hxy
        (Γ.ne_of_adj hab) (by intro hayEq; exact ha_ne_y hayEq)
        (Γ.ne_of_adj hyb).symm
        hxa hab hyb.symm hxyAdj.symm
    have hya :
        (autFixedNeighborFinset Γ σ y).card = (autFixedNeighborFinset Γ σ a).card := by
      exact aut_fixedNeighborFinset_card_eq_of_not_adj hΓ σ smul_adj
        hy haFixed (by intro hyaEq; exact ha_ne_y hyaEq.symm)
        (by intro hyaAdj; exact hay_not_adj hyaAdj.symm)
    have habEq :
        (autFixedNeighborFinset Γ σ a).card = (autFixedNeighborFinset Γ σ b).card :=
      aut_fixedNeighborFinset_card_eq_of_not_adj hΓ σ smul_adj
        haFixed hbFixed (by
          intro habEq
          exact hΓ.no_triangle hxyAdj (by simpa [← habEq] using hyb) hxa.symm)
        hab_not_adj
    have hxb :
        (autFixedNeighborFinset Γ σ x).card = (autFixedNeighborFinset Γ σ b).card :=
      aut_fixedNeighborFinset_card_eq_of_not_adj hΓ σ smul_adj
        hx hbFixed (by intro hxbEq; exact hb_ne_x hxbEq.symm) hxb_not_adj
    exact hxb.trans (habEq.symm.trans hya.symm)
  · exact aut_fixedNeighborFinset_card_eq_of_not_adj hΓ σ smul_adj hx hy hxy hxyAdj

/-! ### Main theorem -/

/-- **Main abstract theorem.** Any order-19 automorphism of a Moore57 graph
fixes exactly one vertex. -/
theorem order19_aut_fixedVertexCount_eq_one
    (hΓ : IsMoore57 Γ) (σ : Equiv.Perm V)
    (smul_adj : ∀ v w : V, Γ.Adj v w ↔ Γ.Adj (σ v) (σ w))
    (pow_nineteen : σ ^ 19 = 1)
    (ne_one : σ ≠ 1) :
    fixedVertexCount σ = 1 := by
  refine aut_fixedVertexCount_eq_one_of_regular_if_not_one hΓ σ smul_adj
    pow_nineteen ne_one ?_
  intro hcount
  have hpos : 0 < Fintype.card (fixedVertexSet σ) := by
    simpa [fixedVertexCount_eq_card_fixedVertexSet] using
      aut_fixedVertexCount_pos_of_pow_nineteen hΓ σ pow_nineteen
  rcases Fintype.card_pos_iff.mp hpos with ⟨x⟩
  let k := (autFixedNeighborFinset Γ σ (x : V)).card
  refine ⟨k, ?_, ?_⟩
  · intro y
    have : (autFixedNeighborFinset Γ σ (y : V)).card =
        (autFixedNeighborFinset Γ σ (x : V)).card :=
      aut_fixedNeighborFinset_card_eq_of_count_ne_one hΓ σ smul_adj pow_nineteen
        hcount y.property x.property
    simpa [autFixedNeighborFinset, k] using this
  · have :
        (autFixedNeighborFinset Γ σ (x : V)).card = 19 ∨
          (autFixedNeighborFinset Γ σ (x : V)).card = 38 ∨
            (autFixedNeighborFinset Γ σ (x : V)).card = 57 :=
      aut_fixedNeighborFinset_card_eq_19_or_38_or_57 hΓ σ smul_adj pow_nineteen
        hcount x.property
    exact this

end Moore57
