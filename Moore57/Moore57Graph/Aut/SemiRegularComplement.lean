import Moore57.Moore57Graph.Aut.NeighborMod
import Moore57.Foundations.GroupAction.SemiRegularOrbit
import Moore57.Foundations.GroupAction.SemiRegularPrimeOrder
import Moore57.Foundations.GroupAction.SemiRegularFixed

set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false
set_option linter.unusedSectionVars false

/-!
# Semi-regular complement bridge

For a graph automorphism `σ : Equiv.Perm V` fixing a vertex `a`, the
σ-moved neighbour set

```
N(a) \ Fix(σ) = (Γ.neighborFinset a).filter (fun w ↦ σ w ≠ w)
```

is σ-invariant.  Combined with the semi-regular hypothesis from
`Foundations.GroupAction.SemiRegularOrbit`, this gives

```
orderOf σ ∣ |N(a) \ Fix(σ)|.
```

This is the Tier C / §6 Lem 17 / Lem 18 semi-regular orbit bridge.

## Main results

* `Moore57.autMovedNeighborFinset` — the σ-moved neighbours of `a`
  (i.e. `N(a) \ Fix(σ)`) as a Finset.
* `Moore57.autMovedNeighborFinset_σ_invariant` — σ-invariance.
* `Moore57.orderOf_dvd_card_movedNeighbour_of_semiRegular` — the bridge:
  given the semi-regular hypothesis on `N(a) \ Fix(σ)`, the order of σ
  divides `|N(a) \ Fix(σ)|`.

The semi-regular hypothesis itself is left as a separate `Prop`-level
input, matching the MS 2010 §6 organisation (semi-regularity is
established "separately" from the complement-count step).
-/

namespace Moore57

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- The σ-moved neighbours of `v` — that is, neighbours `w` with `σ w ≠ w`.
This is `N(v) \ Fix(σ)` written as a Finset. -/
def autMovedNeighborFinset
    (Γ : SimpleGraph V) [DecidableRel Γ.Adj]
    (σ : V → V) (v : V) : Finset V :=
  (Γ.neighborFinset v).filter fun w => σ w ≠ w

@[simp] theorem mem_autMovedNeighborFinset
    (σ : V → V) {v w : V} :
    w ∈ autMovedNeighborFinset Γ σ v ↔ Γ.Adj v w ∧ σ w ≠ w := by
  simp [autMovedNeighborFinset, SimpleGraph.mem_neighborFinset]

/-- **σ-invariance of the moved-neighbour set.** If `σ` is a graph
automorphism (`Γ.Adj v w ↔ Γ.Adj (σ v) (σ w)`) fixing `a`, then σ maps
`N(a) \ Fix(σ)` into itself. -/
theorem autMovedNeighborFinset_σ_invariant
    (σ : Equiv.Perm V)
    (smul_adj : ∀ v w : V, Γ.Adj v w ↔ Γ.Adj (σ v) (σ w))
    {a : V} (ha : σ a = a) :
    ∀ w ∈ autMovedNeighborFinset Γ σ a, σ w ∈ autMovedNeighborFinset Γ σ a := by
  intro w hw
  rw [mem_autMovedNeighborFinset] at hw
  obtain ⟨hadj, hnotfix⟩ := hw
  rw [mem_autMovedNeighborFinset]
  refine ⟨?_, ?_⟩
  · -- σ a = a, and σ sends edges to edges: a — w ⟹ σ a — σ w ⟹ a — σ w
    have h1 : Γ.Adj (σ a) (σ w) := (smul_adj a w).mp hadj
    rwa [ha] at h1
  · -- σ (σ w) = σ w ⟹ σ w = w (σ injective), contradicting `σ w ≠ w`
    intro h
    exact hnotfix (σ.injective h)

/-- **Bridge from semi-regular hypothesis to `orderOf σ ∣ |N(a) \ Fix(σ)|`.**

If `σ` is a graph automorphism of `Γ` fixing `a`, and the cyclic action of
`⟨σ⟩` on the σ-moved neighbour set `N(a) \ Fix(σ)` is semi-regular (every
non-trivial power moves every element), then `orderOf σ` divides
`|N(a) \ Fix(σ)|`.

The semi-regular hypothesis is phrased elementarily:
`∀ w ∈ N(a) \ Fix(σ), ∀ k, σ^k w = w → orderOf σ ∣ k`. -/
theorem orderOf_dvd_card_movedNeighbour_of_semiRegular
    (σ : Equiv.Perm V)
    (smul_adj : ∀ v w : V, Γ.Adj v w ↔ Γ.Adj (σ v) (σ w))
    {a : V} (ha : σ a = a)
    (hsemi : ∀ w ∈ autMovedNeighborFinset Γ σ a,
             ∀ k : ℕ, (σ^k) w = w → orderOf σ ∣ k) :
    orderOf σ ∣ (autMovedNeighborFinset Γ σ a).card :=
  orderOf_dvd_card_of_semiRegular σ (autMovedNeighborFinset Γ σ a)
    (autMovedNeighborFinset_σ_invariant σ smul_adj ha) hsemi

/-- **Prime-order semi-regular bridge on `autMovedNeighborFinset`.**

For `σ : Equiv.Perm V` of prime order `p` (`σ^p = 1`, `p` prime), the
cyclic action of `⟨σ⟩` is automatically semi-regular on every moved
neighbour `w ∈ autMovedNeighborFinset Γ σ a`.  No FixedData /
structural hypothesis is required — the property follows from prime
order alone, by `semiRegular_at_movedPoint_of_prime_orderOf`.

This **generates** the `hsemi` argument required by
`orderOf_dvd_card_movedNeighbour_of_semiRegular` for the prime case,
removing the need to supply it as a separate hypothesis in
Lem 17 / 18 prime-case wrappers. -/
theorem aut_semiRegular_at_movedNeighbor_of_prime
    (σ : Equiv.Perm V) (p : ℕ) (hp : Nat.Prime p) (hpp : σ ^ p = 1)
    (a : V) :
    ∀ w ∈ autMovedNeighborFinset Γ σ a,
    ∀ k : ℕ, (σ ^ k) w = w → orderOf σ ∣ k := by
  intro w hw
  rw [mem_autMovedNeighborFinset] at hw
  exact semiRegular_at_movedPoint_of_prime_orderOf σ p hp hpp w hw.2

/-- **Combined prime-order bridge**: `σ^p = 1` (p prime) + fixed vertex
`a` ⟹ `orderOf σ ∣ |N(a) \ Fix(σ)|`.

Combines `aut_semiRegular_at_movedNeighbor_of_prime` with
`orderOf_dvd_card_movedNeighbour_of_semiRegular`.  This is the
fully-automatic prime-case bridge: no semi-regular hypothesis required. -/
theorem orderOf_dvd_card_movedNeighbour_of_prime
    (σ : Equiv.Perm V) (p : ℕ) (hp : Nat.Prime p) (hpp : σ ^ p = 1)
    (smul_adj : ∀ v w : V, Γ.Adj v w ↔ Γ.Adj (σ v) (σ w))
    {a : V} (ha : σ a = a) :
    orderOf σ ∣ (autMovedNeighborFinset Γ σ a).card :=
  orderOf_dvd_card_movedNeighbour_of_semiRegular σ smul_adj ha
    (aut_semiRegular_at_movedNeighbor_of_prime σ p hp hpp a)

/-! ## Graph-automorphism wrappers for `SemiRegularFixed`

The next section packages the five `Foundations.GroupAction.SemiRegularFixed`
lemmas (`Fix(σ^l) = Fix(σ)`, `|V| = a₀(σ) + k · orderOf σ`, etc.) as
**one-step graph-automorphism specializations**.  Downstream
MS 2010 §6 Lem 14 / Lem 17 / Lem 18 wrappers can call these directly
without re-unwrapping the semi-regular hypothesis on `V \ Fix(σ)`.

The new graph-specific result is
`aut_card_degree_eq_fixedNeighbourCount_add_orderOf_mul`: for a σ-fixed
vertex `a`,

```
Γ.degree a = (autFixedNeighborFinset Γ σ a).card + k' · orderOf σ.
```

This is the **modular constraint** MS 2010 §6 Lem 14/17/18 use to
restrict possible fixed-neighbour counts at high-order automorphisms.
The proof partitions `N(a)` into fixed/moved neighbours and applies
`orderOf_dvd_card_movedNeighbour_of_semiRegular` to the moved part. -/
section SemiRegularFixedGraphAut

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- **Graph-aut wrapper for `fixedVertexSet_pow_eq_of_semiRegular_complement`.**

For a graph automorphism σ that is semi-regular on `V \ Fix(σ)` and
`0 < l < orderOf σ`, the fixed-point set of `σ^l` agrees with `Fix(σ)`.

This is MS 2010 §6 Lem 21 in paper form: under semi-regularity on the
complement, *all* non-trivial powers below `orderOf σ` fix exactly the
same vertices as σ.

The `smul_adj` argument is **not** used for the conclusion (the foundations
lemma is purely group-theoretic); it is listed so that this wrapper has
the same argument shape as the rest of the graph-aut API and downstream
callers can pass it uniformly. -/
theorem aut_fixedVertexSet_pow_eq_of_semiRegular_complement
    (σ : Equiv.Perm V)
    (_smul_adj : ∀ v w : V, Γ.Adj v w ↔ Γ.Adj (σ v) (σ w))
    (hsemi : ∀ v : V, σ v ≠ v → ∀ k : ℕ, (σ^k) v = v → orderOf σ ∣ k)
    {l : ℕ} (hl_pos : 0 < l) (hl_lt : l < orderOf σ) :
    fixedVertexSet (σ ^ l) = fixedVertexSet σ :=
  fixedVertexSet_pow_eq_of_semiRegular_complement σ hsemi hl_pos hl_lt

/-- **Graph-aut wrapper for
`fixedVertexCount_pow_eq_of_semiRegular_complement`.**

For a graph automorphism σ that is semi-regular on `V \ Fix(σ)` and
`0 < l < orderOf σ`, the fixed-point count of `σ^l` equals that of σ. -/
theorem aut_fixedVertexCount_pow_eq_of_semiRegular_complement
    (σ : Equiv.Perm V)
    (_smul_adj : ∀ v w : V, Γ.Adj v w ↔ Γ.Adj (σ v) (σ w))
    (hsemi : ∀ v : V, σ v ≠ v → ∀ k : ℕ, (σ^k) v = v → orderOf σ ∣ k)
    {l : ℕ} (hl_pos : 0 < l) (hl_lt : l < orderOf σ) :
    fixedVertexCount (σ ^ l) = fixedVertexCount σ :=
  fixedVertexCount_pow_eq_of_semiRegular_complement σ hsemi hl_pos hl_lt

/-- **Graph-aut wrapper for
`card_eq_fixedVertexCount_add_orderOf_mul_of_semiRegular_complement`.**

For a graph automorphism σ semi-regular on `V \ Fix(σ)`,

```
Fintype.card V = fixedVertexCount σ + k · orderOf σ
```

for some `k : ℕ`. -/
theorem aut_card_V_eq_fixedVertexCount_add_orderOf_mul
    (σ : Equiv.Perm V)
    (_smul_adj : ∀ v w : V, Γ.Adj v w ↔ Γ.Adj (σ v) (σ w))
    (hsemi : ∀ v : V, σ v ≠ v → ∀ k : ℕ, (σ^k) v = v → orderOf σ ∣ k) :
    ∃ k : ℕ, Fintype.card V = fixedVertexCount σ + k * orderOf σ :=
  card_eq_fixedVertexCount_add_orderOf_mul_of_semiRegular_complement σ hsemi

/-- **Neighbour-set partition.** Every neighbour of `v` is either fixed by σ
or moved.  Card form:

```
Γ.degree v = (autFixedNeighborFinset Γ σ v).card + (autMovedNeighborFinset Γ σ v).card.
```
-/
theorem aut_degree_eq_fixedNeighbourCard_add_movedNeighbourCard
    (σ : Equiv.Perm V) (v : V) :
    Γ.degree v =
      (autFixedNeighborFinset Γ σ v).card +
        (autMovedNeighborFinset Γ σ v).card := by
  classical
  -- `autFixedNeighborFinset` is filter `σ w = w` on `neighborFinset v`;
  -- `autMovedNeighborFinset` is the complement filter `σ w ≠ w`.
  have hsplit :
      (autFixedNeighborFinset Γ σ v).card +
          (autMovedNeighborFinset Γ σ v).card =
        (Γ.neighborFinset v).card := by
    unfold autFixedNeighborFinset autMovedNeighborFinset
    have hpartition :
        ((Γ.neighborFinset v).filter (fun w => σ w = w)).card +
            ((Γ.neighborFinset v).filter (fun w => ¬ (σ w = w))).card =
          (Γ.neighborFinset v).card :=
      Finset.card_filter_add_card_filter_not (s := Γ.neighborFinset v)
        (p := fun w => σ w = w)
    convert hpartition using 2
  rw [← SimpleGraph.card_neighborFinset_eq_degree, ← hsplit]

/-- **Main graph-specific result.** For a graph automorphism σ fixing
vertex `a` (so σ stabilises `N(a)`), if σ acts semi-regularly on
`N(a) \ Fix(σ)`, then

```
Γ.degree a = (autFixedNeighborFinset Γ σ a).card + k' · orderOf σ
```

for some `k' : ℕ`.

This is the **modular fixed-neighbour constraint** used by MS 2010 §6
Lem 14, Lem 17, and Lem 18 to pin down the number of σ-fixed neighbours
of a σ-fixed vertex at high-order automorphisms.

Proof: partition `N(a)` into fixed/moved neighbours, apply
`orderOf_dvd_card_movedNeighbour_of_semiRegular` to the moved part. -/
theorem aut_card_degree_eq_fixedNeighbourCount_add_orderOf_mul
    (σ : Equiv.Perm V)
    (smul_adj : ∀ v w : V, Γ.Adj v w ↔ Γ.Adj (σ v) (σ w))
    {a : V} (ha : σ a = a)
    (hsemi : ∀ w ∈ autMovedNeighborFinset Γ σ a,
             ∀ k : ℕ, (σ^k) w = w → orderOf σ ∣ k) :
    ∃ k' : ℕ,
      Γ.degree a = (autFixedNeighborFinset Γ σ a).card + k' * orderOf σ := by
  -- moved-neighbour cardinality is a multiple of `orderOf σ`.
  have hdvd : orderOf σ ∣ (autMovedNeighborFinset Γ σ a).card :=
    orderOf_dvd_card_movedNeighbour_of_semiRegular σ smul_adj ha hsemi
  obtain ⟨k', hk'⟩ := hdvd
  refine ⟨k', ?_⟩
  -- combine with the partition `degree = fixed + moved`.
  have hpart := aut_degree_eq_fixedNeighbourCard_add_movedNeighbourCard
                  (Γ := Γ) σ a
  rw [hpart, hk', mul_comm]

/-- **Prime-order automatic version of
`aut_card_degree_eq_fixedNeighbourCount_add_orderOf_mul`.**

For a graph automorphism σ with `σ^p = 1` (`p` prime) fixing vertex `a`,
the semi-regular hypothesis on `N(a) \ Fix(σ)` follows automatically
(`aut_semiRegular_at_movedNeighbor_of_prime`), so

```
Γ.degree a = (autFixedNeighborFinset Γ σ a).card + k' · p
```

(with `orderOf σ = p` when σ is non-trivial, but stated as
`orderOf σ` for generality).

This is the **fully-automatic prime-case modular constraint** — no
auxiliary `hsemi` argument needed. -/
theorem aut_card_degree_eq_fixedNeighbourCount_add_orderOf_mul_of_prime
    (σ : Equiv.Perm V) (p : ℕ) (hp : Nat.Prime p) (hpp : σ ^ p = 1)
    (smul_adj : ∀ v w : V, Γ.Adj v w ↔ Γ.Adj (σ v) (σ w))
    {a : V} (ha : σ a = a) :
    ∃ k' : ℕ,
      Γ.degree a = (autFixedNeighborFinset Γ σ a).card + k' * orderOf σ :=
  aut_card_degree_eq_fixedNeighbourCount_add_orderOf_mul σ smul_adj ha
    (aut_semiRegular_at_movedNeighbor_of_prime σ p hp hpp a)

/-- **Combined dvd form.** Under the same hypotheses as
`aut_card_degree_eq_fixedNeighbourCount_add_orderOf_mul`,

```
orderOf σ ∣ (Γ.degree a - (autFixedNeighborFinset Γ σ a).card)
```

(natural-subtraction form; equivalent to the additive decomposition
above).

This packaging matches the form MS 2010 §6 Lem 17/18 use directly:
"σ moves a multiple of `orderOf σ` neighbours of `a`". -/
theorem aut_orderOf_dvd_degree_sub_fixedNeighbourCount
    (σ : Equiv.Perm V)
    (smul_adj : ∀ v w : V, Γ.Adj v w ↔ Γ.Adj (σ v) (σ w))
    {a : V} (ha : σ a = a)
    (hsemi : ∀ w ∈ autMovedNeighborFinset Γ σ a,
             ∀ k : ℕ, (σ^k) w = w → orderOf σ ∣ k) :
    orderOf σ ∣ (Γ.degree a - (autFixedNeighborFinset Γ σ a).card) := by
  -- Use the moved-neighbour bridge directly; via the partition
  -- `degree = fixed + moved`, natural-subtraction gives moved-card.
  have hdvd : orderOf σ ∣ (autMovedNeighborFinset Γ σ a).card :=
    orderOf_dvd_card_movedNeighbour_of_semiRegular σ smul_adj ha hsemi
  have hpart := aut_degree_eq_fixedNeighbourCard_add_movedNeighbourCard
                  (Γ := Γ) σ a
  -- From `degree = fixed + moved`, get `degree - fixed = moved`.
  have hsub :
      Γ.degree a - (autFixedNeighborFinset Γ σ a).card =
        (autMovedNeighborFinset Γ σ a).card := by
    omega
  rw [hsub]; exact hdvd

end SemiRegularFixedGraphAut

end Moore57
