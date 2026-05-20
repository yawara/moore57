import Moore57.Moore57Graph.Aut.NeighborMod
import Moore57.Foundations.GroupAction.SemiRegularOrbit

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

end Moore57
