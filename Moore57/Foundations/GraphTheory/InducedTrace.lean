import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Algebra.BigOperators.GroupWithZero.Action
import Mathlib.Algebra.Field.Basic
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Tactic.FieldSimp
import Moore57.Foundations.GraphTheory.AdjacentMovedCount

/-!
# Induced trace `Tr(S)` and group trace `Tr(X)`

For the Mačaj–Širáň 2010 §3 framework on Moore57.

* `inducedDegreeSum Γ S` : the sum of induced-subgraph degrees over `S`,
  equivalently `2 · |E(Γ[S])|`.
* `inducedTrace Γ S` : `Tr(S) := (∑_{v ∈ S} deg_{Γ[S]}(v)) / |S|` as a
  rational.  By double-counting, this equals the average degree in the
  induced subgraph on `S`.
* `groupTrace Γ X` : `Tr(X) := (∑_{x ∈ X} a₁(x)) / |X|`, the average of
  `adjacentMovedCount` over a finite set of permutations.

These appear throughout Mačaj–Širáň §3 (Lemmas 6, 8, 9, 10, Cor 1).

This file deliberately stays pure-graph-theoretic; no Moore57 SRG
hypothesis is needed.
-/

namespace Moore57

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- The sum of induced-subgraph degrees over `S`, equivalently
`2 · |E(Γ[S])|`. -/
def inducedDegreeSum (Γ : SimpleGraph V) [DecidableRel Γ.Adj] (S : Finset V) :
    ℕ :=
  ∑ v ∈ S, (S.filter (fun w => Γ.Adj v w)).card

/-- The number of edges in the induced subgraph `Γ[S]` (as a pair set). -/
def inducedEdgeCount (Γ : SimpleGraph V) [DecidableRel Γ.Adj] (S : Finset V) :
    ℕ :=
  ((S ×ˢ S).filter (fun p : V × V => Γ.Adj p.1 p.2)).card

/-- `inducedDegreeSum` equals `inducedEdgeCount` (as ordered-pair counting:
each edge `{v, w}` of `Γ[S]` contributes twice, once for each ordering). -/
theorem inducedDegreeSum_eq_inducedEdgeCount (S : Finset V) :
    inducedDegreeSum Γ S = inducedEdgeCount Γ S := by
  classical
  unfold inducedDegreeSum inducedEdgeCount
  rw [Finset.card_filter]
  rw [Finset.sum_product]
  refine Finset.sum_congr rfl (fun v _ => ?_)
  rw [Finset.card_filter]

/-- **`Tr(S)`**: the induced-subgraph trace = `(∑ deg) / |S|`, as a rational. -/
noncomputable def inducedTrace (Γ : SimpleGraph V) [DecidableRel Γ.Adj]
    (S : Finset V) : ℚ :=
  (inducedDegreeSum Γ S : ℚ) / S.card

/-- **`Tr(X)`**: the group trace = `(∑_{x ∈ X} a₁(x)) / |X|`, as a rational. -/
noncomputable def groupTrace (Γ : SimpleGraph V) [DecidableRel Γ.Adj]
    (X : Finset (Equiv.Perm V)) : ℚ :=
  (∑ x ∈ X, (adjacentMovedCount Γ x : ℚ)) / X.card

/-- **Double-counting identity for `groupTrace`**:
`|X| · Tr(X) = Σ_{x ∈ X} a₁(x) = |{(x, v) : v ~ x · v}|`. -/
theorem groupTrace_card_mul_eq_sum_a1
    (X : Finset (Equiv.Perm V)) (hX : X.Nonempty) :
    (X.card : ℚ) * groupTrace Γ X =
      ∑ x ∈ X, (adjacentMovedCount Γ x : ℚ) := by
  unfold groupTrace
  have hpos : (X.card : ℚ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Finset.card_ne_zero.mpr hX)
  rw [mul_div_cancel₀ _ hpos]

/-- **Pair-counting form of `Σ a₁(x)`**: the natural-number identity
`|{(x, v) ∈ X × V : v ~ x · v}| = Σ_{x ∈ X} a₁(x)`. -/
theorem sum_adjacentMovedCount_eq_card_pair
    (X : Finset (Equiv.Perm V)) :
    (((X ×ˢ (Finset.univ : Finset V)).filter
        (fun p => Γ.Adj p.2 (p.1 p.2))).card : ℕ) =
      ∑ x ∈ X, adjacentMovedCount Γ x := by
  classical
  rw [Finset.card_filter, Finset.sum_product]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  unfold adjacentMovedCount
  rw [Finset.card_filter]

/-- **Symmetry of `a₁` under inversion**: `a₁(σ⁻¹) = a₁(σ)`.

Bijection `v ↦ σ⁻¹ v` from the `σ⁻¹`-set
`{v : Γ.Adj v (σ⁻¹ v)}` onto the `σ`-set `{v : Γ.Adj v (σ v)}`:
if `Γ.Adj v (σ⁻¹ v)`, then via `adj_comm` and
`σ (σ⁻¹ v) = v` this becomes `Γ.Adj (σ⁻¹ v) (σ (σ⁻¹ v))`. -/
theorem adjacentMovedCount_inv (σ : Equiv.Perm V) :
    adjacentMovedCount Γ σ⁻¹ = adjacentMovedCount Γ σ := by
  classical
  unfold adjacentMovedCount
  -- Inverse-application identities.
  have h_inv_apply : ∀ v : V, σ (σ⁻¹ v) = v := by
    intro v; change (σ * σ⁻¹) v = v; rw [mul_inv_cancel]; rfl
  have h_apply_inv : ∀ v : V, σ⁻¹ (σ v) = v := by
    intro v; change (σ⁻¹ * σ) v = v; rw [inv_mul_cancel]; rfl
  -- Bijection `v ↦ σ⁻¹ v` from σ⁻¹-set to σ-set.
  apply Finset.card_bij (fun (v : V) (_ : v ∈ _) => σ⁻¹ v)
  · -- Image lies in target.
    intro v hv
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
    -- hv : Γ.Adj v (σ⁻¹ v); goal: Γ.Adj (σ⁻¹ v) (σ (σ⁻¹ v))
    rw [h_inv_apply]
    exact (SimpleGraph.adj_comm Γ v (σ⁻¹ v)).mp hv
  · -- Injective.
    intro v _ w _ hvw
    exact σ⁻¹.injective hvw
  · -- Surjective.
    intro w hw
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw
    -- hw : Γ.Adj w (σ w); want v with σ⁻¹ v = w, i.e. v = σ w.
    refine ⟨σ w, ?_, h_apply_inv w⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    -- Goal: Γ.Adj (σ w) (σ⁻¹ (σ w))
    rw [h_apply_inv]
    exact (SimpleGraph.adj_comm Γ w (σ w)).mp hw

/-- **Pairing parity**: for a subgroup `X ≤ Equiv.Perm V` of odd order,
`∑_{x ∈ X} a₁(x)` is even.

Proof: pair `x ∈ X` with `x⁻¹`.  Each pair contributes `a₁(x) + a₁(x⁻¹)
= 2 · a₁(x)` (using `adjacentMovedCount_inv`), which is ≡ 0 mod 2.
Self-paired elements (with `x = x⁻¹`, i.e., `x² = 1`) force `orderOf x ∣ 2`;
since `orderOf x ∣ |X|` and `|X|` is odd, `orderOf x` is odd, hence
`orderOf x = 1` and `x = 1`; finally `a₁(1) = 0`. -/
theorem sum_adjacentMovedCount_even_of_subgroup_odd_card
    (X : Subgroup (Equiv.Perm V)) [Fintype X]
    (hX_odd : Odd (Fintype.card X)) :
    Even (∑ x : X, adjacentMovedCount Γ (x : Equiv.Perm V)) := by
  classical
  -- Reduce evenness to vanishing in ZMod 2.
  rw [← ZMod.natCast_eq_zero_iff_even]
  push_cast
  -- Pairing involution: x ↦ x⁻¹.
  apply Finset.sum_involution (s := (Finset.univ : Finset X))
    (g := fun (x : X) (_ : x ∈ Finset.univ) => x⁻¹)
  · -- f x + f x⁻¹ = 0 in ZMod 2.
    intro x _
    have hsymm : adjacentMovedCount Γ ((x⁻¹ : X) : Equiv.Perm V) =
        adjacentMovedCount Γ ((x : Equiv.Perm V)) := by
      have hcoe : ((x⁻¹ : X) : Equiv.Perm V) = ((x : Equiv.Perm V))⁻¹ := rfl
      rw [hcoe, adjacentMovedCount_inv]
    rw [hsymm]
    have h2 : ((2 : ℕ) : ZMod 2) = 0 := by decide
    have : ((adjacentMovedCount Γ (x : Equiv.Perm V) : ℕ) : ZMod 2) +
        ((adjacentMovedCount Γ (x : Equiv.Perm V) : ℕ) : ZMod 2) =
      ((2 * adjacentMovedCount Γ (x : Equiv.Perm V) : ℕ) : ZMod 2) := by
      push_cast; ring
    rw [this, Nat.cast_mul, h2, zero_mul]
  · -- f x ≠ 0 → x⁻¹ ≠ x.  Contrapositive.
    intro x _ hf_ne hx_inv_eq_self
    apply hf_ne
    -- x = x⁻¹ ⇒ x² = 1.
    have hx_sq : x * x = 1 := by
      have h1 : x⁻¹ * x = 1 := inv_mul_cancel x
      rw [hx_inv_eq_self] at h1
      exact h1
    have h_ord_dvd_two : orderOf x ∣ 2 := by
      rw [orderOf_dvd_iff_pow_eq_one, pow_two]
      exact hx_sq
    have h_ord_dvd_card : orderOf x ∣ Fintype.card X := orderOf_dvd_card
    have h_ord_odd : Odd (orderOf x) := Odd.of_dvd_nat hX_odd h_ord_dvd_card
    -- orderOf x ∈ {1, 2}; odd ⇒ orderOf x ≠ 2 ⇒ orderOf x = 1.
    have h_ord_eq_one : orderOf x = 1 := by
      rcases (Nat.dvd_prime Nat.prime_two).mp h_ord_dvd_two with h1 | h2
      · exact h1
      · exfalso
        rw [h2] at h_ord_odd
        exact (Nat.not_odd_iff_even.mpr ⟨1, rfl⟩) h_ord_odd
    have hx_eq_one : x = 1 := orderOf_eq_one_iff.mp h_ord_eq_one
    have h_x_coe_one : (x : Equiv.Perm V) = 1 := by
      rw [hx_eq_one]; rfl
    rw [h_x_coe_one]
    -- adjacentMovedCount Γ 1 = 0 in ℕ.
    have h_a1_one : adjacentMovedCount Γ (1 : Equiv.Perm V) = 0 := by
      unfold adjacentMovedCount
      apply Finset.card_eq_zero.mpr
      rw [Finset.filter_eq_empty_iff]
      intro v _
      change ¬ Γ.Adj v ((1 : Equiv.Perm V) v)
      rw [Equiv.Perm.one_apply]
      exact Γ.irrefl
    rw [h_a1_one]
    exact Nat.cast_zero
  · intros; exact Finset.mem_univ _
  · intros; exact inv_inv _

end Moore57
