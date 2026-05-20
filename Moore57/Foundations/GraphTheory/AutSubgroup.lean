import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Combinatorics.SimpleGraph.Basic

set_option linter.unusedSectionVars false

/-!
# `Moore57.autSubgroup Γ` — the automorphism group of `Γ` as a subgroup of `Equiv.Perm V`

The Mačaj–Širáň main statement `|Aut(Γ)| ≤ 375` is naturally a statement
about the order of a subgroup of `Equiv.Perm V`.  This file provides the
canonical definition, mirroring the predicate
`∀ σ ∈ G, ∀ a b, Γ.Adj a b ↔ Γ.Adj (σ a) (σ b)` already used throughout
the Moore57 papers scaffold.

## Main definitions

* `Moore57.autSubgroup Γ : Subgroup (Equiv.Perm V)` — the maximal
  subgroup of permutations preserving adjacency.

* `Moore57.mem_autSubgroup_iff` — membership iff the adjacency-preservation
  predicate holds.

## Main bridges

* `Moore57.autSubgroup_le_iff` — `X ≤ autSubgroup Γ` is the existing
  hypothesis form `∀ σ ∈ X, ∀ a b, Γ.Adj a b ↔ Γ.Adj (σ a) (σ b)`.
-/

namespace Moore57

variable {V : Type*}

/-- The automorphism group of a simple graph `Γ`, as a subgroup of
`Equiv.Perm V`.  `σ ∈ autSubgroup Γ` iff `σ` preserves the adjacency
relation in both directions. -/
def autSubgroup (Γ : SimpleGraph V) : Subgroup (Equiv.Perm V) where
  carrier := {σ | ∀ a b : V, Γ.Adj a b ↔ Γ.Adj (σ a) (σ b)}
  one_mem' := by intro a b; rfl
  mul_mem' := fun {σ τ} hσ hτ a b => by
    rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, ← hσ, ← hτ]
  inv_mem' := fun {σ} hσ a b => by
    have h := hσ (σ⁻¹ a) (σ⁻¹ b)
    -- h : Γ.Adj (σ⁻¹ a) (σ⁻¹ b) ↔ Γ.Adj (σ (σ⁻¹ a)) (σ (σ⁻¹ b))
    have ha : σ (σ⁻¹ a) = a := by simp
    have hb : σ (σ⁻¹ b) = b := by simp
    rw [ha, hb] at h
    exact h.symm

/-- Membership in `autSubgroup Γ` unfolds to the adjacency-preservation
predicate. -/
@[simp] theorem mem_autSubgroup_iff {Γ : SimpleGraph V} {σ : Equiv.Perm V} :
    σ ∈ autSubgroup Γ ↔ ∀ a b : V, Γ.Adj a b ↔ Γ.Adj (σ a) (σ b) :=
  Iff.rfl

/-- `X ≤ autSubgroup Γ` iff every `σ ∈ X` preserves adjacency.

This is the bridge between the explicit hypothesis form used throughout
the papers scaffold and the subgroup-level statement. -/
theorem autSubgroup_le_iff {Γ : SimpleGraph V} {X : Subgroup (Equiv.Perm V)} :
    X ≤ autSubgroup Γ ↔ ∀ σ ∈ X, ∀ a b : V, Γ.Adj a b ↔ Γ.Adj (σ a) (σ b) := by
  constructor
  · intro h σ hσ a b
    exact (h hσ) a b
  · intro h σ hσ
    exact h σ hσ

end Moore57
