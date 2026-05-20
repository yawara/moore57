import Mathlib.GroupTheory.GroupAction.Basic
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.GroupTheory.PGroup
import Moore57.Foundations.GroupAction.FixedPoints

set_option linter.unusedSectionVars false

/-!
# Subgroup-level fixed points for permutation groups (Mathlib native)

For a subgroup `G : Subgroup (Equiv.Perm V)` acting on `V`, the
Mathlib-native fixed point set is `MulAction.fixedPoints G V` (with the
inherited `MulAction G V` from the ambient `Equiv.Perm V`-action).

This file provides minimal bridges between `MulAction.fixedPoints G V`
and the single-element infrastructure in `FixedPoints.lean`
(`fixedVertexSet σ`, `fixedVertexCount σ`).

## Design choice

* The "Fix set" is `MulAction.fixedPoints G V : Set V` (Mathlib native,
  not a Moore57 wrapper).
* The "Fix count" is `Nat.card (MulAction.fixedPoints G V)` (or
  `Fintype.card` when an instance is available).
* Bridges to single-σ live as:
  - `mem_mulAction_fixedPoints_iff_forall_mem`
  - `mulAction_fixedPoints_eq_iInter_fixedVertexSet`
  - `mulAction_fixedPoints_closure_singleton_eq_fixedVertexSet`

## Why Mathlib native?

* `IsPGroup.card_modEq_card_fixedPoints` already gives mod-p constraints
  for free.
* `MulAction.fixedPoints` is monotone in the subgroup (`H ≤ G ⟹ Fix G ⊆
  Fix H`); no need to re-prove.
* `MulAction.Quotient` and `MulAction.orbit` are available; useful for
  the quotient action on `Fix(P)` when `P ◁ X` (Phase 2).
-/

namespace Moore57

open MulAction

variable {V : Type*}

section Basic

variable (G : Subgroup (Equiv.Perm V))

/-- **Characterisation via membership in `G`.**  A vertex `v` lies in
`MulAction.fixedPoints G V` iff every `σ ∈ G` fixes `v`. -/
theorem mem_mulAction_fixedPoints_iff_forall_mem (v : V) :
    v ∈ MulAction.fixedPoints G V ↔ ∀ σ ∈ G, (σ : Equiv.Perm V) v = v := by
  constructor
  · intro h σ hσ
    have := h ⟨σ, hσ⟩
    -- `· • v = v` for the subtype element ⟨σ, hσ⟩ unfolds to `σ v = v`.
    simpa using this
  · intro h ⟨σ, hσ⟩
    simpa using h σ hσ

/-- **Anti-monotonicity in the subgroup.**  `H ≤ G ⟹ Fix(G) ⊆ Fix(H)`. -/
theorem mulAction_fixedPoints_antitone {G H : Subgroup (Equiv.Perm V)}
    (hle : H ≤ G) :
    (MulAction.fixedPoints G V : Set V) ⊆ MulAction.fixedPoints H V := by
  intro v hv ⟨σ, hσ⟩
  have hσ_G : σ ∈ G := hle hσ
  have := hv ⟨σ, hσ_G⟩
  simpa using this

/-- **Bridge to single-element fix sets via intersection.** -/
theorem mulAction_fixedPoints_eq_iInter_fixedVertexSet :
    (MulAction.fixedPoints G V : Set V) =
      ⋂ σ : G, fixedVertexSet (σ : Equiv.Perm V) := by
  ext v
  simp only [Set.mem_iInter, mem_fixedVertexSet,
    MulAction.mem_fixedPoints]
  refine ⟨fun h σ => ?_, fun h ⟨σ, hσ⟩ => ?_⟩
  · simpa using h σ
  · simpa using h ⟨σ, hσ⟩

/-- **Top subgroup fix set.** -/
theorem mulAction_fixedPoints_top :
    (MulAction.fixedPoints (⊤ : Subgroup (Equiv.Perm V)) V : Set V) =
      ⋂ σ : Equiv.Perm V, fixedVertexSet σ := by
  ext v
  simp only [Set.mem_iInter, mem_fixedVertexSet,
    MulAction.mem_fixedPoints]
  refine ⟨fun h σ => ?_, fun h ⟨σ, _⟩ => ?_⟩
  · simpa using h ⟨σ, Subgroup.mem_top σ⟩
  · simpa using h σ

/-- **Bottom subgroup fix set is the whole space.** -/
theorem mulAction_fixedPoints_bot :
    (MulAction.fixedPoints (⊥ : Subgroup (Equiv.Perm V)) V : Set V) = Set.univ := by
  ext v
  refine ⟨fun _ => Set.mem_univ v, fun _ => ?_⟩
  intro ⟨σ, hσ⟩
  rw [Subgroup.mem_bot] at hσ
  subst hσ
  rfl

end Basic

section Closure

/-- **Single-element closure fix set equals single-element fix set.**

For any `σ : Equiv.Perm V`, the subgroup `Subgroup.closure {σ}` has fixed
points exactly `fixedVertexSet σ`.  Both directions:

* Any `v ∈ fixedVertexSet σ` is fixed by `σ^n` for all `n : ℤ` (via
  `Equiv.Perm.zpow_apply_eq_self_of_apply_eq_self`).
* Conversely, `σ ∈ closure {σ}` so `v` fixed by closure ⟹ `v` fixed by `σ`. -/
theorem mulAction_fixedPoints_closure_singleton_eq_fixedVertexSet
    (σ : Equiv.Perm V) :
    (MulAction.fixedPoints (Subgroup.closure {σ}) V : Set V) =
      fixedVertexSet σ := by
  ext v
  rw [mem_mulAction_fixedPoints_iff_forall_mem]
  simp only [mem_fixedVertexSet]
  constructor
  · intro h
    exact h σ (Subgroup.subset_closure (Set.mem_singleton σ))
  · intro hv τ hτ
    -- Every element of `closure {σ}` is a zpower of σ.
    rw [Subgroup.mem_closure_singleton] at hτ
    rcases hτ with ⟨n, rfl⟩
    exact Equiv.Perm.zpow_apply_eq_self_of_apply_eq_self hv n

end Closure

section FintypeInstance

variable [Fintype V] [DecidableEq V]

/-- **Decidable membership in `MulAction.fixedPoints G V`** when `G` is
finite: `v` is G-fixed iff all (finitely many) `g ∈ G` fix `v`. -/
instance instDecidablePredFixedPointsOfFiniteSubgroup
    (G : Subgroup (Equiv.Perm V)) [Fintype G] :
    DecidablePred (fun v : V => v ∈ MulAction.fixedPoints G V) :=
  fun v => show Decidable (∀ g : G, g • v = v) from inferInstance

/-- **Fintype instance for `MulAction.fixedPoints G V`** when `V` and `G`
are both finite.  Derived via the ambient `Fintype V` and decidable
predicate. -/
noncomputable instance instFintypeFixedPointsOfFiniteSubgroup
    (G : Subgroup (Equiv.Perm V)) [Fintype G] :
    Fintype (MulAction.fixedPoints G V) :=
  (Set.toFinite _).fintype

end FintypeInstance

section CardinalityBridges

variable [Fintype V] [DecidableEq V] (G : Subgroup (Equiv.Perm V))

/-- **Single-σ count equals closure-of-singleton count.**

`fixedVertexCount σ = Nat.card (MulAction.fixedPoints (closure {σ}) V)`.

Uses `Nat.card_congr` with the `Equiv.setCongr` derived from the set
equality `mulAction_fixedPoints_closure_singleton_eq_fixedVertexSet`. -/
theorem fixedVertexCount_eq_natCard_closure_fixedPoints (σ : Equiv.Perm V) :
    fixedVertexCount σ =
      Nat.card (MulAction.fixedPoints (Subgroup.closure {σ}) V) := by
  classical
  rw [fixedVertexCount_eq_card_fixedVertexSet, ← Nat.card_eq_fintype_card]
  exact Nat.card_congr
    (Equiv.setCongr
      (mulAction_fixedPoints_closure_singleton_eq_fixedVertexSet σ).symm)

end CardinalityBridges

end Moore57
