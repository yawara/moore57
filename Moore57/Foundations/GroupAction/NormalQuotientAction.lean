import Moore57.Foundations.GroupAction.SubgroupFixed
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.Combinatorics.SimpleGraph.Basic

set_option linter.unusedSectionVars false

/-!
# Quotient action on a normal subgroup's fixed-point set

For a subgroup `P : Subgroup (Equiv.Perm V)` and a normalising element
`g ∈ Subgroup.normalizer (P : Set (Equiv.Perm V))`, `g` maps `MulAction.fixedPoints P V` to itself.

For an ambient `G ≤ Equiv.Perm V` with `P ◁ G` (i.e. `G ≤ Subgroup.normalizer (P : Set (Equiv.Perm V))`),
the entire group `G` acts on `Fix(P)`.  Since `P ≤ G` acts trivially on
`Fix(P)`, this induces a `G ⧸ P`-action on `Fix(P)`.

This is the formal content of Mačaj–Širáň §9 Lemma 25.

## Main results

* `maps_fixedPoints_of_normalizer`: `g ∈ Subgroup.normalizer (P : Set (Equiv.Perm V)) → g • Fix(P) ⊆ Fix(P)`.
* `restrictToFixedPoints`: the resulting `Equiv (Fix P) (Fix P)`.
* `P_acts_trivially_on_fixedPoints`: `p ∈ P → p` is identity on `Fix(P)`.
-/

namespace Moore57

open MulAction

variable {V : Type*}

/-- **Normaliser preserves fixed points.**

If `g` normalises `P` (i.e. `g P g⁻¹ = P`) and `v ∈ Fix(P)`, then
`g v ∈ Fix(P)`.

Proof: for any `p ∈ P`, `g⁻¹ p g ∈ P` (normalising property), so
`(g⁻¹ p g) v = v`.  Applying `g` to both sides: `p (g v) = g v`. -/
theorem maps_fixedPoints_of_normalizer
    (P : Subgroup (Equiv.Perm V))
    {g : Equiv.Perm V} (hg : g ∈ Subgroup.normalizer (P : Set (Equiv.Perm V)))
    {v : V} (hv : v ∈ MulAction.fixedPoints P V) :
    g v ∈ MulAction.fixedPoints P V := by
  rw [mem_mulAction_fixedPoints_iff_forall_mem]
  intro p hp
  -- Use the inverse form: g⁻¹ p g ∈ P.
  have hg' : g⁻¹ ∈ Subgroup.normalizer (P : Set (Equiv.Perm V)) := inv_mem hg
  rw [Subgroup.mem_normalizer_iff] at hg'
  have hgpg : g * p * g⁻¹ ∈ P := by
    -- hg' says: ∀ h, h ∈ P ↔ g⁻¹ h (g⁻¹)⁻¹ ∈ P, i.e. g⁻¹ h g ∈ P.
    -- Use the equivalence at h := g p g⁻¹: g p g⁻¹ ∈ P ↔ g⁻¹ (g p g⁻¹) g ∈ P.
    -- RHS simplifies: g⁻¹ g p g⁻¹ g = p.
    rw [Subgroup.mem_normalizer_iff] at hg
    exact (hg p).mp hp
  -- We have g p g⁻¹ ∈ P, equivalently (writing q = g p g⁻¹): q v = v.
  -- But we need: p (g v) = g v. Let's translate.
  -- (g p g⁻¹) (g v) = ((g p g⁻¹) ∘ g) v = (g p) v = g (p ?) ... hmm wrong direction.
  -- Try the other form. Use hgpg_inv : g⁻¹ p g ∈ P:
  have hg_normalize : ∀ h : Equiv.Perm V, h ∈ P ↔ g⁻¹ * h * g ∈ P := by
    rw [Subgroup.mem_normalizer_iff''] at hg
    exact hg
  have hgpg_inv : g⁻¹ * p * g ∈ P := (hg_normalize p).mp hp
  -- Now use hv at q := g⁻¹ p g ∈ P: q • v = v.
  have hq_v : ((⟨g⁻¹ * p * g, hgpg_inv⟩ : P) : Equiv.Perm V) v = v := by
    have := hv ⟨g⁻¹ * p * g, hgpg_inv⟩
    -- `MulAction.fixedPoints` membership: ∀ m, m • v = v.
    -- For P-action on V, `m • v = (m : Equiv.Perm V) v`.
    simpa [Subgroup.smul_def] using this
  -- hq_v : (g⁻¹ * p * g) v = v.
  -- Multiply by g on the left: g ((g⁻¹ * p * g) v) = g v.
  -- LHS = (g * g⁻¹ * p * g) v = (1 * p * g) v = (p * g) v = p (g v).
  have hgoal : p (g v) = g v := by
    have h1 : g ((g⁻¹ * p * g : Equiv.Perm V) v) = g v := by
      have hq_v' : ((g⁻¹ * p * g : Equiv.Perm V)) v = v := by
        simpa [Subgroup.coe_mk] using hq_v
      rw [hq_v']
    have h2 : g ((g⁻¹ * p * g : Equiv.Perm V) v) = p (g v) := by
      simp [Equiv.Perm.mul_apply]
    rw [h2] at h1
    exact h1
  -- Convert from `p (g v) = g v` (Equiv.Perm apply) to ⟨p, hp⟩ • (g v) = g v.
  change ((⟨p, hp⟩ : P) : Equiv.Perm V) (g v) = g v
  simpa [Subgroup.coe_mk] using hgoal

/-- **P-action on its own fixed points is trivial.**

Trivially, every `p ∈ P` acts as the identity on `MulAction.fixedPoints P V`. -/
theorem P_acts_trivially_on_fixedPoints
    (P : Subgroup (Equiv.Perm V))
    (p : P) {v : V} (hv : v ∈ MulAction.fixedPoints P V) :
    (p : Equiv.Perm V) v = v := by
  have := hv p
  simpa [Subgroup.smul_def] using this

section RestrictEquiv

variable (P : Subgroup (Equiv.Perm V))

/-- **Restriction of a normalising element to a permutation of `Fix(P)`.**

For `g ∈ N(P)`, `g` permutes `Fix(P)`.  This gives an
`Equiv (Fix P) (Fix P)` (i.e., a permutation of the fixed-point set).
The underlying value-function is `v ↦ g v`. -/
def restrictToFixedPoints
    {g : Equiv.Perm V}
    (hg : g ∈ Subgroup.normalizer (P : Set (Equiv.Perm V))) :
    Equiv (MulAction.fixedPoints P V) (MulAction.fixedPoints P V) where
  toFun := fun v => ⟨g v, maps_fixedPoints_of_normalizer P hg v.property⟩
  invFun := fun v => ⟨g⁻¹ v,
    maps_fixedPoints_of_normalizer P (inv_mem hg) v.property⟩
  left_inv := fun v => by
    apply Subtype.ext
    change g⁻¹ (g (v : V)) = (v : V)
    simp
  right_inv := fun v => by
    apply Subtype.ext
    change g (g⁻¹ (v : V)) = (v : V)
    simp

@[simp] theorem restrictToFixedPoints_apply_val
    {g : Equiv.Perm V}
    (hg : g ∈ Subgroup.normalizer (P : Set (Equiv.Perm V)))
    (v : MulAction.fixedPoints P V) :
    ((restrictToFixedPoints P hg v : MulAction.fixedPoints P V) : V) = g (v : V) :=
  rfl

/-- **`restrictToFixedPoints p = identity` for `p ∈ P`.**

For `p ∈ P`, the restriction to `Fix(P)` is the identity permutation. -/
theorem restrictToFixedPoints_of_mem_P
    {p : Equiv.Perm V} (hp : p ∈ P) :
    restrictToFixedPoints P (Subgroup.le_normalizer hp) = Equiv.refl _ := by
  apply Equiv.ext
  intro v
  apply Subtype.ext
  change p (v : V) = (v : V)
  exact P_acts_trivially_on_fixedPoints P ⟨p, hp⟩ v.property

end RestrictEquiv

section GraphAutPreservation

variable {Γ : SimpleGraph V}
variable (P : Subgroup (Equiv.Perm V))

/-- **Graph-automorphism property restricts to `Fix(P)`.**

If `g` normalises `P` and `g` is a graph automorphism of `Γ` (in the
sense `Γ.Adj a b ↔ Γ.Adj (g a) (g b)`), then the restricted permutation
on `Fix(P)` (via the induced subgraph) is also a graph automorphism. -/
theorem restrictToFixedPoints_isGraphAut
    {g : Equiv.Perm V}
    (hg : g ∈ Subgroup.normalizer (P : Set (Equiv.Perm V)))
    (hAut : ∀ a b : V, Γ.Adj a b ↔ Γ.Adj (g a) (g b))
    (x y : MulAction.fixedPoints P V) :
    Γ.Adj (x : V) (y : V) ↔
      Γ.Adj ((restrictToFixedPoints P hg x : V))
        ((restrictToFixedPoints P hg y : V)) :=
  hAut x y

end GraphAutPreservation

end Moore57
