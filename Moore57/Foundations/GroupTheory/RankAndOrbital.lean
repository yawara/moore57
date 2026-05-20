import Mathlib.GroupTheory.GroupAction.Basic
import Mathlib.Algebra.Group.Action.Prod
import Mathlib.SetTheory.Cardinal.Finite

/-!
# Rank and orbital structure for permutation groups

Higman 1964 (Mač–Sir §1) studies rank-3 permutation groups via the
**orbital structure** — the orbits of the diagonal `G`-action on `Ω × Ω`.

Mathlib has the basic `MulAction.orbit` and `MulAction.orbitRel`
machinery, plus the `Prod.mulAction` diagonal action on `Ω × Ω`, but
does **not** package the orbital quotient nor the rank concept.  This
file provides the minimal foundation:

## Main definitions

* `Moore57.orbital G Ω` — quotient of `Ω × Ω` by the diagonal G-action.
* `Moore57.permRank G Ω` — the rank of the action = `|orbital G Ω|`.

## Notes (D2 scope)

* `orbital`, `permRank`, `SameOrbital` — D2.0 (basic definitions).
* `swapOrbital`, `swapOrbital_involutive`, `IsSelfPaired`,
  `isSelfPaired_diagonal` — D2.1 + D2.2 (paired-orbital / self-paired
  criterion via `Prod.swap`).

Higher-level Higman 1964 rank-3 lemmas (D3.0-D3.6) build on this
foundation; see `Moore57/Papers/Higman1964/`.
-/

namespace Moore57

variable (G Ω : Type*) [Group G] [MulAction G Ω]

/-- The **orbitals** of a `G`-action on `Ω`: orbits of the diagonal action
on `Ω × Ω`.

In Higman's notation, the orbitals partition `Ω × Ω` into `G`-invariant
relations.  For `Ω = G/H` (a transitive action), the orbital count equals
the number of `(H, H)`-double cosets, also known as the rank of the action. -/
def orbital : Type _ :=
  Quotient (MulAction.orbitRel G (Ω × Ω))

/-- The **rank** of a permutation group action: the number of orbitals
(= orbits of `G` on `Ω × Ω`).

The action is called *rank-3* when this number equals 3, which is the
case Higman 1964 analyses. -/
noncomputable def permRank : ℕ :=
  Nat.card (orbital G Ω)

/-- Convenience alias: two pairs are in the same orbital iff the first lies in
the diagonal-action orbit of the second.

Unfolding through `MulAction.orbitRel_apply` + `MulAction.mem_orbit_iff`:
`SameOrbital G Ω a b ↔ ∃ g : G, g • b = a`. -/
def SameOrbital (a b : Ω × Ω) : Prop :=
  MulAction.orbitRel G (Ω × Ω) a b

theorem sameOrbital_iff_mem_orbit (a b : Ω × Ω) :
    SameOrbital G Ω a b ↔ a ∈ MulAction.orbit G b :=
  MulAction.orbitRel_apply

theorem sameOrbital_iff (a b : Ω × Ω) :
    SameOrbital G Ω a b ↔ ∃ g : G, g • b = a := by
  rw [sameOrbital_iff_mem_orbit]
  exact MulAction.mem_orbit_iff

/-! ### Paired orbital via `Prod.swap` (D2.1)

In Higman 1964 notation, for each `G_a`-orbit `Δ(a) ⊆ Ω \ {a}`, the
**paired orbit** is `Δ'(a) = { a^g | a^(g⁻¹) ∈ Δ(a) }`.  Equivalently,
in the orbital (= `G`-orbit on `Ω × Ω`) language: pair `(a, b)` with
`(b, a)` via `Prod.swap`, then induce the swap on the orbital quotient.

The key fact is that `Prod.swap` is `G`-equivariant for the diagonal
action: `(g • (a, b)).swap = g • (a, b).swap` (= Mathlib `smul_swap`
for the diagonal `Prod` Pow action). -/

/-- The diagonal `G`-action commutes with `Prod.swap`. -/
@[simp] theorem smul_swap_diagonal (g : G) (p : Ω × Ω) :
    (g • p).swap = g • p.swap := by
  -- Mathlib `smul_swap` (additive form of `pow_swap` on the diagonal `Pow` instance).
  ext <;> rfl

/-- The **paired orbital** map `swapOrbital : orbital G Ω → orbital G Ω`,
induced by `Prod.swap` on the orbital quotient.

For a transitive `G`-action and a vertex `a ∈ Ω`, the `G_a`-orbit `Δ(a)`
corresponds to an orbital `O_Δ`, and `Δ'(a)` corresponds to
`swapOrbital O_Δ`. -/
def swapOrbital : orbital G Ω → orbital G Ω :=
  Quotient.map' Prod.swap fun a b ⟨g, hg⟩ =>
    ⟨g, by simpa [smul_swap_diagonal] using congrArg Prod.swap hg⟩

@[simp] theorem swapOrbital_mk (p : Ω × Ω) :
    swapOrbital G Ω (Quotient.mk'' p) = Quotient.mk'' p.swap :=
  rfl

/-- `swapOrbital` is an involution: pairing twice returns the original orbital. -/
theorem swapOrbital_involutive :
    Function.Involutive (swapOrbital G Ω) := by
  intro O
  induction O using Quotient.inductionOn' with
  | _ p =>
    change swapOrbital G Ω (Quotient.mk'' p.swap) = Quotient.mk'' p
    rw [swapOrbital_mk, Prod.swap_swap]

/-! ### Self-paired orbitals (D2.2) -/

/-- An orbital `O` is **self-paired** if `swapOrbital O = O`.

In Higman 1964 terms, this captures the symmetry of the underlying
relation on `Ω`: `(a, b) ∈ O ⇔ (b, a) ∈ O`.  For Higman's rank-3
group analysis, a non-trivial self-paired orbital exists iff `|G|` is
even (Lem 1, 3). -/
def IsSelfPaired (O : orbital G Ω) : Prop :=
  swapOrbital G Ω O = O

/-- The **diagonal orbital** containing pairs `(a, a)`.

For a transitive action this is *the* diagonal orbital (the unique
orbital containing the diagonal of `Ω × Ω`); for general actions it is
one of possibly many orbitals supported on the diagonal. -/
def diagonalOrbital (a : Ω) : orbital G Ω :=
  Quotient.mk'' (a, a)

/-- The diagonal orbital is self-paired: `swap (a, a) = (a, a)`. -/
theorem isSelfPaired_diagonalOrbital (a : Ω) :
    IsSelfPaired G Ω (diagonalOrbital G Ω a) := by
  change swapOrbital G Ω (Quotient.mk'' (a, a)) = Quotient.mk'' (a, a)
  rw [swapOrbital_mk]
  rfl

end Moore57
