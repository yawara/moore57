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

/-! ### Orbital neighborhoods and intersection counts (D3.1)

For Higman 1964 Lem 2, we need to count `|N_{O₁}(a) ∩ N_{O₂}(b)|` and
show this depends only on the orbital containing `(a, b)`.

For each orbital `O` and basepoint `a ∈ Ω`, define
`orbitalNeighborhood O a := { c ∈ Ω | (a, c) ∈ O }`.  Intersection
counts of such neighborhoods are invariant under the diagonal
`G`-action, which gives Higman 1964 Lem 2 constancy. -/

/-- The "neighborhood" of `a` defined by the orbital `O`: the set of `c`
such that `(a, c)` lies in `O`. -/
def orbitalNeighborhood (O : orbital G Ω) (a : Ω) : Set Ω :=
  { c | (Quotient.mk'' (a, c) : orbital G Ω) = O }

@[simp] theorem mem_orbitalNeighborhood_iff (O : orbital G Ω) (a c : Ω) :
    c ∈ orbitalNeighborhood G Ω O a ↔
    (Quotient.mk'' (a, c) : orbital G Ω) = O :=
  Iff.rfl

/-- The orbital quotient is `G`-equivariant: `Quotient.mk'' p` depends
only on the `G`-orbit of `p`. -/
theorem quotient_mk_smul (g : G) (p : Ω × Ω) :
    (Quotient.mk'' p : orbital G Ω) = Quotient.mk'' (g • p) := by
  apply Quotient.sound
  refine ⟨g⁻¹, ?_⟩
  simp [← mul_smul]

/-- Bridge: `c ∈ orbitalNeighborhood O (g • a) ↔ g⁻¹ • c ∈ orbitalNeighborhood O a`.

This is the `G`-equivariance of the orbital neighborhood in a membership
form (without going through `Set.smul_set`). -/
theorem mem_orbitalNeighborhood_smul_left
    (O : orbital G Ω) (g : G) (a c : Ω) :
    c ∈ orbitalNeighborhood G Ω O (g • a) ↔
    g⁻¹ • c ∈ orbitalNeighborhood G Ω O a := by
  simp only [mem_orbitalNeighborhood_iff]
  -- Both sides equal `Quotient.mk'' (a, g⁻¹ • c) = O` once we transport
  -- the LHS via `(g • a, c) = g • (a, g⁻¹ • c)`.
  have hbridge :
      (Quotient.mk'' (g • a, c) : orbital G Ω) =
      Quotient.mk'' (a, g⁻¹ • c) := by
    have h_eq : ((g • a, c) : Ω × Ω) = (g : G) • ((a, g⁻¹ • c) : Ω × Ω) := by
      apply Prod.ext
      · rfl
      · change c = g • g⁻¹ • c
        rw [← mul_smul, mul_inv_cancel, one_smul]
    rw [h_eq, ← quotient_mk_smul]
  exact ⟨fun h => hbridge ▸ h, fun h => hbridge.symm ▸ h⟩

/-- The "intersection count" of two orbital neighborhoods at base pair
`(a, b)`: the number of `c` lying in both `orbitalNeighborhood O₁ a` and
`orbitalNeighborhood O₂ b`. -/
noncomputable def orbitalIntersectionCount
    (O₁ O₂ : orbital G Ω) (a b : Ω) : ℕ :=
  Nat.card { c : Ω // c ∈ orbitalNeighborhood G Ω O₁ a ∧
                       c ∈ orbitalNeighborhood G Ω O₂ b }

/-- **Higman 1964 Lem 2 backbone**: the orbital intersection count is
`G`-invariant under the diagonal action on the base pair `(a, b)`.

This is the structural reason the intersection numbers `λ, μ, λ₁, μ₁`
of Higman 1964 Lem 2 depend only on which orbital contains `(a, b)`.

Proof: bijection `c ↦ g⁻¹ • c` between the two subtypes, using
`mem_orbitalNeighborhood_smul_left` to transport membership. -/
theorem orbitalIntersectionCount_smul
    (O₁ O₂ : orbital G Ω) (g : G) (a b : Ω) :
    orbitalIntersectionCount G Ω O₁ O₂ (g • a) (g • b) =
    orbitalIntersectionCount G Ω O₁ O₂ a b := by
  unfold orbitalIntersectionCount
  apply Nat.card_eq_of_bijective (f := fun (x : { c : Ω //
      c ∈ orbitalNeighborhood G Ω O₁ (g • a) ∧
      c ∈ orbitalNeighborhood G Ω O₂ (g • b) }) =>
    (⟨g⁻¹ • x.val,
      (mem_orbitalNeighborhood_smul_left G Ω O₁ g a x.val).mp x.property.1,
      (mem_orbitalNeighborhood_smul_left G Ω O₂ g b x.val).mp x.property.2⟩ :
     { c : Ω // c ∈ orbitalNeighborhood G Ω O₁ a ∧
                c ∈ orbitalNeighborhood G Ω O₂ b }))
  refine ⟨?_, ?_⟩
  · -- Injective: g⁻¹ • c = g⁻¹ • c' ⟹ c = c'.
    rintro ⟨c, _⟩ ⟨c', _⟩ h
    apply Subtype.ext
    have hcc : g⁻¹ • c = g⁻¹ • c' := congrArg Subtype.val h
    exact MulAction.injective g⁻¹ hcc
  · -- Surjective: from ⟨c, hc⟩ : RHS, preimage is ⟨g • c, _⟩ : LHS.
    rintro ⟨c, hc1, hc2⟩
    refine ⟨⟨g • c, ?_, ?_⟩, ?_⟩
    · rw [mem_orbitalNeighborhood_smul_left, ← mul_smul, inv_mul_cancel, one_smul]
      exact hc1
    · rw [mem_orbitalNeighborhood_smul_left, ← mul_smul, inv_mul_cancel, one_smul]
      exact hc2
    · apply Subtype.ext
      change g⁻¹ • g • c = c
      rw [← mul_smul, inv_mul_cancel, one_smul]

/-- **Higman 1964 Lem 2 (orbital form)**: the intersection count depends
only on the orbital containing `(a, b)`, not on the specific representative.

This is the precise paper-faithful statement of constancy of the
intersection numbers `λ, μ, λ₁, μ₁`. -/
theorem orbitalIntersectionCount_orbital_invariant
    (O₁ O₂ : orbital G Ω) {a b a' b' : Ω}
    (h : SameOrbital G Ω (a, b) (a', b')) :
    orbitalIntersectionCount G Ω O₁ O₂ a b =
    orbitalIntersectionCount G Ω O₁ O₂ a' b' := by
  rw [sameOrbital_iff] at h
  obtain ⟨g, hg⟩ := h
  -- `hg : g • (a', b') = (a, b)`.  Extract component identities.
  have ha : g • a' = a := by
    have := congrArg Prod.fst hg; simpa using this
  have hb : g • b' = b := by
    have := congrArg Prod.snd hg; simpa using this
  rw [show a = g • a' from ha.symm, show b = g • b' from hb.symm]
  exact orbitalIntersectionCount_smul G Ω O₁ O₂ g a' b'

/-! ### Rank-3 actions (D3.1 prerequisites) -/

/-- A `G`-action on `Ω` is **rank 3** if there are exactly 3 orbitals
(orbits of `G` on `Ω × Ω`).

For a transitive action, this corresponds to the classical "rank-3
permutation group" — subdegrees `(1, k, l)` with `n = 1 + k + l = |Ω|`. -/
def IsRank3 : Prop :=
  permRank G Ω = 3

/-! ### Orbital neighborhood cardinality and reverse neighborhoods (D3.2)

For Higman 1964 Lem 3, we need:
1. The cardinality `|N_O(a)|` (the **subdegree** of `O` at `a`) is
   `G`-invariant — depends only on the orbit of `a`.
2. The **reverse** orbital neighborhood `N⁻_O(a) := {c | (c, a) ∈ O}`
   coincides with `N_{swapOrbital O}(a)`.

Combining (1) and (2): if `swapOrbital O₁ = O₂` (i.e., `O₁, O₂` are
paired), then `|N⁻_{O₁}(a)| = |N_{O₂}(a)|`.  Together with the
in-degree = out-degree fact for any orbital in a transitive action
(double-counting), this yields the Higman 1964 Lem 3 conclusion
`k = l` for odd-order rank-3 groups. -/

/-- The **subdegree** (cardinality of an orbital neighborhood) is
`G`-invariant under the diagonal action.

Proof: bijection `c ↦ g⁻¹ • c` between `N_O(g•a)` and `N_O(a)`. -/
theorem orbitalNeighborhood_card_smul
    (O : orbital G Ω) (g : G) (a : Ω) :
    Nat.card (orbitalNeighborhood G Ω O (g • a)) =
    Nat.card (orbitalNeighborhood G Ω O a) := by
  apply Nat.card_eq_of_bijective (f := fun (x : orbitalNeighborhood G Ω O (g • a)) =>
    (⟨g⁻¹ • x.val,
      (mem_orbitalNeighborhood_smul_left G Ω O g a x.val).mp x.property⟩ :
     orbitalNeighborhood G Ω O a))
  refine ⟨?_, ?_⟩
  · -- Injective
    rintro ⟨c, _⟩ ⟨c', _⟩ h
    apply Subtype.ext
    have hcc : g⁻¹ • c = g⁻¹ • c' := congrArg Subtype.val h
    exact MulAction.injective g⁻¹ hcc
  · -- Surjective: from ⟨c, hc⟩ : RHS, the preimage is ⟨g • c, _⟩.
    rintro ⟨c, hc⟩
    refine ⟨⟨g • c, ?_⟩, ?_⟩
    · rw [mem_orbitalNeighborhood_smul_left, ← mul_smul, inv_mul_cancel, one_smul]
      exact hc
    · apply Subtype.ext
      change g⁻¹ • g • c = c
      rw [← mul_smul, inv_mul_cancel, one_smul]

/-- The **reverse orbital neighborhood**: the set of `c` such that
`(c, a)` (rather than `(a, c)`) lies in `O`. -/
def orbitalReverseNeighborhood (O : orbital G Ω) (a : Ω) : Set Ω :=
  { c | (Quotient.mk'' (c, a) : orbital G Ω) = O }

@[simp] theorem mem_orbitalReverseNeighborhood_iff (O : orbital G Ω) (a c : Ω) :
    c ∈ orbitalReverseNeighborhood G Ω O a ↔
    (Quotient.mk'' (c, a) : orbital G Ω) = O :=
  Iff.rfl

/-- The reverse orbital neighborhood of `O` at `a` is the forward
neighborhood of the paired orbital `swapOrbital O` at `a`.

This bridges the "in-degree" and "out-degree" views of an orbital
through the pairing involution.

Proof: `(c, a) ∈ O ↔ (a, c) ∈ swap O`, by definition of `swapOrbital`. -/
theorem orbitalReverseNeighborhood_eq_orbitalNeighborhood_swap
    (O : orbital G Ω) (a : Ω) :
    orbitalReverseNeighborhood G Ω O a =
    orbitalNeighborhood G Ω (swapOrbital G Ω O) a := by
  ext c
  simp only [mem_orbitalReverseNeighborhood_iff, mem_orbitalNeighborhood_iff]
  constructor
  · intro h
    -- swap (c, a) = (a, c); apply swap to both sides of h.
    have : swapOrbital G Ω (Quotient.mk'' (c, a)) = swapOrbital G Ω O := by
      rw [h]
    rwa [swapOrbital_mk] at this
  · intro h
    -- Apply swap to both sides; use involution.
    have : swapOrbital G Ω (Quotient.mk'' (a, c)) = swapOrbital G Ω (swapOrbital G Ω O) := by
      rw [h]
    rw [swapOrbital_mk, swapOrbital_involutive] at this
    exact this

/-- **Higman 1964 Lem 3 backbone**: if `swapOrbital O₁ = O₂` (i.e., `O₁`
and `O₂` are paired orbitals), then for any `a`, the reverse
neighborhood of `O₁` at `a` coincides with the forward neighborhood of
`O₂` at `a`.

This is the structural identity behind the paper's "Δ'(a) = Γ(a)"
hypothesis in odd-order rank-3 groups. -/
theorem lem3_reverseNeighborhood_eq_neighborhood_of_paired
    {O₁ O₂ : orbital G Ω} (h : swapOrbital G Ω O₁ = O₂) (a : Ω) :
    orbitalReverseNeighborhood G Ω O₁ a =
    orbitalNeighborhood G Ω O₂ a := by
  rw [orbitalReverseNeighborhood_eq_orbitalNeighborhood_swap, h]

end Moore57
