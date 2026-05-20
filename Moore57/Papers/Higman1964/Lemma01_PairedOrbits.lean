import Moore57.Moore57Graph.Moore57Definition
import Moore57.Foundations.GroupTheory.RankAndOrbital

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Higman 1964, Lemma 1 (§1, Paired orbits)

> Let `G` be a transitive permutation group on `Ω`. For each `G_a`-orbit
> `Δ(a)`, define the *paired orbit*
> `Δ'(a) = { a^g | g ∈ G, a^{g⁻¹} ∈ Δ(a) }`.
> Then `G_a` has a self-paired orbit ≠ `{a}` iff `|G|` is even.

(cf. WIELANDT [7], 16.6.)

## Status

* `lem1_paired_orbit_iff_even`: paper-stub (full Cauchy + pairing
  argument, [deferred-heavy]).
* `lem1_self_paired_iff_swap_fixed`: **proven** — the abstract
  reformulation: `IsSelfPaired O ↔ swapOrbital G Ω O = O`.  This is
  just the unfolded definition; recorded for clarity.
* `lem1_diagonal_self_paired`: **proven** — Moore57-style instance
  for the diagonal orbital (always self-paired regardless of `|G|`).
* `lem1_swapOrbital_involutive`: **proven** — the basic involution
  identity `swapOrbital ∘ swapOrbital = id`.

The non-trivial direction (the *existence* of a non-diagonal self-paired
orbital ⇔ `|G|` even) requires Cauchy's theorem on order-2 elements +
the pairing argument; that remains [deferred-heavy].
-/

namespace Moore57.Papers.Higman1964

variable (G Ω : Type*) [Group G] [MulAction G Ω]

/-- **Lemma 1 (abstract reformulation): self-paired ⇔ swap-fixed**. [done]

The Moore57 framework's `IsSelfPaired` predicate (on the `orbital`
quotient) is literally `swapOrbital O = O`.  This restates the
definition for paper-faithful clarity. -/
theorem lem1_self_paired_iff_swap_fixed (O : Moore57.orbital G Ω) :
    Moore57.IsSelfPaired G Ω O ↔ Moore57.swapOrbital G Ω O = O :=
  Iff.rfl

/-- **Lemma 1 (diagonal instance): the diagonal orbital is always
self-paired**. [done]

The diagonal orbital `{(a, a)}` (more precisely, the `G`-orbit through
`(a, a) ∈ Ω × Ω`) is self-paired since `(a, a).swap = (a, a)`.  This
is the trivial part of Lemma 1 (it holds regardless of `|G|`'s parity). -/
theorem lem1_diagonal_self_paired (a : Ω) :
    Moore57.IsSelfPaired G Ω (Moore57.diagonalOrbital G Ω a) :=
  Moore57.isSelfPaired_diagonalOrbital G Ω a

/-- **Lemma 1 (involution): pairing is an involution on the orbital
quotient**. [done]

The map `swapOrbital : orbital G Ω → orbital G Ω` is its own inverse.
This is the structural backbone of Lemma 1: the set of orbitals splits
into pairs `{O, swapOrbital O}` (size 2) and singletons (the self-paired
orbitals).  Counting modulo 2 then gives the Lemma 1 conclusion via
Cauchy's theorem. -/
theorem lem1_swapOrbital_involutive :
    Function.Involutive (Moore57.swapOrbital G Ω) :=
  Moore57.swapOrbital_involutive G Ω

/-- **Lemma 1 (paired orbit ⇔ even order).** [deferred-heavy]

A transitive permutation group `G` on `Ω` has a non-diagonal self-paired
`G`-orbital iff `|G|` is even.

The forward direction uses Cauchy's theorem (an element of order 2 fixes
its corresponding orbital pair).  The reverse direction uses the
swap-involution: if every non-diagonal orbital is non-self-paired, they
pair up into 2-element sets, forcing the off-diagonal orbital count to
be even — and then the structural relation between this count and `|G|`
(via Burnside) gives the parity claim.

The structural backbone (`swapOrbital`, `IsSelfPaired`, involution) is
proven in this file; the Cauchy + counting argument remains deferred. -/
theorem lem1_paired_orbit_iff_even : True := by trivial

end Moore57.Papers.Higman1964
