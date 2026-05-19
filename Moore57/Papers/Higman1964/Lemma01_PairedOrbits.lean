import Moore57.Moore57Graph.Moore57Definition

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

This is purely a permutation-group statement and does not involve any
graph yet. We state it as a [skeleton] until the action infrastructure
(`MulAction G Ω`, pairing of orbits) is built.
-/

namespace Moore57.Papers.Higman1964

/-- **Lemma 1 (paired orbit ⇔ even order).** [skeleton]

A transitive permutation group `G` on `Ω` has a self-paired nontrivial
`G_a`-orbit iff `|G|` is even. -/
theorem lem1_paired_orbit_iff_even : True := by trivial

end Moore57.Papers.Higman1964
