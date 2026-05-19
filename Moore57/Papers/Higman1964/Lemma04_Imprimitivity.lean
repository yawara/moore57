import Moore57.Moore57Graph.Moore57Definition

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Higman 1964, Lemma 4 (§2, Imprimitivity)

> The following are equivalent for a transitive rank-3 group `G`:
>
> * (i)   `G` is imprimitive and `k ≤ l`.
> * (ii)  `G_a ≠ G_{Γ(a)}` (the orbit stabiliser is strictly larger).
> * (iii) `Γ(a) = Γ(b)` for some `a ≠ b`.
>
> These conditions imply the systems of imprimitivity are
> `{a} ∪ Δ(a)`, hence `k + 1 ∣ n` and `k ≤ l`.

**Corollaries.**
* If `k ≤ l`, then `Δ(a) = Δ(b)` implies `a = b`.
* An imprimitive rank-3 group has a unique block decomposition and is
  doubly transitive on blocks.
* A rank-3 group of odd order is primitive.

[deferred-heavy]
-/

namespace Moore57.Papers.Higman1964

/-- **Lemma 4 (imprimitivity criterion).** [deferred-heavy] -/
theorem lem4_imprimitivity_equivalents : True := by trivial

/-- **Corollary (rank-3 of odd order is primitive).** [deferred-heavy] -/
theorem cor_lem4_odd_rank3_primitive : True := by trivial

end Moore57.Papers.Higman1964
