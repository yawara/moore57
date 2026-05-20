import Mathlib.GroupTheory.Sylow
import Mathlib.GroupTheory.SchurZassenhaus

/-!
# Sylow + Schur-Zassenhaus bridge

Mathlib has both `Sylow` and `Subgroup.exists_right_complement'_of_coprime`
(Schur-Zassenhaus), but the latter takes a generic normal subgroup with
coprime order/index, not a Sylow directly.  This file bundles the two for
the common case of a *normal Sylow p-subgroup*, using the standard fact
`Sylow.card_coprime_index`.

## Main result

* `Sylow.exists_complement_of_normal` — a normal Sylow p-subgroup has a
  complement (equivalently, the ambient group is a semidirect product
  `Sylow_p ⋊ Complement`).

This is the Mathlib-level bridge from the `*_sylow*_normal` lemmas
proven for Mačaj–Širáň §9 Propositions 6, 7, 8 and Theorem 7 to the
**semidirect product structure** the paper uses to dispatch the
2-prime / 3-prime cases.  In particular, Moore57's `|Aut(Γ)| ≤ 375`
chain does not need Feit-Thompson or Philip Hall: the Sylow-level
arithmetic + Schur-Zassenhaus is sufficient.
-/

namespace Moore57

variable {G : Type*} [Group G] [Finite G]
variable {p : ℕ} [Fact p.Prime]

/-- A normal Sylow `p`-subgroup admits a complement in `G` (Schur-Zassenhaus
applied to Sylow's `(card P).Coprime P.index`). -/
theorem Sylow.exists_complement_of_normal
    (P : Sylow p G) [(P : Subgroup G).Normal] :
    ∃ K : Subgroup G, Subgroup.IsComplement' (P : Subgroup G) K :=
  Subgroup.exists_right_complement'_of_coprime P.card_coprime_index

/-- The "left" version: a normal Sylow admits a left complement. -/
theorem Sylow.exists_left_complement_of_normal
    (P : Sylow p G) [(P : Subgroup G).Normal] :
    ∃ K : Subgroup G, Subgroup.IsComplement' K (P : Subgroup G) :=
  Subgroup.exists_left_complement'_of_coprime P.card_coprime_index

end Moore57
