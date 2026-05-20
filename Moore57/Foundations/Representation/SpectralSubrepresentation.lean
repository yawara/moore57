import Moore57.Foundations.GraphTheory.AutSubgroup
import Moore57.Moore57Graph.Characters
import Moore57.D19OnMoore57.E7Projection.ProjectionRepresentationSkeleton
import Moore57.D19OnMoore57.E7Projection.ProjectionTraceBridge
import Mathlib.RepresentationTheory.Basic
import Mathlib.RepresentationTheory.Character

set_option linter.unusedSectionVars false

/-!
# Spectral subrepresentation for `χ₁`

This file formalises the identification

```
chi1 Γ g.val = (chi1Subrep Γ).character g     for g : autSubgroup Γ
```

where `chi1Subrep Γ` is the restriction of the permutation representation
`autSubgroupPermRep Γ : Representation ℚ (autSubgroup Γ) (V → ℚ)` to the
`E7Matrix`-projection range (= 1729-dimensional 7-eigenspace).

This makes precise the §4 character-system view that `χ₁` is the character
of the subrepresentation on the 7-eigenspace of the adjacency matrix.

## Main definitions

* `Moore57.autSubgroupPermRep Γ` — the permutation representation of the
  graph automorphism subgroup on `V → ℚ`.
* `Moore57.chi1Subrep Γ` — its restriction to `range (E7Matrix Γ).toLin'`.

## Main theorem

* `Moore57.chi1_eq_chi1Subrep_character` — `χ₁(σ) = chi1Subrep.character σ`
  for `σ : autSubgroup Γ`.

## Note (B3.1+ scope)

Currently scoped to `χ₁` (the only character with a proven idempotent +
restriction trace bridge in `D19OnMoore57/E7Projection`).  The analogous
constructions for `χ₀` (E₅₇) and `χ₂` (E₋₈) require hoisting the
`*_toLin'_isIdempotentElem` lemmas (currently `private` in
`Order22OnMoore57/`) and an analogous trace bridge.
-/

namespace Moore57

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-! ### The autSubgroup permutation representation -/

/-- The permutation representation of `autSubgroup Γ` on `V → ℚ`, sending
`σ` to `(permMatrix σ).toLin'`.  This is the natural action of graph
automorphisms on the vector space of `ℚ`-valued functions on the vertex set.

The project-local `permMatrix` convention (`σ.symm.toPEquiv.toMatrix`) makes
this a true group homomorphism (no anti-hom flip). -/
noncomputable def autSubgroupPermRep (Γ : SimpleGraph V) [DecidableRel Γ.Adj] :
    Representation ℚ (autSubgroup Γ) (V → ℚ) where
  toFun g := (permMatrix g.val).toLin'
  map_one' := by
    change (permMatrix ((1 : autSubgroup Γ).val)).toLin' = 1
    rw [Subgroup.coe_one, moore57_permMatrix_one, Matrix.toLin'_one]
    rfl
  map_mul' g g' := by
    change (permMatrix ((g * g').val)).toLin' =
        (permMatrix g.val).toLin' * (permMatrix g'.val).toLin'
    rw [Subgroup.coe_mul, moore57_permMatrix_mul, Matrix.toLin'_mul]
    rfl

@[simp]
theorem autSubgroupPermRep_apply
    (Γ : SimpleGraph V) [DecidableRel Γ.Adj] (g : autSubgroup Γ) :
    autSubgroupPermRep Γ g = (permMatrix g.val).toLin' :=
  rfl

/-- The `E7` projection commutes with every element of `autSubgroupPermRep`,
since adjacency-preserving permutations commute with the adjacency-derived
projection `E₇`. -/
theorem E7Matrix_toLin'_commute_autSubgroupPermRep
    (Γ : SimpleGraph V) [DecidableRel Γ.Adj] (g : autSubgroup Γ) :
    Commute (E7Matrix Γ).toLin' (autSubgroupPermRep Γ g) :=
  E7Matrix_toLin'_commute_permMatrix Γ g.val (mem_autSubgroup_iff.mp g.property)

/-! ### The χ₁ spectral subrepresentation -/

/-- The χ₁ spectral subrepresentation: restriction of `autSubgroupPermRep Γ`
to `range (E7Matrix Γ).toLin'`, the 1729-dimensional 7-eigenspace.

This is the `Representation ℚ (autSubgroup Γ)`-valued realisation of
`χ₁` — its character is exactly `chi1`. -/
noncomputable def chi1Subrep (Γ : SimpleGraph V) [DecidableRel Γ.Adj] :
    Representation ℚ (autSubgroup Γ)
      (LinearMap.range (E7Matrix Γ).toLin') :=
  Representation.onCommutingRange (autSubgroupPermRep Γ) (E7Matrix Γ).toLin'
    (E7Matrix_toLin'_commute_autSubgroupPermRep Γ)

@[simp]
theorem chi1Subrep_apply_coe
    (Γ : SimpleGraph V) [DecidableRel Γ.Adj] (g : autSubgroup Γ)
    (x : LinearMap.range (E7Matrix Γ).toLin') :
    ((chi1Subrep Γ g x : LinearMap.range (E7Matrix Γ).toLin') : V → ℚ) =
      (permMatrix g.val).toLin' x :=
  rfl

/-! ### Character identification -/

/-- **B3.1+ main identification:** the spectral character `χ₁(σ)` is the
character of the subrepresentation `chi1Subrep` evaluated at `σ`.

Proof: unfold `Representation.character` to the trace of the restricted
linear map and apply the existing
`trace_restrict_E7Range_permMatrix_toLin'_eq_matrix_trace` bridge. -/
theorem chi1_eq_chi1Subrep_character
    (hΓ : IsMoore57 Γ) (g : autSubgroup Γ) :
    chi1 Γ g.val = (chi1Subrep Γ).character g := by
  unfold Representation.character chi1 chi1Subrep
  rw [Representation.onCommutingRange]
  change Matrix.trace (E7Matrix Γ * permMatrix g.val) =
      LinearMap.trace ℚ (LinearMap.range (E7Matrix Γ).toLin')
        ((autSubgroupPermRep Γ g).restrict
          (LinearMap.range_le_comap_of_commute _ _
            (E7Matrix_toLin'_commute_autSubgroupPermRep Γ g)))
  exact (trace_restrict_E7Range_permMatrix_toLin'_eq_matrix_trace hΓ g.val
    (mem_autSubgroup_iff.mp g.property)).symm

end Moore57
