import Moore57.Foundations.GraphTheory.AutSubgroup
import Moore57.Moore57Graph.Characters
import Moore57.D19OnMoore57.E7Projection.ProjectionRepresentationSkeleton
import Moore57.D19OnMoore57.E7Projection.ProjectionTraceBridge
import Moore57.D19OnMoore57.Misc.Minus8ProjectionRepresentation
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

## Scope (B3.1+ done for all three characters)

* `chi1Subrep` — uses existing
  `D19OnMoore57/E7Projection/ProjectionTraceBridge.lean`.
* `chi0Subrep` — built fresh: E₅₇ toLin' idempotent + trace bridge.
* `chi2Subrep` — built fresh: EMinus8 toLin' idempotent + trace bridge
  (analogous to E₇ pattern, using `EMinus8Matrix_mul_EMinus8Matrix_eq_EMinus8Matrix`
  and `EMinus8Matrix_mul_permMatrix_eq_permMatrix_mul_EMinus8Matrix`).
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

/-! ### The χ₀ spectral subrepresentation (E₅₇ projection) -/

/-- `E_57.toLin'` is idempotent. -/
theorem E57Matrix_toLin'_isIdempotentElem (hΓ : IsMoore57 Γ) :
    IsIdempotentElem (E57Matrix V).toLin' := by
  rw [IsIdempotentElem, Module.End.mul_eq_comp, ← matrix_toLin'_mul,
    E57Matrix_mul_E57Matrix_eq_E57Matrix hΓ]

/-- `E_57` commutes with every `permMatrix`, in `toLin'` form. -/
theorem E57Matrix_toLin'_commute_permMatrix_toLin'
    (σ : Equiv.Perm V) :
    Commute (E57Matrix V).toLin' (permMatrix σ).toLin' :=
  toLin'_commute_of_mul_eq
    (E57Matrix_mul_permMatrix_eq_permMatrix_mul_E57Matrix σ)

/-- `E_57` commutes with every element of `autSubgroupPermRep`. -/
theorem E57Matrix_toLin'_commute_autSubgroupPermRep
    (Γ : SimpleGraph V) [DecidableRel Γ.Adj] (g : autSubgroup Γ) :
    Commute (E57Matrix V).toLin' (autSubgroupPermRep Γ g) :=
  E57Matrix_toLin'_commute_permMatrix_toLin' g.val

/-- Restricting a permutation matrix to the range of the `E_57` projection
has trace equal to the concrete `E57Matrix` trace. -/
theorem trace_restrict_E57Range_permMatrix_toLin'_eq_matrix_trace
    (hΓ : IsMoore57 Γ) (σ : Equiv.Perm V) :
    LinearMap.trace ℚ (LinearMap.range (E57Matrix V).toLin')
        ((permMatrix σ).toLin'.restrict (by
          intro x hx
          exact ((Module.End.mem_invtSubmodule_iff_mapsTo
            (f := (permMatrix σ).toLin')).mp
              ((LinearMap.IsIdempotentElem.commute_iff
                (E57Matrix_toLin'_isIdempotentElem (Γ := Γ) hΓ)
                (T := (permMatrix σ).toLin')).mp
                (E57Matrix_toLin'_commute_permMatrix_toLin' σ)).1) hx)) =
      Matrix.trace (E57Matrix V * permMatrix σ) := by
  have hcomm := E57Matrix_toLin'_commute_permMatrix_toLin' (V := V) σ
  rw [Moore57.LinearMap.trace_restrict_range_eq_trace_comp_of_isIdempotentElem
    (p := (E57Matrix V).toLin') (f := (permMatrix σ).toLin')
    (E57Matrix_toLin'_isIdempotentElem (Γ := Γ) hΓ) hcomm]
  rw [show (E57Matrix V).toLin' ∘ₗ (permMatrix σ).toLin' =
      (E57Matrix V * permMatrix σ).toLin' by rw [matrix_toLin'_mul]]
  exact trace_toLin'_eq_matrix_trace (E57Matrix V * permMatrix σ)

/-- The χ₀ spectral subrepresentation on `range (E_57).toLin'`. -/
noncomputable def chi0Subrep (Γ : SimpleGraph V) [DecidableRel Γ.Adj] :
    Representation ℚ (autSubgroup Γ)
      (LinearMap.range (E57Matrix V).toLin') :=
  Representation.onCommutingRange (autSubgroupPermRep Γ) (E57Matrix V).toLin'
    (E57Matrix_toLin'_commute_autSubgroupPermRep Γ)

/-- **B3.1+ χ₀ identification:** `χ₀(σ) = chi0Subrep.character σ`. -/
theorem chi0_eq_chi0Subrep_character
    (hΓ : IsMoore57 Γ) (g : autSubgroup Γ) :
    chi0 (V := V) g.val = (chi0Subrep Γ).character g := by
  unfold Representation.character chi0 chi0Subrep
  rw [Representation.onCommutingRange]
  change Matrix.trace (E57Matrix V * permMatrix g.val) =
      LinearMap.trace ℚ (LinearMap.range (E57Matrix V).toLin')
        ((autSubgroupPermRep Γ g).restrict
          (LinearMap.range_le_comap_of_commute _ _
            (E57Matrix_toLin'_commute_autSubgroupPermRep Γ g)))
  exact (trace_restrict_E57Range_permMatrix_toLin'_eq_matrix_trace
    (Γ := Γ) hΓ g.val).symm

/-! ### The χ₂ spectral subrepresentation (E₋₈ projection)

Build EMinus8 toLin' idempotent and trace bridge directly (analogous to
the existing E₇ bridge in `D19OnMoore57/E7Projection/ProjectionTraceBridge.lean`). -/

/-- `EMinus8.toLin'` is idempotent. -/
theorem EMinus8Matrix_toLin'_isIdempotentElem
    {Γ : SimpleGraph V} [DecidableRel Γ.Adj] (hΓ : IsMoore57 Γ) :
    IsIdempotentElem (EMinus8Matrix Γ).toLin' := by
  rw [IsIdempotentElem, Module.End.mul_eq_comp, ← matrix_toLin'_mul,
    EMinus8Matrix_mul_EMinus8Matrix_eq_EMinus8Matrix hΓ]

/-- `EMinus8` commutes with every graph-automorphism's `permMatrix`, in
`toLin'` form. -/
theorem EMinus8Matrix_toLin'_commute_permMatrix_toLin'
    (Γ : SimpleGraph V) [DecidableRel Γ.Adj] (σ : Equiv.Perm V)
    (haut : ∀ v w, Γ.Adj v w ↔ Γ.Adj (σ v) (σ w)) :
    Commute (EMinus8Matrix Γ).toLin' (permMatrix σ).toLin' :=
  toLin'_commute_of_mul_eq
    (EMinus8Matrix_mul_permMatrix_eq_permMatrix_mul_EMinus8Matrix σ haut)

/-- `EMinus8.toLin'` commutes with every element of `autSubgroupPermRep`. -/
theorem EMinus8Matrix_toLin'_commute_autSubgroupPermRep
    (Γ : SimpleGraph V) [DecidableRel Γ.Adj] (g : autSubgroup Γ) :
    Commute (EMinus8Matrix Γ).toLin' (autSubgroupPermRep Γ g) :=
  EMinus8Matrix_toLin'_commute_permMatrix_toLin' Γ g.val
    (mem_autSubgroup_iff.mp g.property)

/-- Restricting a permutation matrix to the range of the `EMinus8` projection
has trace equal to the concrete `EMinus8Matrix` trace. -/
theorem trace_restrict_EMinus8Range_permMatrix_toLin'_eq_matrix_trace
    (hΓ : IsMoore57 Γ) (σ : Equiv.Perm V)
    (haut : ∀ v w, Γ.Adj v w ↔ Γ.Adj (σ v) (σ w)) :
    LinearMap.trace ℚ (LinearMap.range (EMinus8Matrix Γ).toLin')
        ((permMatrix σ).toLin'.restrict (by
          intro x hx
          exact ((Module.End.mem_invtSubmodule_iff_mapsTo
            (f := (permMatrix σ).toLin')).mp
              ((LinearMap.IsIdempotentElem.commute_iff
                (EMinus8Matrix_toLin'_isIdempotentElem hΓ)
                (T := (permMatrix σ).toLin')).mp
                (EMinus8Matrix_toLin'_commute_permMatrix_toLin' Γ σ haut)).1) hx)) =
      Matrix.trace (EMinus8Matrix Γ * permMatrix σ) := by
  have hcomm := EMinus8Matrix_toLin'_commute_permMatrix_toLin' Γ σ haut
  rw [Moore57.LinearMap.trace_restrict_range_eq_trace_comp_of_isIdempotentElem
    (p := (EMinus8Matrix Γ).toLin') (f := (permMatrix σ).toLin')
    (EMinus8Matrix_toLin'_isIdempotentElem hΓ) hcomm]
  rw [show (EMinus8Matrix Γ).toLin' ∘ₗ (permMatrix σ).toLin' =
      (EMinus8Matrix Γ * permMatrix σ).toLin' by rw [matrix_toLin'_mul]]
  exact trace_toLin'_eq_matrix_trace (EMinus8Matrix Γ * permMatrix σ)

/-- The χ₂ spectral subrepresentation on `range (EMinus8Matrix Γ).toLin'`. -/
noncomputable def chi2Subrep (Γ : SimpleGraph V) [DecidableRel Γ.Adj] :
    Representation ℚ (autSubgroup Γ)
      (LinearMap.range (EMinus8Matrix Γ).toLin') :=
  Representation.onCommutingRange (autSubgroupPermRep Γ) (EMinus8Matrix Γ).toLin'
    (EMinus8Matrix_toLin'_commute_autSubgroupPermRep Γ)

/-- **B3.1+ χ₂ identification:** `χ₂(σ) = chi2Subrep.character σ`. -/
theorem chi2_eq_chi2Subrep_character
    (hΓ : IsMoore57 Γ) (g : autSubgroup Γ) :
    chi2 Γ g.val = (chi2Subrep Γ).character g := by
  unfold Representation.character chi2 chi2Subrep
  rw [Representation.onCommutingRange]
  change Matrix.trace (EMinus8Matrix Γ * permMatrix g.val) =
      LinearMap.trace ℚ (LinearMap.range (EMinus8Matrix Γ).toLin')
        ((autSubgroupPermRep Γ g).restrict
          (LinearMap.range_le_comap_of_commute _ _
            (EMinus8Matrix_toLin'_commute_autSubgroupPermRep Γ g)))
  exact (trace_restrict_EMinus8Range_permMatrix_toLin'_eq_matrix_trace
    hΓ g.val (mem_autSubgroup_iff.mp g.property)).symm

end Moore57
