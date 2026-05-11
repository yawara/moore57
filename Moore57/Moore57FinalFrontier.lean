import Moore57.PhaseSevenPrebuilt

/-!
# Final frontier: the remaining geometric witness

This file makes explicit the single remaining hypothesis needed to close the
`D19ActsOnMoore57` non-existence theorem from raw action alone.

After Phases 1-7, the only missing input is a function that constructs
`AdjacentMovedReflectionComplementResidual38Witness` from any
`h : D19ActsOnMoore57 V Γ`.  The compact witness asks for:

* a reflection index `k : ZMod 19`,
* `cross_disjoint`: the 56 selected A-fiber rotation orbits and their
  `sr k`-reflections are pairwise disjoint,
* `residual_contribution`: the complement of the `2×56` orbit pieces has
  filtered cardinality `38` for every nontrivial rotation.

The conditional theorem below packages the remaining gap.  Once a function
`witness_from_h : ∀ h, AdjacentMovedReflectionComplementResidual38Witness h
(h.orbitBaseSelectionInput_of_raw_action)` is produced, the non-existence
theorem follows immediately with no additional assumptions.

The theorem depends on only Lean's three standard foundational axioms
(`propext`, `Classical.choice`, `Quot.sound`); there are no custom axioms,
no sorries, and no other hypotheses are slipped in.
-/

namespace Moore57

/-- Conditional non-existence theorem: assuming the single geometric witness
constructor, `D19ActsOnMoore57 V Γ` is uninhabited. -/
theorem no_D19_acts_on_Moore57_of_geometricWitness
    {V : Type*} [Fintype V] [DecidableEq V]
    {Γ : SimpleGraph V} [DecidableRel Γ.Adj]
    (witness_from_h :
      ∀ h : D19ActsOnMoore57 V Γ,
        AdjacentMovedReflectionComplementResidual38Witness h
          (h.orbitBaseSelectionInput_of_raw_action)) :
    ¬ Nonempty (D19ActsOnMoore57 V Γ) := by
  rintro ⟨h⟩
  exact h.false_of_compactAdjacentMoved (witness_from_h h)

end Moore57
