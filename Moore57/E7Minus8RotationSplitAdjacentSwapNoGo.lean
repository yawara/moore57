import Moore57.ReflectionAdjacentMovedPositive
import Moore57.E7Minus8CharacterBoundariesFromRotationSplit
import Moore57.E7Minus8RotationSplitLower47NoGo

/-!
# Rotation-split no-go from a reflection swapping an edge

The local Cameron/Higman Step 2 geometry supplies `56` fixed points whenever a
reflection interchanges an adjacent pair.  Since the trace-refined candidate
list only needs the weaker lower bound `47`, such an adjacent swap is now a
direct source of the current rotation-split no-go route.
-/

namespace Moore57

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

namespace D19ActsOnMoore57

/-- The rotation split and one adjacent edge swapped by a reflection supply the
E7 character-class boundary and side arithmetic consumed downstream. -/
theorem exists_e7ProjectionCharacterClassBoundary_and_sideArithmetic_of_adjacent_swap
    (h : D19ActsOnMoore57 V Γ)
    {dt : ZMod 19} {a b : V}
    (hab : Γ.Adj a b)
    (ha : h.smul (DihedralGroup.sr dt) a = b)
    (hb : h.smul (DihedralGroup.sr dt) b = a) :
    ∃ alpha beta gamma : ℕ,
      D19CharacterClassBoundary h.e7ProjectionRepresentation
        alpha beta gamma ∧
      (alpha : ℤ) - (beta : ℤ) = 33 ∧
      alpha ≤ 113 ∧ beta ≤ 58 :=
  h.exists_e7ProjectionCharacterClassBoundary_and_sideArithmetic_of_reflectionFixedCount_ge_fortySeven
    (dt := dt)
    (by
      have h56 :=
        h.fixedVertexCount_reflection_ge_fiftySix_of_adjacent_swap
          (k := dt) hab ha hb
      omega)

/-- The rotation split plus an adjacent-swap reflection supplies the old
linear-character input package. -/
theorem nonempty_d19LinearCharacterInput_of_rotation_split_and_adjacent_swap
    (h : D19ActsOnMoore57 V Γ)
    {dt : ZMod 19} {a b : V}
    (hab : Γ.Adj a b)
    (ha : h.smul (DihedralGroup.sr dt) a = b)
    (hb : h.smul (DihedralGroup.sr dt) b = a) :
    Nonempty (D19LinearCharacterInput h) :=
  h.nonempty_d19LinearCharacterInput_of_rotation_split_and_reflectionFixedCount_ge_fortySeven
    (dt := dt)
    (by
      have h56 :=
        h.fixedVertexCount_reflection_ge_fiftySix_of_adjacent_swap
          (k := dt) hab ha hb
      omega)

/-- One adjacent-swap reflection is now enough, together with the concrete
rotation split, to rule out the current final-gap boundary. -/
theorem no_currentFinalGapBoundary_of_rotation_split_and_adjacent_swap
    (h : D19ActsOnMoore57 V Γ)
    {dt : ZMod 19} {a b : V}
    (hab : Γ.Adj a b)
    (ha : h.smul (DihedralGroup.sr dt) a = b)
    (hb : h.smul (DihedralGroup.sr dt) b = a) :
    ¬ Nonempty (BranchOrbitABCCurrentFinalGapBoundary h) :=
  h.no_currentFinalGapBoundary_of_rotation_split_and_reflectionFixedCount_ge_fortySeven
    (dt := dt)
    (by
      have h56 :=
        h.fixedVertexCount_reflection_ge_fiftySix_of_adjacent_swap
          (k := dt) hab ha hb
      omega)

/-- Existential form: if some reflection swaps some edge, the current
rotation-split final-gap boundary is impossible. -/
theorem no_currentFinalGapBoundary_of_rotation_split_and_exists_adjacent_swap
    (h : D19ActsOnMoore57 V Γ)
    (hswap :
      ∃ dt : ZMod 19, ∃ a b : V,
        Γ.Adj a b ∧
        h.smul (DihedralGroup.sr dt) a = b ∧
        h.smul (DihedralGroup.sr dt) b = a) :
    ¬ Nonempty (BranchOrbitABCCurrentFinalGapBoundary h) := by
  rcases hswap with ⟨dt, a, b, hab, ha, hb⟩
  exact h.no_currentFinalGapBoundary_of_rotation_split_and_adjacent_swap
    hab ha hb

/-- Positive adjacent-moved count for one reflection is an equivalent entry
point to the adjacent-swap branch, so it also closes the current rotation-split
final-gap boundary. -/
theorem no_currentFinalGapBoundary_of_rotation_split_and_reflection_adjacentMovedCount_pos
    (h : D19ActsOnMoore57 V Γ)
    {dt : ZMod 19}
    (hpos : 0 < adjacentMovedCount Γ (h.smulEquiv (DihedralGroup.sr dt))) :
    ¬ Nonempty (BranchOrbitABCCurrentFinalGapBoundary h) := by
  exact h.no_currentFinalGapBoundary_of_rotation_split_and_exists_adjacent_swap
    ⟨dt, h.exists_adjacent_swap_of_reflection_adjacentMovedCount_pos dt hpos⟩

/-- The trace-refined raw reflection arithmetic now supplies the reflection
fixed-count lower-bound package with no extra hypotheses.  Hence the concrete
rotation split gives the E7 character-class boundary and side arithmetic
directly from the raw action. -/
theorem exists_e7ProjectionCharacterClassBoundary_and_sideArithmetic_of_raw_action
    (h : D19ActsOnMoore57 V Γ)
    (dt : ZMod 19) :
    ∃ alpha beta gamma : ℕ,
      D19CharacterClassBoundary h.e7ProjectionRepresentation
        alpha beta gamma ∧
      (alpha : ℤ) - (beta : ℤ) = 33 ∧
      alpha ≤ 113 ∧ beta ≤ 58 :=
  h.exists_e7ProjectionCharacterClassBoundary_and_sideArithmetic_of_reflectionFixedCountLower47
    h.reflectionFixedCountLower47_of_raw_action dt

/-- Rotation split plus raw reflection arithmetic constructs the old
linear-character input package without a separate fixed-count assumption. -/
theorem nonempty_d19LinearCharacterInput_of_rotation_split_and_raw_action
    (h : D19ActsOnMoore57 V Γ)
    (dt : ZMod 19) :
    Nonempty (D19LinearCharacterInput h) :=
  h.nonempty_d19LinearCharacterInput_of_rotation_split_and_reflectionFixedCountLower47
    h.reflectionFixedCountLower47_of_raw_action dt

/-- The current rotation-split final-gap boundary is impossible from the raw
D19 action alone. -/
theorem no_currentFinalGapBoundary_of_rotation_split_and_raw_action
    (h : D19ActsOnMoore57 V Γ) :
    ¬ Nonempty (BranchOrbitABCCurrentFinalGapBoundary h) :=
  h.no_currentFinalGapBoundary_of_rotation_split_and_reflection_adjacentMovedCount_pos
    (dt := 0) (h.reflection_adjacentMovedCount_pos 0)

end D19ActsOnMoore57

end

end Moore57
