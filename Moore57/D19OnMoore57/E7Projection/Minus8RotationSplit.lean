import Moore57.D19OnMoore57.E7Projection.Minus8CharacterBoundariesFromRotationSplit
import Moore57.D19OnMoore57.LinearCharacter.Nonempty
import Moore57.D19OnMoore57.Reflection.AdjacentMovedPositive

/-!
# Rotation-split no-go from the trace-refined reflection lower bound

The representation-theoretic part is now supplied directly by the rotation
split for the concrete E7 and `(-8)` projection representations.  Therefore
the current final-gap no-go needs only the remaining reflection fixed-count
lower bound `47`, which the trace-refined candidate list upgrades to the
paper count `56`.
-/

namespace Moore57

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

namespace D19ActsOnMoore57

/-- Rotation-split character construction plus one per-reflection lower bound
`fixedVertexCount ≥ 47` rules out the current final-gap boundary. -/
theorem no_currentFinalGapBoundary_of_rotation_split_and_reflectionFixedCount_ge_fortySeven
    (h : D19ActsOnMoore57 V Γ)
    {dt : ZMod 19}
    (hlower :
      47 ≤ fixedVertexCount (h.smulEquiv (DihedralGroup.sr dt))) :
    ¬ Nonempty (BranchOrbitABCCurrentFinalGapBoundary h) :=
  no_D19_currentFinalGapBoundary_of_nonempty_linearCharacterInput h
    (h.nonempty_d19LinearCharacterInput_of_rotation_split_and_reflectionFixedCount_ge_fortySeven
      hlower)

/-- Uniform lower-bound package version of
`no_currentFinalGapBoundary_of_rotation_split_and_reflectionFixedCount_ge_fortySeven`. -/
theorem no_currentFinalGapBoundary_of_rotation_split_and_reflectionFixedCountLower47
    (h : D19ActsOnMoore57 V Γ)
    (bounds : ReflectionFixedCountLower47 h)
    (dt : ZMod 19) :
    ¬ Nonempty (BranchOrbitABCCurrentFinalGapBoundary h) :=
  h.no_currentFinalGapBoundary_of_rotation_split_and_reflectionFixedCount_ge_fortySeven
    (bounds.lower dt)

end D19ActsOnMoore57

end

end Moore57

/-!
# Rotation-split no-go from a single E7 reflection trace value

The trace value `33` for one reflection forces the paper fixed count `56`.
Together with the rotation-split construction of the concrete E7 and `(-8)`
projection characters, this is enough to recover the old
`D19LinearCharacterInput` and hence the current-final-gap no-go.
-/

namespace Moore57

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

namespace D19ActsOnMoore57

/-- Per-reflection geometry consequence of E7 trace value `33`: the reflection
has fixed count `56`, hence the rotation-fixed center is a leaf of the
reflection fixed-induced graph. -/
theorem reflectionFixedCenterLeafAt_of_E7_reflection_trace_eq_33
    (h : D19ActsOnMoore57 V Γ)
    {dt : ZMod 19}
    (htrace33 :
      Matrix.trace (E7Matrix Γ * permMatrix (h.smulEquiv (DihedralGroup.sr dt))) =
        (33 : ℚ)) :
    ReflectionFixedCenterLeafAt h dt :=
  h.reflectionFixedCenterLeafAt_of_fixedVertexCount_eq_56 dt
    (h.fixedVertexCount_reflection_eq_56_of_E7_trace_eq_33 dt htrace33)

/-- Uniform E7 reflection trace value `33` gives the fixed-center leaf
boundary for all reflections. -/
theorem reflectionFixedCenterLeafBoundary_of_E7_reflection_trace_eq_33_all
    (h : D19ActsOnMoore57 V Γ)
    (htrace33 :
      ∀ dt : ZMod 19,
        Matrix.trace (E7Matrix Γ * permMatrix (h.smulEquiv (DihedralGroup.sr dt))) =
          (33 : ℚ)) :
    ReflectionFixedCenterLeafBoundary h where
  degree_le_one := by
    intro dt
    exact
      (h.reflectionFixedCenterLeafAt_of_E7_reflection_trace_eq_33
        (htrace33 dt)).degree_le_one

/-- Rotation-split character construction plus one E7 reflection trace value
`33` rules out the current final-gap boundary. -/
theorem no_currentFinalGapBoundary_of_rotation_split_and_E7_reflection_trace_eq_33
    (h : D19ActsOnMoore57 V Γ)
    {dt : ZMod 19}
    (htrace33 :
      Matrix.trace (E7Matrix Γ * permMatrix (h.smulEquiv (DihedralGroup.sr dt))) =
        (33 : ℚ)) :
    ¬ Nonempty (BranchOrbitABCCurrentFinalGapBoundary h) :=
  no_D19_currentFinalGapBoundary_of_nonempty_linearCharacterInput h
    (h.nonempty_d19LinearCharacterInput_of_rotation_split_and_E7_reflection_trace_eq_33
      htrace33)

/-- Uniform E7 reflection trace value `33` version of the rotation-split no-go. -/
theorem no_currentFinalGapBoundary_of_rotation_split_and_E7_reflection_trace_eq_33_all
    (h : D19ActsOnMoore57 V Γ)
    (htrace33 :
      ∀ dt : ZMod 19,
        Matrix.trace (E7Matrix Γ * permMatrix (h.smulEquiv (DihedralGroup.sr dt))) =
          (33 : ℚ)) :
    ¬ Nonempty (BranchOrbitABCCurrentFinalGapBoundary h) :=
  h.no_currentFinalGapBoundary_of_rotation_split_and_E7_reflection_trace_eq_33
    (htrace33 0)

end D19ActsOnMoore57

end

end Moore57

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

