import Moore57.D19OnMoore57.D19Core.ConstructiveFinal
import Moore57.D19OnMoore57.D19Core.RepresentationCharacter
import Moore57.D19OnMoore57.Final.Inputs
import Moore57.D19OnMoore57.LinearCharacter.Input

/-!
# Dimension equation from the D19 linear-character equality

The full class-character equality
`trace (E7Matrix Γ * permMatrix (h.smulEquiv g)) =
  d19LinearCharacter α β γ g`
specialized at the identity element, combined with the Higman trace formula
applied to the identity permutation, gives the 7-eigenspace dimension equation
`α + β + 18 γ = 1729`.

The arithmetic constraint `α + β + 18 γ = 1729` is currently a hypothesis on
`TraceMultiplicityData`.  This file shows that under the full linear-character
equality on `D19`, the constraint is automatically true for any natural
multiplicities `α, β, γ`.
-/

namespace Moore57

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- The identity permutation fixes every vertex, so its `fixedVertexCount` is
the total vertex count. -/
@[simp] theorem fixedVertexCount_one :
    fixedVertexCount (1 : Equiv.Perm V) = Fintype.card V := by
  classical
  unfold fixedVertexCount
  rw [Finset.filter_true_of_mem]
  · exact Finset.card_univ
  · intro v _
    rfl

omit [DecidableEq V] in
/-- The identity permutation never sends any vertex to an adjacent one in a
simple graph, since `Γ` is irreflexive. -/
@[simp] theorem adjacentMovedCount_one :
    adjacentMovedCount Γ (1 : Equiv.Perm V) = 0 := by
  classical
  unfold adjacentMovedCount
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro v _
  simp

namespace IsMoore57

/-- Higman trace formula at the identity gives the 7-eigenspace dimension `1729`
for `Moore57`. -/
theorem trace_E7Matrix_one (hΓ : IsMoore57 Γ) :
    Matrix.trace (E7Matrix Γ * permMatrix (1 : Equiv.Perm V)) = 1729 := by
  rw [hΓ.higman_trace_formula]
  rw [fixedVertexCount_one, adjacentMovedCount_one, hΓ.card]
  norm_num

end IsMoore57

namespace D19ActsOnMoore57

variable {h : D19ActsOnMoore57 V Γ}

/-- The 7-eigenspace dimension equation `α + β + 18 γ = 1729` follows from any
linear-character equality on `D19`, without requiring it as a separate
multiplicity field. -/
theorem dimension_eq_of_linear_character
    (alpha beta gamma : ℕ)
    (hlin : ∀ g : DihedralGroup 19,
      Matrix.trace (E7Matrix Γ * permMatrix (h.smulEquiv g)) =
        (d19LinearCharacter alpha beta gamma g : ℚ)) :
    alpha + beta + 18 * gamma = 1729 := by
  have hkey := hlin 1
  rw [h.smulEquiv_one, h.isMoore.trace_E7Matrix_one,
    d19LinearCharacter_one] at hkey
  exact_mod_cast hkey.symm

/-- The reflection-character equation `α - β = 33` follows from the
linear-character equality at any reflection element together with the standard
involution counts `a₀(t) = 56` and `a₁(t) = 112`. -/
theorem reflection_eq_of_linear_character
    (alpha beta gamma : ℕ)
    (hlin : ∀ g : DihedralGroup 19,
      Matrix.trace (E7Matrix Γ * permMatrix (h.smulEquiv g)) =
        (d19LinearCharacter alpha beta gamma g : ℚ))
    {d : ZMod 19}
    (ha0 : fixedVertexCount (h.smulEquiv (DihedralGroup.sr d)) = 56)
    (ha1 : adjacentMovedCount Γ (h.smulEquiv (DihedralGroup.sr d)) = 112) :
    (alpha : ℤ) - (beta : ℤ) = 33 := by
  have hkey := hlin (DihedralGroup.sr d)
  rw [h.isMoore.higman_trace_formula, ha0, ha1,
    d19LinearCharacter_reflection] at hkey
  have hℚ : (((alpha : ℤ) - (beta : ℤ) : ℤ) : ℚ) = ((33 : ℤ) : ℚ) := by
    rw [← hkey]; push_cast; norm_num
  exact_mod_cast hℚ

/-- Conversely, the full linear-character equality and the multiplicity
reflection equation force the standard reflection fixed count as soon as the
reflection adjacent-moved count is `112`. -/
theorem fixedVertexCount_reflection_eq_56_of_linear_character
    (alpha beta gamma : ℕ)
    (hlin : ∀ g : DihedralGroup 19,
      Matrix.trace (E7Matrix Γ * permMatrix (h.smulEquiv g)) =
        (d19LinearCharacter alpha beta gamma g : ℚ))
    (hreflection : (alpha : ℤ) - (beta : ℤ) = 33)
    {d : ZMod 19}
    (ha1 : adjacentMovedCount Γ (h.smulEquiv (DihedralGroup.sr d)) = 112) :
    fixedVertexCount (h.smulEquiv (DihedralGroup.sr d)) = 56 := by
  have hkey := hlin (DihedralGroup.sr d)
  rw [h.isMoore.higman_trace_formula, ha1, d19LinearCharacter_reflection] at hkey
  have hreflectionℚ : (((alpha : ℤ) - (beta : ℤ) : ℤ) : ℚ) = 33 := by
    exact_mod_cast hreflection
  rw [hreflectionℚ] at hkey
  have hcountℚ :
      (fixedVertexCount (h.smulEquiv (DihedralGroup.sr d)) : ℚ) = 56 := by
    linarith
  exact_mod_cast hcountℚ

namespace D19LinearCharacterInput

/-- A `D19LinearCharacterInput` automatically witnesses the dimension equation
through its full linear-character equality, in addition to the
`multiplicity.dimension` field. -/
theorem dimension (hin : D19LinearCharacterInput h) :
    hin.multiplicity.alpha + hin.multiplicity.beta +
      18 * hin.multiplicity.gamma = 1729 :=
  dimension_eq_of_linear_character _ _ _ hin.linear_character

/-- A `D19LinearCharacterInput` automatically witnesses the reflection equation
`α - β = 33` for any reflection class element, given the standard involution
counts. -/
theorem reflection_of_counts
    (hin : D19LinearCharacterInput h)
    {d : ZMod 19}
    (ha0 : fixedVertexCount (h.smulEquiv (DihedralGroup.sr d)) = 56)
    (ha1 : adjacentMovedCount Γ (h.smulEquiv (DihedralGroup.sr d)) = 112) :
    (hin.multiplicity.alpha : ℤ) - (hin.multiplicity.beta : ℤ) = 33 :=
  reflection_eq_of_linear_character _ _ _ hin.linear_character ha0 ha1

/-- A `D19LinearCharacterInput` recovers the standard reflection fixed count
from the standard reflection adjacent-moved count. -/
theorem fixedVertexCount_reflection_eq_56_of_adjacentMovedCount_eq_112
    (hin : D19LinearCharacterInput h)
    {d : ZMod 19}
    (ha1 : adjacentMovedCount Γ (h.smulEquiv (DihedralGroup.sr d)) = 112) :
    fixedVertexCount (h.smulEquiv (DihedralGroup.sr d)) = 56 :=
  fixedVertexCount_reflection_eq_56_of_linear_character
    hin.multiplicity.alpha hin.multiplicity.beta hin.multiplicity.gamma
    hin.linear_character hin.multiplicity.reflection ha1

/-- Build `D19LinearCharacterInput` from the linear-character equality, the
standard involution counts at one reflection, and the `(-8)`-eigenspace bounds
`α ≤ 113`, `β ≤ 58`.  The dimension and reflection arithmetic constraints are
filled in automatically. -/
noncomputable def ofLinearCharacterAndCounts
    (alpha beta gamma : ℕ)
    (hAlpha : alpha ≤ 113)
    (hBeta : beta ≤ 58)
    (hlin : ∀ g : DihedralGroup 19,
      Matrix.trace (E7Matrix Γ * permMatrix (h.smulEquiv g)) =
        (d19LinearCharacter alpha beta gamma g : ℚ))
    {d : ZMod 19}
    (ha0 : fixedVertexCount (h.smulEquiv (DihedralGroup.sr d)) = 56)
    (ha1 : adjacentMovedCount Γ (h.smulEquiv (DihedralGroup.sr d)) = 112) :
    D19LinearCharacterInput h where
  multiplicity :=
    { alpha := alpha
      beta := beta
      gamma := gamma
      reflection := reflection_eq_of_linear_character alpha beta gamma hlin ha0 ha1
      dimension := dimension_eq_of_linear_character alpha beta gamma hlin
      minus8_trivial_nonneg := hAlpha
      minus8_sign_nonneg := hBeta }
  linear_character := hlin

end D19LinearCharacterInput

end D19ActsOnMoore57

/-- Convenience: produce `D19FinalCharacterInputs` from a linear-character
witness together with the standard rotation fixed-count bound. -/
noncomputable def D19FinalCharacterInputs.ofD19LinearCharacterInput
    {V : Type*} [Fintype V] [DecidableEq V]
    {Γ : SimpleGraph V} [DecidableRel Γ.Adj]
    {h : D19ActsOnMoore57 V Γ}
    (hin : D19ActsOnMoore57.D19LinearCharacterInput h)
    (fixedUpperBound : D19ActsOnMoore57.RotationFixedUpperBoundInput h) :
    D19FinalCharacterInputs h where
  representation := hin.toD19RepresentationCharacterInput
  fixedUpperBound := fixedUpperBound

end Moore57

/-!
# Connectors for linear-character dimension data

This file keeps the representation-side boundary close to mathlib character
data.  A full `Representation.character` decomposition, together with the
standard reflection counts, is enough to build the existing linear-character
input; the dimension and reflection arithmetic fields are filled by
`D19LinearCharacterDimension`.
-/

namespace Moore57

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

namespace D19ActsOnMoore57

variable {h : D19ActsOnMoore57 V Γ}

namespace D19LinearCharacterInput

/-- Build the full linear-character input from a mathlib representation
character identity and the standard reflection counts.

Compared with `ofRepresentationCharacter`, this does not ask for a
pre-packaged `TraceMultiplicityData`: the dimension equation and the
reflection equation are derived from the full linear-character equality by
`ofLinearCharacterAndCounts`. -/
noncomputable def ofRepresentationCharacterAndCounts
    {W : Type*} [AddCommGroup W] [Module ℚ W] [FiniteDimensional ℚ W]
    (ρ : Representation ℚ (DihedralGroup 19) W)
    (alpha beta gamma : ℕ)
    (minus8_trivial_nonneg : alpha ≤ 113)
    (minus8_sign_nonneg : beta ≤ 58)
    (trace_eq_character :
      ∀ g : DihedralGroup 19,
        Matrix.trace (E7Matrix Γ * permMatrix (h.smulEquiv g)) =
          ρ.character g)
    (character_eq_d19Linear :
      ∀ g : DihedralGroup 19,
        ρ.character g =
          (d19LinearCharacter alpha beta gamma g : ℚ))
    {d : ZMod 19}
    (ha0 : fixedVertexCount (h.smulEquiv (DihedralGroup.sr d)) = 56)
    (ha1 : adjacentMovedCount Γ (h.smulEquiv (DihedralGroup.sr d)) = 112) :
    D19LinearCharacterInput h :=
  ofLinearCharacterAndCounts (h := h) alpha beta gamma
    minus8_trivial_nonneg minus8_sign_nonneg
    (by
      intro g
      exact (trace_eq_character g).trans (character_eq_d19Linear g))
    ha0 ha1

end D19LinearCharacterInput

namespace D19RepresentationCharacterInput

/-- Forget a raw full linear-character equality with standard reflection counts
to the representation-character input consumed by the D19 pipeline. -/
noncomputable def ofLinearCharacterAndCounts
    (alpha beta gamma : ℕ)
    (minus8_trivial_nonneg : alpha ≤ 113)
    (minus8_sign_nonneg : beta ≤ 58)
    (hlin : ∀ g : DihedralGroup 19,
      Matrix.trace (E7Matrix Γ * permMatrix (h.smulEquiv g)) =
        (d19LinearCharacter alpha beta gamma g : ℚ))
    {d : ZMod 19}
    (ha0 : fixedVertexCount (h.smulEquiv (DihedralGroup.sr d)) = 56)
    (ha1 : adjacentMovedCount Γ (h.smulEquiv (DihedralGroup.sr d)) = 112) :
    D19RepresentationCharacterInput h :=
  (D19LinearCharacterInput.ofLinearCharacterAndCounts (h := h)
    alpha beta gamma minus8_trivial_nonneg minus8_sign_nonneg
    hlin ha0 ha1).toD19RepresentationCharacterInput

/-- Mathlib representation-character version of
`ofLinearCharacterAndCounts`. -/
noncomputable def ofRepresentationCharacterAndCounts
    {W : Type*} [AddCommGroup W] [Module ℚ W] [FiniteDimensional ℚ W]
    (ρ : Representation ℚ (DihedralGroup 19) W)
    (alpha beta gamma : ℕ)
    (minus8_trivial_nonneg : alpha ≤ 113)
    (minus8_sign_nonneg : beta ≤ 58)
    (trace_eq_character :
      ∀ g : DihedralGroup 19,
        Matrix.trace (E7Matrix Γ * permMatrix (h.smulEquiv g)) =
          ρ.character g)
    (character_eq_d19Linear :
      ∀ g : DihedralGroup 19,
        ρ.character g =
          (d19LinearCharacter alpha beta gamma g : ℚ))
    {d : ZMod 19}
    (ha0 : fixedVertexCount (h.smulEquiv (DihedralGroup.sr d)) = 56)
    (ha1 : adjacentMovedCount Γ (h.smulEquiv (DihedralGroup.sr d)) = 112) :
    D19RepresentationCharacterInput h :=
  (D19LinearCharacterInput.ofRepresentationCharacterAndCounts (h := h)
    ρ alpha beta gamma minus8_trivial_nonneg minus8_sign_nonneg
    trace_eq_character character_eq_d19Linear ha0 ha1).toD19RepresentationCharacterInput

end D19RepresentationCharacterInput

/-- Exposed component-boundary form of `ofLinearCharacterAndCounts`. -/
theorem representationCharacterComponentsBoundary_of_linearCharacterAndCounts
    (h : D19ActsOnMoore57 V Γ)
    (alpha beta gamma : ℕ)
    (minus8_trivial_nonneg : alpha ≤ 113)
    (minus8_sign_nonneg : beta ≤ 58)
    (hlin : ∀ g : DihedralGroup 19,
      Matrix.trace (E7Matrix Γ * permMatrix (h.smulEquiv g)) =
        (d19LinearCharacter alpha beta gamma g : ℚ))
    {d : ZMod 19}
    (ha0 : fixedVertexCount (h.smulEquiv (DihedralGroup.sr d)) = 56)
    (ha1 : adjacentMovedCount Γ (h.smulEquiv (DihedralGroup.sr d)) = 112) :
    RepresentationCharacterComponentsBoundary h :=
  (D19LinearCharacterInput.ofLinearCharacterAndCounts (h := h)
    alpha beta gamma minus8_trivial_nonneg minus8_sign_nonneg
    hlin ha0 ha1).representationCharacterComponentsBoundary

/-- Exposed component-boundary form for mathlib representation-character data.

This removes the explicit `finrank = 1729`, dimension arithmetic, and
reflection arithmetic assumptions from the representation side when a full
D19 linear-character identity and the standard reflection counts are
available. -/
theorem representationCharacterComponentsBoundary_of_representationCharacterAndCounts
    (h : D19ActsOnMoore57 V Γ)
    {W : Type*} [AddCommGroup W] [Module ℚ W] [FiniteDimensional ℚ W]
    (ρ : Representation ℚ (DihedralGroup 19) W)
    (alpha beta gamma : ℕ)
    (minus8_trivial_nonneg : alpha ≤ 113)
    (minus8_sign_nonneg : beta ≤ 58)
    (trace_eq_character :
      ∀ g : DihedralGroup 19,
        Matrix.trace (E7Matrix Γ * permMatrix (h.smulEquiv g)) =
          ρ.character g)
    (character_eq_d19Linear :
      ∀ g : DihedralGroup 19,
        ρ.character g =
          (d19LinearCharacter alpha beta gamma g : ℚ))
    {d : ZMod 19}
    (ha0 : fixedVertexCount (h.smulEquiv (DihedralGroup.sr d)) = 56)
    (ha1 : adjacentMovedCount Γ (h.smulEquiv (DihedralGroup.sr d)) = 112) :
    RepresentationCharacterComponentsBoundary h :=
  (D19LinearCharacterInput.ofRepresentationCharacterAndCounts (h := h)
    ρ alpha beta gamma minus8_trivial_nonneg minus8_sign_nonneg
    trace_eq_character character_eq_d19Linear ha0 ha1)
      |>.representationCharacterComponentsBoundary

end D19ActsOnMoore57

namespace D19FinalCharacterInputs

variable {h : D19ActsOnMoore57 V Γ}

/-- Build final character inputs from a full linear-character equality,
standard reflection counts, and a separately supplied fixed-count upper
bound. -/
noncomputable def ofLinearCharacterAndCounts
    (alpha beta gamma : ℕ)
    (minus8_trivial_nonneg : alpha ≤ 113)
    (minus8_sign_nonneg : beta ≤ 58)
    (hlin : ∀ g : DihedralGroup 19,
      Matrix.trace (E7Matrix Γ * permMatrix (h.smulEquiv g)) =
        (d19LinearCharacter alpha beta gamma g : ℚ))
    {d : ZMod 19}
    (ha0 : fixedVertexCount (h.smulEquiv (DihedralGroup.sr d)) = 56)
    (ha1 : adjacentMovedCount Γ (h.smulEquiv (DihedralGroup.sr d)) = 112)
    (fixedUpperBound : D19ActsOnMoore57.RotationFixedUpperBoundInput h) :
    D19FinalCharacterInputs h :=
  ofD19LinearCharacterInput
    (D19ActsOnMoore57.D19LinearCharacterInput.ofLinearCharacterAndCounts
      (h := h) alpha beta gamma minus8_trivial_nonneg
      minus8_sign_nonneg hlin ha0 ha1)
    fixedUpperBound

/-- Mathlib representation-character version of
`ofLinearCharacterAndCounts`. -/
noncomputable def ofRepresentationCharacterAndCounts
    {W : Type*} [AddCommGroup W] [Module ℚ W] [FiniteDimensional ℚ W]
    (ρ : Representation ℚ (DihedralGroup 19) W)
    (alpha beta gamma : ℕ)
    (minus8_trivial_nonneg : alpha ≤ 113)
    (minus8_sign_nonneg : beta ≤ 58)
    (trace_eq_character :
      ∀ g : DihedralGroup 19,
        Matrix.trace (E7Matrix Γ * permMatrix (h.smulEquiv g)) =
          ρ.character g)
    (character_eq_d19Linear :
      ∀ g : DihedralGroup 19,
        ρ.character g =
          (d19LinearCharacter alpha beta gamma g : ℚ))
    {d : ZMod 19}
    (ha0 : fixedVertexCount (h.smulEquiv (DihedralGroup.sr d)) = 56)
    (ha1 : adjacentMovedCount Γ (h.smulEquiv (DihedralGroup.sr d)) = 112)
    (fixedUpperBound : D19ActsOnMoore57.RotationFixedUpperBoundInput h) :
    D19FinalCharacterInputs h :=
  ofD19LinearCharacterInput
    (D19ActsOnMoore57.D19LinearCharacterInput.ofRepresentationCharacterAndCounts
      (h := h) ρ alpha beta gamma minus8_trivial_nonneg
      minus8_sign_nonneg trace_eq_character character_eq_d19Linear ha0 ha1)
    fixedUpperBound

end D19FinalCharacterInputs

namespace D19ConstructiveFinalInputs

variable {h : D19ActsOnMoore57 V Γ}

/-- Constructive final inputs from a full linear-character equality and the
standard reflection counts. -/
noncomputable def ofLinearCharacterAndCounts
    (alpha beta gamma : ℕ)
    (minus8_trivial_nonneg : alpha ≤ 113)
    (minus8_sign_nonneg : beta ≤ 58)
    (hlin : ∀ g : DihedralGroup 19,
      Matrix.trace (E7Matrix Γ * permMatrix (h.smulEquiv g)) =
        (d19LinearCharacter alpha beta gamma g : ℚ))
    {d : ZMod 19}
    (ha0 : fixedVertexCount (h.smulEquiv (DihedralGroup.sr d)) = 56)
    (ha1 : adjacentMovedCount Γ (h.smulEquiv (DihedralGroup.sr d)) = 112)
    (fixedUpperBound : D19ActsOnMoore57.RotationFixedUpperBoundInput h)
    (orbitBase : OrbitBaseSelectionEnumeration h)
    (adjacentMoved :
      AdjacentMovedTwoCopyPartition38Witness h orbitBase.base) :
    D19ConstructiveFinalInputs h where
  character :=
    D19FinalCharacterInputs.ofLinearCharacterAndCounts (h := h)
      alpha beta gamma minus8_trivial_nonneg minus8_sign_nonneg
      hlin ha0 ha1 fixedUpperBound
  orbitBase := orbitBase
  adjacentMoved := adjacentMoved

/-- Constructive final inputs from mathlib representation-character data and
the standard reflection counts. -/
noncomputable def ofRepresentationCharacterAndCounts
    {W : Type*} [AddCommGroup W] [Module ℚ W] [FiniteDimensional ℚ W]
    (ρ : Representation ℚ (DihedralGroup 19) W)
    (alpha beta gamma : ℕ)
    (minus8_trivial_nonneg : alpha ≤ 113)
    (minus8_sign_nonneg : beta ≤ 58)
    (trace_eq_character :
      ∀ g : DihedralGroup 19,
        Matrix.trace (E7Matrix Γ * permMatrix (h.smulEquiv g)) =
          ρ.character g)
    (character_eq_d19Linear :
      ∀ g : DihedralGroup 19,
        ρ.character g =
          (d19LinearCharacter alpha beta gamma g : ℚ))
    {d : ZMod 19}
    (ha0 : fixedVertexCount (h.smulEquiv (DihedralGroup.sr d)) = 56)
    (ha1 : adjacentMovedCount Γ (h.smulEquiv (DihedralGroup.sr d)) = 112)
    (fixedUpperBound : D19ActsOnMoore57.RotationFixedUpperBoundInput h)
    (orbitBase : OrbitBaseSelectionEnumeration h)
    (adjacentMoved :
      AdjacentMovedTwoCopyPartition38Witness h orbitBase.base) :
    D19ConstructiveFinalInputs h where
  character :=
    D19FinalCharacterInputs.ofRepresentationCharacterAndCounts (h := h)
      ρ alpha beta gamma minus8_trivial_nonneg minus8_sign_nonneg
      trace_eq_character character_eq_d19Linear ha0 ha1 fixedUpperBound
  orbitBase := orbitBase
  adjacentMoved := adjacentMoved

end D19ConstructiveFinalInputs

end Moore57
