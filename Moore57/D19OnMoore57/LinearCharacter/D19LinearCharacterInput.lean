import Moore57.D19OnMoore57.Misc.CharacterInputPackaging
import Mathlib.RepresentationTheory.Character
import Moore57.D19OnMoore57.Action.D19Action
import Moore57.Foundations.GroupTheory.Dihedral19LinearCharacter

/-!
# Linear-character criteria for D19 representation inputs

This file records a natural class-function style input for the D19 action:
the trace of the `E7Matrix` permutation operator agrees with the linear
character `alpha * 1 + beta * epsilon + gamma * rho` on every group element.
For the current D19 pipeline, this full character equality is then restricted
to nontrivial rotations and reduced with `d19LinearCharacter_rotation_ne`.
-/

namespace Moore57

namespace D19ActsOnMoore57

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- A full D19 linear-character witness for the trace representation.

The current contradiction pipeline only consumes the value on nontrivial
rotations, but this record allows that input to be supplied as the more natural
class-character equality on all of `D19`. -/
structure D19LinearCharacterInput (h : D19ActsOnMoore57 V Γ) where
  /-- Multiplicities of the three rational character pieces. -/
  multiplicity : TraceMultiplicityData
  /-- The full class-character equality for the trace representation. -/
  linear_character :
    ∀ g : DihedralGroup 19,
      Matrix.trace (E7Matrix Γ * permMatrix (h.smulEquiv g)) =
        (d19LinearCharacter multiplicity.alpha multiplicity.beta multiplicity.gamma g : ℚ)

namespace D19LinearCharacterInput

variable {h : D19ActsOnMoore57 V Γ}

/-- Build the full D19 linear-character witness from a mathlib
`Representation.character`.  The two hypotheses isolate the graph trace
identification and the D19-specific character decomposition. -/
noncomputable def ofRepresentationCharacter
    {W : Type*} [AddCommGroup W] [Module ℚ W] [FiniteDimensional ℚ W]
    (ρ : Representation ℚ (DihedralGroup 19) W)
    (multiplicity : TraceMultiplicityData)
    (trace_eq_character :
      ∀ g : DihedralGroup 19,
        Matrix.trace (E7Matrix Γ * permMatrix (h.smulEquiv g)) =
          ρ.character g)
    (character_eq_d19Linear :
      ∀ g : DihedralGroup 19,
        ρ.character g =
          (d19LinearCharacter multiplicity.alpha multiplicity.beta
            multiplicity.gamma g : ℚ)) :
    D19LinearCharacterInput h where
  multiplicity := multiplicity
  linear_character := by
    intro g
    exact (trace_eq_character g).trans (character_eq_d19Linear g)

@[simp] theorem ofRepresentationCharacter_multiplicity
    {W : Type*} [AddCommGroup W] [Module ℚ W] [FiniteDimensional ℚ W]
    (ρ : Representation ℚ (DihedralGroup 19) W)
    (multiplicity : TraceMultiplicityData)
    (trace_eq_character :
      ∀ g : DihedralGroup 19,
        Matrix.trace (E7Matrix Γ * permMatrix (h.smulEquiv g)) =
          ρ.character g)
    (character_eq_d19Linear :
      ∀ g : DihedralGroup 19,
        ρ.character g =
          (d19LinearCharacter multiplicity.alpha multiplicity.beta
            multiplicity.gamma g : ℚ)) :
    (ofRepresentationCharacter (h := h) ρ multiplicity
        trace_eq_character character_eq_d19Linear).multiplicity =
      multiplicity :=
  rfl

/-- Restrict the full linear-character witness to a rotation. -/
theorem rotation_linear_character
    (hin : D19LinearCharacterInput h) (d : ZMod 19) :
    Matrix.trace (E7Matrix Γ * permMatrix (h.rotation d)) =
      (d19LinearCharacter hin.multiplicity.alpha hin.multiplicity.beta
        hin.multiplicity.gamma (DihedralGroup.r d) : ℚ) := by
  simpa [D19ActsOnMoore57.rotation] using
    hin.linear_character (DihedralGroup.r d)

/-- A nontrivial rotation has character value `alpha + beta - gamma`. -/
theorem rotation_character_eq_of_linearCharacter
    (hin : D19LinearCharacterInput h) (d : ZMod 19) (hd : d ≠ 0) :
    Matrix.trace (E7Matrix Γ * permMatrix (h.rotation d)) =
      (hin.multiplicity.alpha : ℚ) + (hin.multiplicity.beta : ℚ) -
        (hin.multiplicity.gamma : ℚ) := by
  calc
    Matrix.trace (E7Matrix Γ * permMatrix (h.rotation d))
        =
          (d19LinearCharacter hin.multiplicity.alpha hin.multiplicity.beta
            hin.multiplicity.gamma (DihedralGroup.r d) : ℚ) :=
      hin.rotation_linear_character d
    _ =
        (hin.multiplicity.alpha : ℚ) + (hin.multiplicity.beta : ℚ) -
          (hin.multiplicity.gamma : ℚ) := by
      rw [d19LinearCharacter_rotation_ne hin.multiplicity.alpha
        hin.multiplicity.beta hin.multiplicity.gamma hd]
      norm_num

/-- Forget the full D19 class-character equality down to the representation
input consumed by the reduced D19 pipeline. -/
def toD19RepresentationCharacterInput
    (hin : D19LinearCharacterInput h) :
    D19RepresentationCharacterInput h where
  multiplicity := hin.multiplicity
  rotation_character := hin.rotation_character_eq_of_linearCharacter

@[simp] theorem toD19RepresentationCharacterInput_multiplicity
    (hin : D19LinearCharacterInput h) :
    hin.toD19RepresentationCharacterInput.multiplicity = hin.multiplicity :=
  rfl

@[simp] theorem toD19RepresentationCharacterInput_rotation_character
    (hin : D19LinearCharacterInput h) :
    hin.toD19RepresentationCharacterInput.rotation_character =
      hin.rotation_character_eq_of_linearCharacter :=
  rfl

end D19LinearCharacterInput

end D19ActsOnMoore57

end Moore57
