import Moore57.D19OnMoore57.LinearCharacter.Input
import Moore57.D19OnMoore57.D19Core.RepresentationCharacterDataBridge
import Mathlib.RepresentationTheory.Character

/-!
# Mathlib representation-character bridge

This file exposes a small mathlib-facing entrypoint for the existing
representation-character boundary.  Proving a `Representation.character`
identity now suffices to build the component boundary consumed by the final
D19 pipeline.
-/

namespace Moore57

namespace D19ActsOnMoore57

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

namespace D19LinearCharacterInput

variable {h : D19ActsOnMoore57 V Γ}

/-- A full linear-character witness supplies the exposed representation
component boundary. -/
theorem representationCharacterComponentsBoundary
    (hin : D19LinearCharacterInput h) :
    RepresentationCharacterComponentsBoundary h :=
  (D19RepresentationCharacterInput.nonempty_iff_componentsBoundary h).mp
    ⟨hin.toD19RepresentationCharacterInput⟩

end D19LinearCharacterInput

/-- Direct mathlib-character constructor for the exposed component boundary. -/
theorem representationCharacterComponentsBoundary_of_representationCharacter
    (h : D19ActsOnMoore57 V Γ)
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
    RepresentationCharacterComponentsBoundary h :=
  (D19LinearCharacterInput.ofRepresentationCharacter (h := h)
      ρ multiplicity trace_eq_character character_eq_d19Linear)
    |>.representationCharacterComponentsBoundary

end D19ActsOnMoore57

end Moore57
