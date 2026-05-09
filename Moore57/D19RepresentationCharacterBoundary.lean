import Moore57.CharacterInputPackaging

/-!
# Boundary form of D19 representation-character input

This file exposes `D19RepresentationCharacterInput` as exactly the existence
of trace multiplicity data satisfying the nontrivial-rotation character
identity.
-/

namespace Moore57

namespace D19ActsOnMoore57

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

namespace D19RepresentationCharacterInput

variable {h : D19ActsOnMoore57 V Γ}

/-- Build the representation-character input from its boundary data. -/
def ofTraceMultiplicityData
    (multiplicity : TraceMultiplicityData)
    (rotation_character :
      ∀ d : ZMod 19, d ≠ 0 →
        Matrix.trace (E7Matrix Γ * permMatrix (h.rotation d)) =
          (multiplicity.alpha : ℚ) + (multiplicity.beta : ℚ) -
            (multiplicity.gamma : ℚ)) :
    D19RepresentationCharacterInput h where
  multiplicity := multiplicity
  rotation_character := rotation_character

@[simp] theorem ofTraceMultiplicityData_multiplicity
    (multiplicity : TraceMultiplicityData)
    (rotation_character :
      ∀ d : ZMod 19, d ≠ 0 →
        Matrix.trace (E7Matrix Γ * permMatrix (h.rotation d)) =
          (multiplicity.alpha : ℚ) + (multiplicity.beta : ℚ) -
            (multiplicity.gamma : ℚ)) :
    (ofTraceMultiplicityData (h := h) multiplicity rotation_character).multiplicity =
      multiplicity :=
  rfl

@[simp] theorem ofTraceMultiplicityData_rotation_character
    (multiplicity : TraceMultiplicityData)
    (rotation_character :
      ∀ d : ZMod 19, d ≠ 0 →
        Matrix.trace (E7Matrix Γ * permMatrix (h.rotation d)) =
          (multiplicity.alpha : ℚ) + (multiplicity.beta : ℚ) -
            (multiplicity.gamma : ℚ)) :
    (ofTraceMultiplicityData (h := h) multiplicity rotation_character).rotation_character =
      rotation_character :=
  rfl

/-- Boundary characterization of representation-character input existence. -/
theorem nonempty_iff_exists_traceMultiplicityData
    (h : D19ActsOnMoore57 V Γ) :
    Nonempty (D19RepresentationCharacterInput h) ↔
      ∃ multiplicity : TraceMultiplicityData,
        ∀ d : ZMod 19, d ≠ 0 →
          Matrix.trace (E7Matrix Γ * permMatrix (h.rotation d)) =
            (multiplicity.alpha : ℚ) + (multiplicity.beta : ℚ) -
              (multiplicity.gamma : ℚ) := by
  constructor
  · rintro ⟨input⟩
    exact ⟨input.multiplicity, input.rotation_character⟩
  · rintro ⟨multiplicity, rotation_character⟩
    exact ⟨ofTraceMultiplicityData (h := h) multiplicity rotation_character⟩

/-- Existential-first alias for the boundary characterization. -/
theorem exists_traceMultiplicityData_iff_nonempty
    (h : D19ActsOnMoore57 V Γ) :
    (∃ multiplicity : TraceMultiplicityData,
        ∀ d : ZMod 19, d ≠ 0 →
          Matrix.trace (E7Matrix Γ * permMatrix (h.rotation d)) =
            (multiplicity.alpha : ℚ) + (multiplicity.beta : ℚ) -
              (multiplicity.gamma : ℚ)) ↔
      Nonempty (D19RepresentationCharacterInput h) :=
  (nonempty_iff_exists_traceMultiplicityData h).symm

end D19RepresentationCharacterInput

end D19ActsOnMoore57

end Moore57
