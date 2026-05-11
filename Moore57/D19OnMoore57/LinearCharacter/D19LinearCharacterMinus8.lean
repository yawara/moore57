import Moore57.D19OnMoore57.LinearCharacter.D19LinearCharacterDimension

/-!
# `(-8)`-eigenspace bounds from the linear-character data

The natural-language proof derives `α ≤ 113` and `β ≤ 58` from the fact that
the `(-8)`-eigenspace is a representation, hence its character is a non-negative
integer combination of the three rational irreducibles `1, ε, ρ`.

This file packages the conversion: given the `7`-eigenspace and `(-8)`-eigenspace
class characters together with the standard reflection and rotation counts, the
bounds follow as theorems.

The eigenspace identity `E_{-8}=I-E_{57}-E_7` produces the formal relation
`trace(E_{-8}·P_g) = a₀(g) - 1 - trace(E₇·P_g)`.  We take the `(-8)` character
hypothesis in this form so we never need to define `E_{-8}` explicitly.
-/

namespace Moore57

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- Uniqueness of the `α·1 + β·ε + γ·ρ` decomposition: equality of the linear
combination as a class function on `D₁₉` forces equality of all three
multiplicities. -/
theorem d19LinearCharacter_inj
    {a b c a' b' c' : ℕ}
    (h : ∀ g : DihedralGroup 19,
      d19LinearCharacter a b c g = d19LinearCharacter a' b' c' g) :
    a = a' ∧ b = b' ∧ c = c' := by
  have h1 := h 1
  rw [d19LinearCharacter_one, d19LinearCharacter_one] at h1
  have h2 := h (DihedralGroup.sr 0)
  rw [d19LinearCharacter_reflection, d19LinearCharacter_reflection] at h2
  have h1ne : (1 : ZMod 19) ≠ 0 := by decide
  have h3 := h (DihedralGroup.r 1)
  rw [d19LinearCharacter_rotation_ne _ _ _ h1ne,
      d19LinearCharacter_rotation_ne _ _ _ h1ne] at h3
  refine ⟨?_, ?_, ?_⟩ <;> omega

namespace D19ActsOnMoore57

variable {h : D19ActsOnMoore57 V Γ}

/-- Combining the `7`-eigenspace and `(-8)`-eigenspace class characters with the
standard involution / rotation fixed-vertex counts gives the explicit
sum-of-multiplicities identities

  α + A = 113,  β + B = 58,  γ + C = 171.

The linear system follows from evaluating the character identities at the
identity, a reflection with `a₀(t)=56`, and a non-trivial rotation
with `a₀(rᵈ)=1`. -/
theorem alpha_plus_minus8_eq_of_eigenspace_characters
    (α β γ A B C : ℕ)
    (h7 : ∀ g : DihedralGroup 19,
      Matrix.trace (E7Matrix Γ * permMatrix (h.smulEquiv g)) =
        (d19LinearCharacter α β γ g : ℚ))
    (hMinus8 : ∀ g : DihedralGroup 19,
      Matrix.trace (permMatrix (h.smulEquiv g)) - 1 -
          Matrix.trace (E7Matrix Γ * permMatrix (h.smulEquiv g)) =
        (d19LinearCharacter A B C g : ℚ))
    {dt : ZMod 19}
    (hreflection_a0 :
      fixedVertexCount (h.smulEquiv (DihedralGroup.sr dt)) = 56)
    (hrotation_a0 :
      ∀ d : ZMod 19, d ≠ 0 →
        fixedVertexCount (h.smulEquiv (DihedralGroup.r d)) = 1) :
    α + A = 113 ∧ β + B = 58 ∧ γ + C = 171 := by
  -- Identity: a₀ = card V = 3250.
  have e1 := hMinus8 1
  rw [h.smulEquiv_one] at e1
  rw [trace_permMatrix_eq_fixedVertexCount, fixedVertexCount_one,
      h.isMoore.card] at e1
  have e1' := h7 1
  rw [h.smulEquiv_one] at e1'
  rw [e1'] at e1
  simp only [d19LinearCharacter_one] at e1
  -- Reflection: a₀ = 56.
  have e2 := hMinus8 (DihedralGroup.sr dt)
  rw [trace_permMatrix_eq_fixedVertexCount, hreflection_a0] at e2
  have e2' := h7 (DihedralGroup.sr dt)
  rw [e2'] at e2
  simp only [d19LinearCharacter_reflection] at e2
  -- Rotation at d = 1.
  have h1ne : (1 : ZMod 19) ≠ 0 := by decide
  have e3 := hMinus8 (DihedralGroup.r 1)
  rw [trace_permMatrix_eq_fixedVertexCount, hrotation_a0 1 h1ne] at e3
  have e3' := h7 (DihedralGroup.r 1)
  rw [e3'] at e3
  simp only [d19LinearCharacter_rotation_ne _ _ _ h1ne] at e3
  -- Normalize casts for linarith.
  push_cast at e1 e2 e3
  ring_nf at e1 e2 e3
  -- Convert each rational equation back to ℤ for omega.
  have e1z : ((α : ℤ) + β + 18 * γ + A + B + 18 * C : ℤ) = 3249 := by
    have hcast :
        (((α : ℤ) + β + 18 * γ + A + B + 18 * C : ℤ) : ℚ) = (3249 : ℚ) := by
      push_cast
      linarith
    exact_mod_cast hcast
  have e2z : ((α : ℤ) - β + (A - B) : ℤ) = 55 := by
    have hcast : (((α : ℤ) - β + (A - B) : ℤ) : ℚ) = (55 : ℚ) := by
      push_cast
      linarith
    exact_mod_cast hcast
  have e3z : ((α : ℤ) + β - γ + (A + B - C) : ℤ) = 0 := by
    have hcast : (((α : ℤ) + β - γ + (A + B - C) : ℤ) : ℚ) = (0 : ℚ) := by
      push_cast
      linarith
    exact_mod_cast hcast
  refine ⟨?_, ?_, ?_⟩ <;> omega

/-- The `(-8)`-eigenspace decomposition forces `α ≤ 113`, `β ≤ 58`, and
`γ ≤ 171`. -/
theorem alpha_beta_gamma_le_of_eigenspace_characters
    (α β γ A B C : ℕ)
    (h7 : ∀ g : DihedralGroup 19,
      Matrix.trace (E7Matrix Γ * permMatrix (h.smulEquiv g)) =
        (d19LinearCharacter α β γ g : ℚ))
    (hMinus8 : ∀ g : DihedralGroup 19,
      Matrix.trace (permMatrix (h.smulEquiv g)) - 1 -
          Matrix.trace (E7Matrix Γ * permMatrix (h.smulEquiv g)) =
        (d19LinearCharacter A B C g : ℚ))
    {dt : ZMod 19}
    (hreflection_a0 :
      fixedVertexCount (h.smulEquiv (DihedralGroup.sr dt)) = 56)
    (hrotation_a0 :
      ∀ d : ZMod 19, d ≠ 0 →
        fixedVertexCount (h.smulEquiv (DihedralGroup.r d)) = 1) :
    α ≤ 113 ∧ β ≤ 58 ∧ γ ≤ 171 := by
  obtain ⟨hα, hβ, hγ⟩ :=
    alpha_plus_minus8_eq_of_eigenspace_characters
      α β γ A B C h7 hMinus8 hreflection_a0 hrotation_a0
  exact ⟨by omega, by omega, by omega⟩

end D19ActsOnMoore57

end Moore57
