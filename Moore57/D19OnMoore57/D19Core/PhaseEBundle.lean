import Moore57.D19OnMoore57.LinearCharacter.Minus8
import Moore57.D19OnMoore57.Involution.FixedStarA1

/-!
# Bundled Phase E character input from natural representation data

A single constructor that takes the natural representation-side inputs

* `V_7` class character `α·1 + β·ε + γ·ρ`,
* `V_{-8}` class character `A·1 + B·ε + C·ρ` (in the trace shape
  `a₀(g) − 1 − χ_7(g)`),
* a `K_{1,55}` fixed-star witness for one reflection, and
* the standard rotation fixed-vertex count `a₀(rᵈ) = 1`,

and produces the existing `D19FinalCharacterInputs` boundary, with all of
the `TraceMultiplicityData` arithmetic constraints filled in
automatically by the Phase E lemmas.
-/

namespace Moore57

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

namespace D19FinalCharacterInputs

variable {h : D19ActsOnMoore57 V Γ}

/-- Bundled Phase E construction.  See module docstring. -/
noncomputable def ofEigenspaceCharactersAndStar
    (alpha7 beta7 gamma7 alphaMinus8 betaMinus8 gammaMinus8 : ℕ)
    (h7 : ∀ g : DihedralGroup 19,
      Matrix.trace (E7Matrix Γ * permMatrix (h.smulEquiv g)) =
        (d19LinearCharacter alpha7 beta7 gamma7 g : ℚ))
    (hMinus8 : ∀ g : DihedralGroup 19,
      Matrix.trace (permMatrix (h.smulEquiv g)) - 1 -
          Matrix.trace (E7Matrix Γ * permMatrix (h.smulEquiv g)) =
        (d19LinearCharacter alphaMinus8 betaMinus8 gammaMinus8 g : ℚ))
    {dt : ZMod 19}
    (hStar :
      InvolutionFixedStar55 Γ (h.smulEquiv (DihedralGroup.sr dt)))
    (hrotation_a0 :
      ∀ d : ZMod 19, d ≠ 0 →
        fixedVertexCount (h.smulEquiv (DihedralGroup.r d)) = 1)
    (fixedUpperBound : D19ActsOnMoore57.RotationFixedUpperBoundInput h) :
    D19FinalCharacterInputs h :=
  let hbounds :=
    D19ActsOnMoore57.alpha_beta_gamma_le_of_eigenspace_characters
      alpha7 beta7 gamma7 alphaMinus8 betaMinus8 gammaMinus8
      h7 hMinus8
      (h.fixedVertexCount_reflection_eq_56_of_involutionFixedStar55 hStar)
      hrotation_a0
  let hin :=
    D19ActsOnMoore57.D19LinearCharacterInput.ofLinearCharacterAndFixedStar55
      alpha7 beta7 gamma7 hbounds.1 hbounds.2.1 h7 hStar
  D19FinalCharacterInputs.ofD19LinearCharacterInput hin fixedUpperBound

end D19FinalCharacterInputs

end Moore57
