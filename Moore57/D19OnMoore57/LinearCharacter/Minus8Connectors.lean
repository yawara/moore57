import Moore57.D19OnMoore57.LinearCharacter.Minus8
import Moore57.D19OnMoore57.LinearCharacter.Dimension

/-!
# Connectors from the `(-8)`-eigenspace character bounds

This file combines the `7`-eigenspace and `(-8)`-eigenspace character
identities with the standard fixed-count data, then delegates to the existing
linear-character dimension connectors.
-/

namespace Moore57

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

namespace D19ActsOnMoore57

variable {h : D19ActsOnMoore57 V Γ}

/-- The `(-8)`-eigenspace character identity supplies the two non-negativity
bounds needed by the linear-character dimension connector. -/
theorem minus8_bounds_of_eigenspaceCharactersAndCounts
    (alpha beta gamma A B C : ℕ)
    (h7 : ∀ g : DihedralGroup 19,
      Matrix.trace (E7Matrix Γ * permMatrix (h.smulEquiv g)) =
        (d19LinearCharacter alpha beta gamma g : ℚ))
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
    alpha ≤ 113 ∧ beta ≤ 58 := by
  obtain ⟨hAlpha, hBeta, _hGamma⟩ :=
    alpha_beta_gamma_le_of_eigenspace_characters
      alpha beta gamma A B C h7 hMinus8 hreflection_a0 hrotation_a0
  exact ⟨hAlpha, hBeta⟩

namespace D19LinearCharacterInput

/-- Build the full linear-character input from the `7`-eigenspace character,
the `(-8)`-eigenspace character, and the standard reflection/rotation counts.
-/
noncomputable def ofEigenspaceCharactersAndCounts
    (alpha beta gamma A B C : ℕ)
    (h7 : ∀ g : DihedralGroup 19,
      Matrix.trace (E7Matrix Γ * permMatrix (h.smulEquiv g)) =
        (d19LinearCharacter alpha beta gamma g : ℚ))
    (hMinus8 : ∀ g : DihedralGroup 19,
      Matrix.trace (permMatrix (h.smulEquiv g)) - 1 -
          Matrix.trace (E7Matrix Γ * permMatrix (h.smulEquiv g)) =
        (d19LinearCharacter A B C g : ℚ))
    {dt : ZMod 19}
    (hreflection_a0 :
      fixedVertexCount (h.smulEquiv (DihedralGroup.sr dt)) = 56)
    (hrotation_a0 :
      ∀ d : ZMod 19, d ≠ 0 →
        fixedVertexCount (h.smulEquiv (DihedralGroup.r d)) = 1)
    (hreflection_a1 :
      adjacentMovedCount Γ (h.smulEquiv (DihedralGroup.sr dt)) = 112) :
    D19LinearCharacterInput h := by
  obtain ⟨hAlpha, hBeta⟩ :=
    minus8_bounds_of_eigenspaceCharactersAndCounts (h := h)
      alpha beta gamma A B C h7 hMinus8 hreflection_a0 hrotation_a0
  exact ofLinearCharacterAndCounts (h := h)
    alpha beta gamma hAlpha hBeta h7 hreflection_a0 hreflection_a1

end D19LinearCharacterInput

namespace D19RepresentationCharacterInput

/-- Forget the minus-8/eigenspace connector to the representation-character
input consumed by the D19 pipeline. -/
noncomputable def ofEigenspaceCharactersAndCounts
    (alpha beta gamma A B C : ℕ)
    (h7 : ∀ g : DihedralGroup 19,
      Matrix.trace (E7Matrix Γ * permMatrix (h.smulEquiv g)) =
        (d19LinearCharacter alpha beta gamma g : ℚ))
    (hMinus8 : ∀ g : DihedralGroup 19,
      Matrix.trace (permMatrix (h.smulEquiv g)) - 1 -
          Matrix.trace (E7Matrix Γ * permMatrix (h.smulEquiv g)) =
        (d19LinearCharacter A B C g : ℚ))
    {dt : ZMod 19}
    (hreflection_a0 :
      fixedVertexCount (h.smulEquiv (DihedralGroup.sr dt)) = 56)
    (hrotation_a0 :
      ∀ d : ZMod 19, d ≠ 0 →
        fixedVertexCount (h.smulEquiv (DihedralGroup.r d)) = 1)
    (hreflection_a1 :
      adjacentMovedCount Γ (h.smulEquiv (DihedralGroup.sr dt)) = 112) :
    D19RepresentationCharacterInput h :=
  (D19LinearCharacterInput.ofEigenspaceCharactersAndCounts (h := h)
    alpha beta gamma A B C h7 hMinus8 hreflection_a0 hrotation_a0
    hreflection_a1).toD19RepresentationCharacterInput

end D19RepresentationCharacterInput

/-- Exposed component-boundary form of
`D19LinearCharacterInput.ofEigenspaceCharactersAndCounts`. -/
theorem representationCharacterComponentsBoundary_of_eigenspaceCharactersAndCounts
    (h : D19ActsOnMoore57 V Γ)
    (alpha beta gamma A B C : ℕ)
    (h7 : ∀ g : DihedralGroup 19,
      Matrix.trace (E7Matrix Γ * permMatrix (h.smulEquiv g)) =
        (d19LinearCharacter alpha beta gamma g : ℚ))
    (hMinus8 : ∀ g : DihedralGroup 19,
      Matrix.trace (permMatrix (h.smulEquiv g)) - 1 -
          Matrix.trace (E7Matrix Γ * permMatrix (h.smulEquiv g)) =
        (d19LinearCharacter A B C g : ℚ))
    {dt : ZMod 19}
    (hreflection_a0 :
      fixedVertexCount (h.smulEquiv (DihedralGroup.sr dt)) = 56)
    (hrotation_a0 :
      ∀ d : ZMod 19, d ≠ 0 →
        fixedVertexCount (h.smulEquiv (DihedralGroup.r d)) = 1)
    (hreflection_a1 :
      adjacentMovedCount Γ (h.smulEquiv (DihedralGroup.sr dt)) = 112) :
    RepresentationCharacterComponentsBoundary h :=
  (D19LinearCharacterInput.ofEigenspaceCharactersAndCounts (h := h)
    alpha beta gamma A B C h7 hMinus8 hreflection_a0 hrotation_a0
    hreflection_a1).representationCharacterComponentsBoundary

namespace RotationFixedUpperBoundInput

/-- Exact fixed-count `a₀(rᵈ)=1` for nontrivial rotations gives the coarse
rotation fixed-count upper bound required by final character inputs. -/
def of_rotationFixedCountOne
    (hrotation_a0 :
      ∀ d : ZMod 19, d ≠ 0 →
        fixedVertexCount (h.smulEquiv (DihedralGroup.r d)) = 1) :
    RotationFixedUpperBoundInput h where
  fixed_le_nineteen := by
    intro d hd
    rw [D19ActsOnMoore57.rotation, hrotation_a0 d hd]
    norm_num

end RotationFixedUpperBoundInput

end D19ActsOnMoore57

namespace D19FinalCharacterInputs

variable {h : D19ActsOnMoore57 V Γ}

/-- Build final character inputs from the eigenspace character identities and
the standard reflection/rotation counts. -/
noncomputable def ofEigenspaceCharactersAndCounts
    (alpha beta gamma A B C : ℕ)
    (h7 : ∀ g : DihedralGroup 19,
      Matrix.trace (E7Matrix Γ * permMatrix (h.smulEquiv g)) =
        (d19LinearCharacter alpha beta gamma g : ℚ))
    (hMinus8 : ∀ g : DihedralGroup 19,
      Matrix.trace (permMatrix (h.smulEquiv g)) - 1 -
          Matrix.trace (E7Matrix Γ * permMatrix (h.smulEquiv g)) =
        (d19LinearCharacter A B C g : ℚ))
    {dt : ZMod 19}
    (hreflection_a0 :
      fixedVertexCount (h.smulEquiv (DihedralGroup.sr dt)) = 56)
    (hrotation_a0 :
      ∀ d : ZMod 19, d ≠ 0 →
        fixedVertexCount (h.smulEquiv (DihedralGroup.r d)) = 1)
    (hreflection_a1 :
      adjacentMovedCount Γ (h.smulEquiv (DihedralGroup.sr dt)) = 112) :
    D19FinalCharacterInputs h := by
  obtain ⟨hAlpha, hBeta⟩ :=
    D19ActsOnMoore57.minus8_bounds_of_eigenspaceCharactersAndCounts
      (h := h) alpha beta gamma A B C h7 hMinus8 hreflection_a0
      hrotation_a0
  exact ofLinearCharacterAndCounts (h := h)
    alpha beta gamma hAlpha hBeta h7 hreflection_a0 hreflection_a1
    (D19ActsOnMoore57.RotationFixedUpperBoundInput.of_rotationFixedCountOne
      (h := h) hrotation_a0)

end D19FinalCharacterInputs

namespace D19ConstructiveFinalInputs

variable {h : D19ActsOnMoore57 V Γ}

/-- Constructive final inputs from eigenspace character identities, the
standard reflection/rotation counts, and the remaining constructive geometry
witnesses. -/
noncomputable def ofEigenspaceCharactersAndCounts
    (alpha beta gamma A B C : ℕ)
    (h7 : ∀ g : DihedralGroup 19,
      Matrix.trace (E7Matrix Γ * permMatrix (h.smulEquiv g)) =
        (d19LinearCharacter alpha beta gamma g : ℚ))
    (hMinus8 : ∀ g : DihedralGroup 19,
      Matrix.trace (permMatrix (h.smulEquiv g)) - 1 -
          Matrix.trace (E7Matrix Γ * permMatrix (h.smulEquiv g)) =
        (d19LinearCharacter A B C g : ℚ))
    {dt : ZMod 19}
    (hreflection_a0 :
      fixedVertexCount (h.smulEquiv (DihedralGroup.sr dt)) = 56)
    (hrotation_a0 :
      ∀ d : ZMod 19, d ≠ 0 →
        fixedVertexCount (h.smulEquiv (DihedralGroup.r d)) = 1)
    (hreflection_a1 :
      adjacentMovedCount Γ (h.smulEquiv (DihedralGroup.sr dt)) = 112)
    (orbitBase : OrbitBaseSelectionEnumeration h)
    (adjacentMoved :
      AdjacentMovedTwoCopyPartition38Witness h orbitBase.base) :
    D19ConstructiveFinalInputs h := by
  obtain ⟨hAlpha, hBeta⟩ :=
    D19ActsOnMoore57.minus8_bounds_of_eigenspaceCharactersAndCounts
      (h := h) alpha beta gamma A B C h7 hMinus8 hreflection_a0
      hrotation_a0
  exact ofLinearCharacterAndCounts (h := h)
    alpha beta gamma hAlpha hBeta h7 hreflection_a0 hreflection_a1
    (D19ActsOnMoore57.RotationFixedUpperBoundInput.of_rotationFixedCountOne
      (h := h) hrotation_a0)
    orbitBase adjacentMoved

end D19ConstructiveFinalInputs

end

end Moore57
