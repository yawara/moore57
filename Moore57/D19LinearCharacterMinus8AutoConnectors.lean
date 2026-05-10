import Moore57.D19LinearCharacterMinus8Connectors
import Moore57.RotationFixedCountOneFrontier
import Moore57.InvolutionFixedStarA1

/-!
# Auto-rotation variants of the `(-8)` eigenspace connectors

The `(-8)` connector file was intentionally written with the exact rotation
fixed-count input explicit.  After `RotationFixedCountOneFrontier`, that input
is a theorem of the ambient `D19ActsOnMoore57` witness.  This file exposes the
same constructors with that argument filled automatically.
-/

namespace Moore57

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

namespace D19ActsOnMoore57

variable {h : D19ActsOnMoore57 V Γ}

/-- Auto-rotation form of the `(-8)` eigenspace bounds: the nontrivial
rotation fixed-count input is supplied by `rotationFixedCountOne_smulEquiv`. -/
theorem minus8_bounds_of_eigenspaceCharactersAndReflectionCount
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
      fixedVertexCount (h.smulEquiv (DihedralGroup.sr dt)) = 56) :
    alpha ≤ 113 ∧ beta ≤ 58 :=
  minus8_bounds_of_eigenspaceCharactersAndCounts (h := h)
    alpha beta gamma A B C h7 hMinus8 hreflection_a0
    (D19ActsOnMoore57.rotationFixedCountOne_smulEquiv h)

namespace D19LinearCharacterInput

/-- Build the full linear-character input from eigenspace characters and
reflection counts, with rotation counts filled automatically. -/
noncomputable def ofEigenspaceCharactersAndReflectionCounts
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
    (hreflection_a1 :
      adjacentMovedCount Γ (h.smulEquiv (DihedralGroup.sr dt)) = 112) :
    D19LinearCharacterInput h :=
  ofEigenspaceCharactersAndCounts (h := h)
    alpha beta gamma A B C h7 hMinus8 hreflection_a0
    (D19ActsOnMoore57.rotationFixedCountOne_smulEquiv h) hreflection_a1

/-- Fixed-star form of `ofEigenspaceCharactersAndReflectionCounts`. -/
noncomputable def ofEigenspaceCharactersAndFixedStar55
    (alpha beta gamma A B C : ℕ)
    (h7 : ∀ g : DihedralGroup 19,
      Matrix.trace (E7Matrix Γ * permMatrix (h.smulEquiv g)) =
        (d19LinearCharacter alpha beta gamma g : ℚ))
    (hMinus8 : ∀ g : DihedralGroup 19,
      Matrix.trace (permMatrix (h.smulEquiv g)) - 1 -
          Matrix.trace (E7Matrix Γ * permMatrix (h.smulEquiv g)) =
        (d19LinearCharacter A B C g : ℚ))
    {dt : ZMod 19}
    (hStar :
      InvolutionFixedStar55 Γ (h.smulEquiv (DihedralGroup.sr dt))) :
    D19LinearCharacterInput h :=
  ofEigenspaceCharactersAndReflectionCounts (h := h)
    alpha beta gamma A B C h7 hMinus8
    (h.fixedVertexCount_reflection_eq_56_of_involutionFixedStar55 hStar)
    (h.adjacentMovedCount_reflection_eq_112 hStar)

end D19LinearCharacterInput

namespace D19RepresentationCharacterInput

/-- Representation-character input from eigenspace characters and reflection
counts, with rotation counts filled automatically. -/
noncomputable def ofEigenspaceCharactersAndReflectionCounts
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
    (hreflection_a1 :
      adjacentMovedCount Γ (h.smulEquiv (DihedralGroup.sr dt)) = 112) :
    D19RepresentationCharacterInput h :=
  (D19LinearCharacterInput.ofEigenspaceCharactersAndReflectionCounts
    (h := h) alpha beta gamma A B C h7 hMinus8 hreflection_a0
    hreflection_a1).toD19RepresentationCharacterInput

/-- Fixed-star form of `ofEigenspaceCharactersAndReflectionCounts`. -/
noncomputable def ofEigenspaceCharactersAndFixedStar55
    (alpha beta gamma A B C : ℕ)
    (h7 : ∀ g : DihedralGroup 19,
      Matrix.trace (E7Matrix Γ * permMatrix (h.smulEquiv g)) =
        (d19LinearCharacter alpha beta gamma g : ℚ))
    (hMinus8 : ∀ g : DihedralGroup 19,
      Matrix.trace (permMatrix (h.smulEquiv g)) - 1 -
          Matrix.trace (E7Matrix Γ * permMatrix (h.smulEquiv g)) =
        (d19LinearCharacter A B C g : ℚ))
    {dt : ZMod 19}
    (hStar :
      InvolutionFixedStar55 Γ (h.smulEquiv (DihedralGroup.sr dt))) :
    D19RepresentationCharacterInput h :=
  (D19LinearCharacterInput.ofEigenspaceCharactersAndFixedStar55
    (h := h) alpha beta gamma A B C h7 hMinus8 hStar)
      |>.toD19RepresentationCharacterInput

end D19RepresentationCharacterInput

/-- Component-boundary form of the auto-rotation eigenspace connector. -/
theorem representationCharacterComponentsBoundary_of_eigenspaceCharactersAndReflectionCounts
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
    (hreflection_a1 :
      adjacentMovedCount Γ (h.smulEquiv (DihedralGroup.sr dt)) = 112) :
    RepresentationCharacterComponentsBoundary h :=
  (D19LinearCharacterInput.ofEigenspaceCharactersAndReflectionCounts
    (h := h) alpha beta gamma A B C h7 hMinus8 hreflection_a0
    hreflection_a1).representationCharacterComponentsBoundary

/-- Component-boundary fixed-star form of the auto-rotation eigenspace
connector. -/
theorem representationCharacterComponentsBoundary_of_eigenspaceCharactersAndFixedStar55
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
    (hStar :
      InvolutionFixedStar55 Γ (h.smulEquiv (DihedralGroup.sr dt))) :
    RepresentationCharacterComponentsBoundary h :=
  (D19LinearCharacterInput.ofEigenspaceCharactersAndFixedStar55
    (h := h) alpha beta gamma A B C h7 hMinus8 hStar)
      |>.representationCharacterComponentsBoundary

end D19ActsOnMoore57

namespace D19FinalCharacterInputs

variable {h : D19ActsOnMoore57 V Γ}

/-- Final character inputs from eigenspace characters and reflection counts,
with rotation fixed counts and the upper-bound package filled automatically. -/
noncomputable def ofEigenspaceCharactersAndReflectionCounts
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
    (hreflection_a1 :
      adjacentMovedCount Γ (h.smulEquiv (DihedralGroup.sr dt)) = 112) :
    D19FinalCharacterInputs h :=
  ofEigenspaceCharactersAndCounts (h := h)
    alpha beta gamma A B C h7 hMinus8 hreflection_a0
    (D19ActsOnMoore57.rotationFixedCountOne_smulEquiv h) hreflection_a1

/-- Fixed-star final character input from eigenspace characters. -/
noncomputable def ofEigenspaceCharactersAndFixedStar55
    (alpha beta gamma A B C : ℕ)
    (h7 : ∀ g : DihedralGroup 19,
      Matrix.trace (E7Matrix Γ * permMatrix (h.smulEquiv g)) =
        (d19LinearCharacter alpha beta gamma g : ℚ))
    (hMinus8 : ∀ g : DihedralGroup 19,
      Matrix.trace (permMatrix (h.smulEquiv g)) - 1 -
          Matrix.trace (E7Matrix Γ * permMatrix (h.smulEquiv g)) =
        (d19LinearCharacter A B C g : ℚ))
    {dt : ZMod 19}
    (hStar :
      InvolutionFixedStar55 Γ (h.smulEquiv (DihedralGroup.sr dt))) :
    D19FinalCharacterInputs h :=
  ofEigenspaceCharactersAndReflectionCounts (h := h)
    alpha beta gamma A B C h7 hMinus8
    (h.fixedVertexCount_reflection_eq_56_of_involutionFixedStar55 hStar)
    (h.adjacentMovedCount_reflection_eq_112 hStar)

end D19FinalCharacterInputs

namespace D19ConstructiveFinalInputs

variable {h : D19ActsOnMoore57 V Γ}

/-- Constructive final inputs from eigenspace characters and reflection counts,
with rotation fixed counts filled automatically. -/
noncomputable def ofEigenspaceCharactersAndReflectionCounts
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
    (hreflection_a1 :
      adjacentMovedCount Γ (h.smulEquiv (DihedralGroup.sr dt)) = 112)
    (orbitBase : OrbitBaseSelectionEnumeration h)
    (adjacentMoved :
      AdjacentMovedTwoCopyPartition38Witness h orbitBase.base) :
    D19ConstructiveFinalInputs h :=
  ofEigenspaceCharactersAndCounts (h := h)
    alpha beta gamma A B C h7 hMinus8 hreflection_a0
    (D19ActsOnMoore57.rotationFixedCountOne_smulEquiv h) hreflection_a1
    orbitBase adjacentMoved

/-- Fixed-star constructive final inputs from eigenspace characters. -/
noncomputable def ofEigenspaceCharactersAndFixedStar55
    (alpha beta gamma A B C : ℕ)
    (h7 : ∀ g : DihedralGroup 19,
      Matrix.trace (E7Matrix Γ * permMatrix (h.smulEquiv g)) =
        (d19LinearCharacter alpha beta gamma g : ℚ))
    (hMinus8 : ∀ g : DihedralGroup 19,
      Matrix.trace (permMatrix (h.smulEquiv g)) - 1 -
          Matrix.trace (E7Matrix Γ * permMatrix (h.smulEquiv g)) =
        (d19LinearCharacter A B C g : ℚ))
    {dt : ZMod 19}
    (hStar :
      InvolutionFixedStar55 Γ (h.smulEquiv (DihedralGroup.sr dt)))
    (orbitBase : OrbitBaseSelectionEnumeration h)
    (adjacentMoved :
      AdjacentMovedTwoCopyPartition38Witness h orbitBase.base) :
    D19ConstructiveFinalInputs h :=
  ofEigenspaceCharactersAndReflectionCounts (h := h)
    alpha beta gamma A B C h7 hMinus8
    (h.fixedVertexCount_reflection_eq_56_of_involutionFixedStar55 hStar)
    (h.adjacentMovedCount_reflection_eq_112 hStar)
    orbitBase adjacentMoved

end D19ConstructiveFinalInputs

end

end Moore57
