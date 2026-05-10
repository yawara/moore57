import Moore57.D19LinearCharacterMinus8AutoConnectors

/-!
# `K_{1,55}` variants of the auto `(-8)` eigenspace connectors

This file keeps the representation-theoretic work delegated to
`D19LinearCharacterMinus8AutoConnectors`.  The only extra step is replacing an
explicit `InvolutionK155` witness by the existing `InvolutionFixedStar55`
abstraction.
-/

namespace Moore57

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

namespace D19ActsOnMoore57

variable {h : D19ActsOnMoore57 V Γ}

namespace D19LinearCharacterInput

/-- Build the full linear-character input from eigenspace characters and an
explicit `K_{1,55}` fixed-star witness for a reflection. -/
noncomputable def ofEigenspaceCharactersAndInvolutionK155
    (alpha beta gamma A B C : ℕ)
    (h7 : ∀ g : DihedralGroup 19,
      Matrix.trace (E7Matrix Γ * permMatrix (h.smulEquiv g)) =
        (d19LinearCharacter alpha beta gamma g : ℚ))
    (hMinus8 : ∀ g : DihedralGroup 19,
      Matrix.trace (permMatrix (h.smulEquiv g)) - 1 -
          Matrix.trace (E7Matrix Γ * permMatrix (h.smulEquiv g)) =
        (d19LinearCharacter A B C g : ℚ))
    {dt : ZMod 19}
    (hK : InvolutionK155 Γ (h.smulEquiv (DihedralGroup.sr dt))) :
    D19LinearCharacterInput h :=
  ofEigenspaceCharactersAndFixedStar55 (h := h)
    alpha beta gamma A B C h7 hMinus8
    (InvolutionK155.toInvolutionFixedStar55 h.isMoore hK)

end D19LinearCharacterInput

namespace D19RepresentationCharacterInput

/-- Representation-character input from eigenspace characters and an explicit
`K_{1,55}` fixed-star witness for a reflection. -/
noncomputable def ofEigenspaceCharactersAndInvolutionK155
    (alpha beta gamma A B C : ℕ)
    (h7 : ∀ g : DihedralGroup 19,
      Matrix.trace (E7Matrix Γ * permMatrix (h.smulEquiv g)) =
        (d19LinearCharacter alpha beta gamma g : ℚ))
    (hMinus8 : ∀ g : DihedralGroup 19,
      Matrix.trace (permMatrix (h.smulEquiv g)) - 1 -
          Matrix.trace (E7Matrix Γ * permMatrix (h.smulEquiv g)) =
        (d19LinearCharacter A B C g : ℚ))
    {dt : ZMod 19}
    (hK : InvolutionK155 Γ (h.smulEquiv (DihedralGroup.sr dt))) :
    D19RepresentationCharacterInput h :=
  (D19LinearCharacterInput.ofEigenspaceCharactersAndInvolutionK155
    (h := h) alpha beta gamma A B C h7 hMinus8 hK)
      |>.toD19RepresentationCharacterInput

end D19RepresentationCharacterInput

/-- Component-boundary form of the `K_{1,55}` eigenspace connector. -/
theorem representationCharacterComponentsBoundary_of_eigenspaceCharactersAndInvolutionK155
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
    (hK : InvolutionK155 Γ (h.smulEquiv (DihedralGroup.sr dt))) :
    RepresentationCharacterComponentsBoundary h :=
  (D19LinearCharacterInput.ofEigenspaceCharactersAndInvolutionK155
    (h := h) alpha beta gamma A B C h7 hMinus8 hK)
      |>.representationCharacterComponentsBoundary

end D19ActsOnMoore57

namespace D19FinalCharacterInputs

variable {h : D19ActsOnMoore57 V Γ}

/-- Final character inputs from eigenspace characters and an explicit
`K_{1,55}` fixed-star witness for a reflection. -/
noncomputable def ofEigenspaceCharactersAndInvolutionK155
    (alpha beta gamma A B C : ℕ)
    (h7 : ∀ g : DihedralGroup 19,
      Matrix.trace (E7Matrix Γ * permMatrix (h.smulEquiv g)) =
        (d19LinearCharacter alpha beta gamma g : ℚ))
    (hMinus8 : ∀ g : DihedralGroup 19,
      Matrix.trace (permMatrix (h.smulEquiv g)) - 1 -
          Matrix.trace (E7Matrix Γ * permMatrix (h.smulEquiv g)) =
        (d19LinearCharacter A B C g : ℚ))
    {dt : ZMod 19}
    (hK : InvolutionK155 Γ (h.smulEquiv (DihedralGroup.sr dt))) :
    D19FinalCharacterInputs h :=
  ofEigenspaceCharactersAndFixedStar55 (h := h)
    alpha beta gamma A B C h7 hMinus8
    (InvolutionK155.toInvolutionFixedStar55 h.isMoore hK)

end D19FinalCharacterInputs

namespace D19ConstructiveFinalInputs

variable {h : D19ActsOnMoore57 V Γ}

/-- Constructive final inputs from eigenspace characters, an explicit
`K_{1,55}` fixed-star witness for a reflection, and the remaining constructive
geometry witnesses. -/
noncomputable def ofEigenspaceCharactersAndInvolutionK155
    (alpha beta gamma A B C : ℕ)
    (h7 : ∀ g : DihedralGroup 19,
      Matrix.trace (E7Matrix Γ * permMatrix (h.smulEquiv g)) =
        (d19LinearCharacter alpha beta gamma g : ℚ))
    (hMinus8 : ∀ g : DihedralGroup 19,
      Matrix.trace (permMatrix (h.smulEquiv g)) - 1 -
          Matrix.trace (E7Matrix Γ * permMatrix (h.smulEquiv g)) =
        (d19LinearCharacter A B C g : ℚ))
    {dt : ZMod 19}
    (hK : InvolutionK155 Γ (h.smulEquiv (DihedralGroup.sr dt)))
    (orbitBase : OrbitBaseSelectionEnumeration h)
    (adjacentMoved :
      AdjacentMovedTwoCopyPartition38Witness h orbitBase.base) :
    D19ConstructiveFinalInputs h :=
  ofEigenspaceCharactersAndFixedStar55 (h := h)
    alpha beta gamma A B C h7 hMinus8
    (InvolutionK155.toInvolutionFixedStar55 h.isMoore hK)
    orbitBase adjacentMoved

end D19ConstructiveFinalInputs

end

end Moore57
