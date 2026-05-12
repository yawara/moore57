import Moore57.D19OnMoore57.NoGo.NonRepresentationFrontierEigenspaceNoGo
import Moore57.D19OnMoore57.NoGo.NonRepresentationFrontierStarNoGo
import Moore57.D19OnMoore57.Rotation.FixedCountOneFrontier

/-!
# Auto-rotation no-go for the default-base non-representation frontier

This file removes the explicit rotation fixed-count hypothesis from the
post-default-base frontier no-go surfaces.  The rotation count is supplied by
the proved `D19ActsOnMoore57.rotationFixedCountOne_smulEquiv` theorem.
-/

namespace Moore57

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- Eigenspace-character no-go with explicit reflection counts and automatic
rotation count-one input from the ambient `D19ActsOnMoore57` theorem. -/
theorem no_remainingNonRepresentationFrontierAfterDefaultBase_of_eigenspaceCharactersAndReflectionCounts_autoRotation
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
    ¬ Nonempty (RemainingNonRepresentationFrontierAfterDefaultBase h) :=
  no_remainingNonRepresentationFrontierAfterDefaultBase_of_eigenspaceCharactersAndCounts
    h alpha beta gamma A B C h7 hMinus8 hreflection_a0
    (D19ActsOnMoore57.rotationFixedCountOne_smulEquiv h) hreflection_a1

/-- Raw-action-frontier alias of the auto-rotation eigenspace/reflection-count
no-go. -/
theorem no_remainingNonRepresentationRawActionFrontierAfterDefaultBase_of_eigenspaceCharactersAndReflectionCounts_autoRotation
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
    ¬ RemainingNonRepresentationRawActionFrontierAfterDefaultBase h :=
  no_remainingNonRepresentationFrontierAfterDefaultBase_of_eigenspaceCharactersAndReflectionCounts_autoRotation
    h alpha beta gamma A B C h7 hMinus8 hreflection_a0 hreflection_a1

/-- Eigenspace-character no-go with reflection counts supplied by an
`InvolutionFixedStar55` witness and rotation counts supplied automatically. -/
theorem no_remainingNonRepresentationFrontierAfterDefaultBase_of_eigenspaceCharactersAndFixedStar55_autoRotation
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
    ¬ Nonempty (RemainingNonRepresentationFrontierAfterDefaultBase h) :=
  no_remainingNonRepresentationFrontierAfterDefaultBase_of_eigenspaceCharactersAndFixedStar55
    h alpha beta gamma A B C h7 hMinus8 hStar
    (D19ActsOnMoore57.rotationFixedCountOne_smulEquiv h)

/-- Raw-action-frontier alias of the auto-rotation fixed-star eigenspace
no-go. -/
theorem no_remainingNonRepresentationRawActionFrontierAfterDefaultBase_of_eigenspaceCharactersAndFixedStar55_autoRotation
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
    ¬ RemainingNonRepresentationRawActionFrontierAfterDefaultBase h :=
  no_remainingNonRepresentationFrontierAfterDefaultBase_of_eigenspaceCharactersAndFixedStar55_autoRotation
    h alpha beta gamma A B C h7 hMinus8 hStar

end

end Moore57
