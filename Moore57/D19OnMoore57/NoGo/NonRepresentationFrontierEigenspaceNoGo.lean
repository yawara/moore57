import Moore57.D19OnMoore57.LinearCharacter.Minus8Connectors
import Moore57.D19OnMoore57.NoGo.NonRepresentationFrontierAfterDefaultBase

/-!
# Eigenspace-character connector for the post-default-base frontier

This file keeps the representation-theoretic work behind the existing
`D19LinearCharacterMinus8Connectors` boundary.  The post-default-base
non-representation frontier can therefore consume the eigenspace character
identities and fixed-count data directly.
-/

namespace Moore57

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- Eigenspace character identities and the standard fixed-count data supply
the representation components needed to refute the post-default-base
non-representation frontier. -/
theorem no_remainingNonRepresentationFrontierAfterDefaultBase_of_eigenspaceCharactersAndCounts
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
    ¬ Nonempty (RemainingNonRepresentationFrontierAfterDefaultBase h) := by
  intro frontier
  exact no_remainingNonRepresentationFrontierAfterDefaultBase_of_components h
    ⟨D19ActsOnMoore57.representationCharacterComponentsBoundary_of_eigenspaceCharactersAndCounts
        h alpha beta gamma A B C h7 hMinus8 hreflection_a0
        hrotation_a0 hreflection_a1,
      frontier⟩

/-- Raw-action-frontier alias of
`no_remainingNonRepresentationFrontierAfterDefaultBase_of_eigenspaceCharactersAndCounts`.
-/
theorem no_remainingNonRepresentationRawActionFrontierAfterDefaultBase_of_eigenspaceCharactersAndCounts
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
    ¬ RemainingNonRepresentationRawActionFrontierAfterDefaultBase h :=
  no_remainingNonRepresentationFrontierAfterDefaultBase_of_eigenspaceCharactersAndCounts
    h alpha beta gamma A B C h7 hMinus8 hreflection_a0 hrotation_a0
    hreflection_a1

end

end Moore57
