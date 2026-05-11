import Moore57.Foundations.GroupAction.InvolutionParity
import Moore57.Foundations.GroupAction.FixedPointBasics
import Moore57.D19OnMoore57.Reflection.ReflectionInvolutionFixedSetStarFromActionBoundary

/-!
# Parity constraints for involutions

This file records small parity consequences for involutions, including the
reflection permutations supplied by a `D19ActsOnMoore57` action.
-/

namespace Moore57

open Finset

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]

variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- The vertices sent to adjacent vertices by an involution come in swapped
pairs. -/
theorem two_dvd_adjacentMovedCount_of_involutive
    (Γ : SimpleGraph V) [DecidableRel Γ.Adj]
    (σ : Equiv.Perm V) (hσ : Function.Involutive σ) :
    2 ∣ adjacentMovedCount Γ σ := by
  classical
  let S := {v : V // Γ.Adj v (σ v)}
  let τ : Equiv.Perm S := {
    toFun := fun x =>
      ⟨σ x, by
        simpa [hσ x] using x.property.symm⟩
    invFun := fun x =>
      ⟨σ x, by
        simpa [hσ x] using x.property.symm⟩
    left_inv := by
      intro x
      ext
      exact hσ x
    right_inv := by
      intro x
      ext
      exact hσ x
  }
  have hτ : Function.Involutive τ := by
    intro x
    ext
    exact hσ x
  have hsupport : τ.support = (Finset.univ : Finset S) := by
    ext x
    simp [Equiv.Perm.mem_support]
    intro hfix
    have hval : σ x = x := congrArg Subtype.val hfix
    have hloop : Γ.Adj (x : V) (x : V) := by
      simpa [hval] using x.property
    exact SimpleGraph.irrefl Γ hloop
  have hcard :
      adjacentMovedCount Γ σ = Fintype.card S := by
    simpa [adjacentMovedCount, S] using
      (Fintype.card_subtype (fun v : V => Γ.Adj v (σ v))).symm
  rw [hcard]
  simpa [hsupport] using two_dvd_support_card_of_involutive τ hτ

namespace D19ActsOnMoore57

variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]
variable (h : D19ActsOnMoore57 V Γ)

/-- A reflection in a `D19ActsOnMoore57` action moves an even number of
vertices. -/
theorem two_dvd_reflection_support_card (k : ZMod 19) :
    2 ∣ (Equiv.Perm.support (h.smulEquiv (DihedralGroup.sr k))).card :=
  two_dvd_support_card_of_involutive
    (h.smulEquiv (DihedralGroup.sr k))
    (h.reflection_smulEquiv_involutive k)

/-- A reflection in a `D19ActsOnMoore57` action has even non-fixed count. -/
theorem two_dvd_card_sub_reflection_fixedVertexCount (k : ZMod 19) :
    2 ∣ Fintype.card V - fixedVertexCount (h.smulEquiv (DihedralGroup.sr k)) :=
  two_dvd_card_sub_fixedVertexCount_of_involutive
    (h.smulEquiv (DihedralGroup.sr k))
    (h.reflection_smulEquiv_involutive k)

/-- The adjacent-moved count of a reflection in a `D19ActsOnMoore57` action is
even. -/
theorem two_dvd_reflection_adjacentMovedCount (k : ZMod 19) :
    2 ∣ adjacentMovedCount Γ (h.smulEquiv (DihedralGroup.sr k)) :=
  two_dvd_adjacentMovedCount_of_involutive Γ
    (h.smulEquiv (DihedralGroup.sr k))
    (h.reflection_smulEquiv_involutive k)

end D19ActsOnMoore57

end

end Moore57
