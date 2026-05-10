import Mathlib.GroupTheory.Perm.Cycle.Type
import Moore57.GroupAction.FixedPoints

/-!
# Parity constraints for involutions

This module records graph-independent parity facts for finite involutive
permutations.
-/

namespace Moore57

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]

/-- The moving support of an involution has even cardinality. -/
theorem two_dvd_support_card_of_involutive
    (σ : Equiv.Perm V) (hσ : Function.Involutive σ) :
    2 ∣ σ.support.card := by
  exact Equiv.Perm.two_dvd_card_support (σ := σ) (by
    ext v
    exact hσ v)

/-- Equivalently, an involution moves an even number of vertices. -/
theorem two_dvd_card_sub_fixedVertexCount_of_involutive
    (σ : Equiv.Perm V) (hσ : Function.Involutive σ) :
    2 ∣ Fintype.card V - fixedVertexCount σ := by
  classical
  have hsupport :
      σ.support.card = Fintype.card V - fixedVertexCount σ := by
    have hsum :
        σ.support.card + σ.supportᶜ.card = Fintype.card V :=
      Finset.card_add_card_compl σ.support
    have hfixed : fixedVertexCount σ = σ.supportᶜ.card := by
      simp [fixedVertexCount, Equiv.Perm.support]
    omega
  simpa [hsupport] using two_dvd_support_card_of_involutive σ hσ

end

end Moore57
