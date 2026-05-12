import Moore57.D19OnMoore57.Reflection.RawGeometrySplit
import Moore57.D19OnMoore57.Reflection.RegularTenDefaultBaseBoundary

/-!
# Default-base index split for raw reflections

The raw geometry split has a concrete default-base interpretation:

* the local fixed-center leaf branch supplies a moved reflected
  center-neighbor orbit index;
* the regular-`10` all-preserved branch fixes every default-base orbit index.

This file records that dichotomy without adding new hypotheses.
-/

namespace Moore57

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

namespace D19ActsOnMoore57

variable {h : D19ActsOnMoore57 V Γ}

/-- For every reflection, the default three center-neighbor orbit indices are
either moved somewhere, or all fixed.  The latter case is exactly what the
regular-`10` preserved-orbits branch supplies. -/
theorem exists_moved_defaultBase_index_or_forall_defaultBase_index_fixed
    (k : ZMod 19) :
    (∃ b : Fin 3,
      BranchOrbitABCReflectionLabeling.reflectionCenterNeighborOrbitIndex
        (h := h)
        (remainingCenterNeighborOrbitBase h)
        (remainingCenterNeighborOrbitBase_adj (h := h))
        (remainingCenterNeighborOrbitBase_cover (h := h))
        k b ≠ b) ∨
    (∀ q : Fin 3,
      BranchOrbitABCReflectionLabeling.reflectionCenterNeighborOrbitIndex
        (h := h)
        (remainingCenterNeighborOrbitBase h)
        (remainingCenterNeighborOrbitBase_adj (h := h))
        (remainingCenterNeighborOrbitBase_cover (h := h))
        k q = q) := by
  rcases h.reflectionFixedCenterLeafAt_or_regularTenAllCenterNeighborOrbitsPreserved
      k with hleaf | hregular
  · exact Or.inl hleaf.exists_remainingCenterNeighborBase_index_ne
  · exact Or.inr
      hregular.remainingCenterNeighborOrbitBase_reflectionCenterNeighborOrbitIndex_eq_self

/-- Contrapositive form: if no default-base index is moved for a reflection,
the default-base quotient action fixes all three indices. -/
theorem forall_defaultBase_index_fixed_of_not_exists_moved_defaultBase_index
    (k : ZMod 19)
    (hnoMove :
      ¬ ∃ b : Fin 3,
        BranchOrbitABCReflectionLabeling.reflectionCenterNeighborOrbitIndex
          (h := h)
          (remainingCenterNeighborOrbitBase h)
          (remainingCenterNeighborOrbitBase_adj (h := h))
          (remainingCenterNeighborOrbitBase_cover (h := h))
          k b ≠ b) :
    ∀ q : Fin 3,
      BranchOrbitABCReflectionLabeling.reflectionCenterNeighborOrbitIndex
        (h := h)
        (remainingCenterNeighborOrbitBase h)
        (remainingCenterNeighborOrbitBase_adj (h := h))
        (remainingCenterNeighborOrbitBase_cover (h := h))
        k q = q := by
  rcases h.exists_moved_defaultBase_index_or_forall_defaultBase_index_fixed k with
    hmove | hfixed
  · exact False.elim (hnoMove hmove)
  · exact hfixed

/-- If a global fixed-center leaf boundary is unavailable, then some
reflection fixes every default-base center-neighbor orbit index. -/
theorem exists_reflection_forall_defaultBase_index_fixed_of_not_reflectionFixedCenterLeafBoundary
    (hnoLeaf : ¬ ReflectionFixedCenterLeafBoundary h) :
    ∃ k : ZMod 19,
      ∀ q : Fin 3,
        BranchOrbitABCReflectionLabeling.reflectionCenterNeighborOrbitIndex
          (h := h)
          (remainingCenterNeighborOrbitBase h)
          (remainingCenterNeighborOrbitBase_adj (h := h))
          (remainingCenterNeighborOrbitBase_cover (h := h))
          k q = q := by
  rcases h.exists_regularTenAllCenterNeighborOrbitsPreserved_of_not_reflectionFixedCenterLeafBoundary
      hnoLeaf with ⟨k, hregular⟩
  exact
    ⟨k,
      hregular.remainingCenterNeighborOrbitBase_reflectionCenterNeighborOrbitIndex_eq_self⟩

end D19ActsOnMoore57

end

end Moore57
