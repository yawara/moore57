import Moore57.D19OnMoore57.NoGo.LabeledReflectionMatchingEquationFrontier
import Moore57.D19OnMoore57.BranchOrbit.ABCDataFromCenter

/-!
# Branch A/B/C center-neighbor base frontier

This file gives stable names to the default three-orbit center-neighbor base
used by the raw-action reflection frontier, and routes that base through the
existing `BranchOrbitABCFromCenter` and `BranchOrbitABCData` constructors.
-/

namespace Moore57

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-! ## Stable aliases for the remaining center-neighbor base -/

/-- Stable alias for the default three center-neighbor rotation-orbit base used
by the remaining labeled-reflection frontier. -/
noncomputable abbrev remainingCenterNeighborOrbitBase
    (h : D19ActsOnMoore57 V Γ) : Fin 3 → V :=
  remainingCenterNeighborBase h

/-- Each selected default base point is adjacent to the rotation-fixed center. -/
theorem remainingCenterNeighborOrbitBase_adj
    (h : D19ActsOnMoore57 V Γ) :
    ∀ q : Fin 3,
      Γ.Adj h.rotationFixedCenter (remainingCenterNeighborOrbitBase h q) :=
  remainingCenterNeighborBase_adj (h := h)

/-- Each selected default center-neighbor rotation orbit has size `19`. -/
theorem remainingCenterNeighborOrbitBase_card
    (h : D19ActsOnMoore57 V Γ) :
    ∀ q : Fin 3,
      (h.rotationOrbitFinset (remainingCenterNeighborOrbitBase h q)).card = 19 :=
  (Classical.choose_spec
    h.exists_three_rotationOrbitFinset_neighbors_rotationFixedCenter).2.1

/-- The selected default center-neighbor rotation orbits are pairwise disjoint. -/
theorem remainingCenterNeighborOrbitBase_pairwise_disjoint
    (h : D19ActsOnMoore57 V Γ) :
    ∀ q r : Fin 3, q ≠ r →
      Disjoint (h.rotationOrbitFinset (remainingCenterNeighborOrbitBase h q))
        (h.rotationOrbitFinset (remainingCenterNeighborOrbitBase h r)) :=
  remainingCenterNeighborBase_pairwise_disjoint (h := h)

/-- The selected default center-neighbor rotation orbits cover the whole
neighbor finset of the rotation-fixed center. -/
theorem remainingCenterNeighborOrbitBase_cover
    (h : D19ActsOnMoore57 V Γ) :
    Γ.neighborFinset h.rotationFixedCenter =
      h.orbitFamilyUnion (remainingCenterNeighborOrbitBase h) :=
  remainingCenterNeighborBase_cover (h := h)

/-! ## Conversions to existing A/B/C branch data -/

namespace BranchOrbitABCFromCenter

variable {h : D19ActsOnMoore57 V Γ}

/-- Convert the default remaining center-neighbor base into fixed-center A/B/C
branch data using the existing center-neighbor base constructor. -/
noncomputable def ofRemainingCenterNeighborBase
    (h : D19ActsOnMoore57 V Γ) :
    BranchOrbitABCFromCenter h :=
  ofNeighborOrbitBase (h := h)
    (remainingCenterNeighborOrbitBase h)
    (remainingCenterNeighborOrbitBase_adj (h := h))
    (remainingCenterNeighborOrbitBase_card (h := h))
    (remainingCenterNeighborOrbitBase_pairwise_disjoint (h := h))
    (remainingCenterNeighborOrbitBase_cover (h := h))

/-- The `Fin 3` base stored by `ofRemainingCenterNeighborBase` is the default
remaining center-neighbor base. -/
theorem ofRemainingCenterNeighborBase_base
    (h : D19ActsOnMoore57 V Γ) :
    (ofRemainingCenterNeighborBase (h := h)).base =
      remainingCenterNeighborOrbitBase h := by
  funext q
  fin_cases q <;> rfl

end BranchOrbitABCFromCenter

namespace BranchOrbitABCData

variable {h : D19ActsOnMoore57 V Γ}

/-- Convert the default remaining center-neighbor base into the downstream
`BranchOrbitABCData` package, reusing the existing `BranchOrbitABCFromCenter`
promotion. -/
noncomputable def ofRemainingCenterNeighborBase
    (h : D19ActsOnMoore57 V Γ) :
    BranchOrbitABCData h :=
  (BranchOrbitABCFromCenter.ofRemainingCenterNeighborBase (h := h)).toBranchOrbitABCData

@[simp] theorem ofRemainingCenterNeighborBase_toAFiberCoordinates
    (h : D19ActsOnMoore57 V Γ) :
    (ofRemainingCenterNeighborBase (h := h)).toAFiberCoordinates =
      (BranchOrbitABCFromCenter.ofRemainingCenterNeighborBase (h := h)).toAFiberCoordinates :=
  rfl

end BranchOrbitABCData

/-! ## Default-base reflection-index connector aliases -/

namespace BranchOrbitABCReflectionLabeling

variable {h : D19ActsOnMoore57 V Γ}

/-- Specialize the reflected-orbit-index labeled-pair constructor to the
default remaining center-neighbor base. -/
noncomputable abbrev hasLabeledReflectionPair_of_remainingCenterNeighborBase_index_ne
    {k : ZMod 19} {b : Fin 3}
    (hmove :
      reflectionCenterNeighborOrbitIndex
        (h := h)
        (remainingCenterNeighborOrbitBase h)
        (remainingCenterNeighborOrbitBase_adj (h := h))
        (remainingCenterNeighborOrbitBase_cover (h := h))
        k b ≠ b) :
    HasLabeledReflectionPair h :=
  hasLabeledReflectionPair_of_reflectionCenterNeighborOrbitIndex_ne
    (h := h)
    (remainingCenterNeighborOrbitBase h)
    (remainingCenterNeighborOrbitBase_adj (h := h))
    (remainingCenterNeighborOrbitBase_pairwise_disjoint (h := h))
    (remainingCenterNeighborOrbitBase_cover (h := h))
    hmove

end BranchOrbitABCReflectionLabeling

namespace RemainingReflectionIndexMatchingEquationConnector

variable {h : D19ActsOnMoore57 V Γ}

/-- Constructor for the reflected-index matching-equation connector using the
default remaining center-neighbor base. -/
noncomputable def ofRemainingCenterNeighborBase
    {k : ZMod 19} {b : Fin 3}
    (hmove :
      BranchOrbitABCReflectionLabeling.reflectionCenterNeighborOrbitIndex
        (h := h)
        (remainingCenterNeighborOrbitBase h)
        (remainingCenterNeighborOrbitBase_adj (h := h))
        (remainingCenterNeighborOrbitBase_cover (h := h))
        k b ≠ b)
    (referenceMatchingEquationCardTwo :
      BranchOrbitABCReflectionLabeling.ReferenceFiberMatchingEquationCardTwoOfPair
        (h := h)
        (BranchOrbitABCReflectionLabeling.hasLabeledReflectionPair_of_remainingCenterNeighborBase_index_ne
          (h := h) hmove)) :
    RemainingReflectionIndexMatchingEquationConnector h where
  base := remainingCenterNeighborOrbitBase h
  base_adj := remainingCenterNeighborOrbitBase_adj (h := h)
  base_pairwise_disjoint :=
    remainingCenterNeighborOrbitBase_pairwise_disjoint (h := h)
  base_cover := remainingCenterNeighborOrbitBase_cover (h := h)
  k := k
  b := b
  hmove := hmove
  referenceMatchingEquationCardTwo := referenceMatchingEquationCardTwo

end RemainingReflectionIndexMatchingEquationConnector

end

end Moore57
