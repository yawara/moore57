import Moore57.D19OnMoore57.AdjacentMoved.ReflectionCanonicalAFiberCriteria

/-!
# Fixed/A-fiber contribution decomposition

This file factors the single residual contribution hypothesis used by
`AdjacentMovedReflectionFixedAFiberCriteria38Witness` through two local
contribution statements: one for the canonical rotation-fixed residual side and
one for the A-fiber residual side.
-/

namespace Moore57

open Finset

universe u uP

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- Filtering a disjoint union has cardinality equal to the sum of the
filtered cardinalities.

This is the reusable `Finset.filter_union`/`Finset.card_union_of_disjoint`
step used by the fixed/A-fiber residual contribution constructors below. -/
theorem filter_union_card_eq_add_of_disjoint
    {α : Type*} [DecidableEq α] {s t : Finset α}
    (hdisjoint : Disjoint s t) (p : α → Prop) [DecidablePred p] :
    ((s ∪ t).filter p).card = (s.filter p).card + (t.filter p).card := by
  rw [Finset.filter_union]
  exact Finset.card_union_of_disjoint
    (Disjoint.mono (Finset.filter_subset p s)
      (Finset.filter_subset p t) hdisjoint)

/-- Contribution data for the canonical fixed side and the A-fiber side.

The two local equalities record the filtered cardinalities of each side
separately.  The `contribution_sum` field is the only place where the target
constant `38` is mentioned. -/
structure FixedAFiberContribution38Data
    (h : D19ActsOnMoore57 V Γ) (input : OrbitBaseSelectionInput h)
    (k : ZMod 19) (aPart : Finset V) where
  fixedContribution : ZMod 19 → ℕ
  aFiberContribution : ZMod 19 → ℕ
  fixed_contribution :
    ∀ d : ZMod 19, ∀ _hd : d ≠ 0,
      ((rotationOneFixedResidualPart h input k).filter fun y =>
          Γ.Adj y (h.rotation d y)).card =
        fixedContribution d
  aFiber_contribution :
    ∀ d : ZMod 19, ∀ _hd : d ≠ 0,
      (aPart.filter fun y =>
          Γ.Adj y (h.rotation d y)).card =
        aFiberContribution d
  contribution_sum :
    ∀ d : ZMod 19, ∀ _hd : d ≠ 0,
      fixedContribution d + aFiberContribution d = 38

namespace FixedAFiberContribution38Data

variable {h : D19ActsOnMoore57 V Γ}
variable {input : OrbitBaseSelectionInput h}
variable {k : ZMod 19}
variable {aPart : Finset V}

/-- The two local fixed/A-fiber contribution hypotheses imply the old bundled
residual contribution equation expected by the fixed/A-fiber criterion. -/
theorem residual_contribution
    (data : FixedAFiberContribution38Data h input k aPart) :
    ∀ d : ZMod 19, ∀ _hd : d ≠ 0,
      ((rotationOneFixedResidualPart h input k).filter fun y =>
          Γ.Adj y (h.rotation d y)).card +
        (aPart.filter fun y =>
          Γ.Adj y (h.rotation d y)).card =
        38 := by
  intro d hd
  calc
    ((rotationOneFixedResidualPart h input k).filter fun y =>
          Γ.Adj y (h.rotation d y)).card +
        (aPart.filter fun y =>
          Γ.Adj y (h.rotation d y)).card
        = data.fixedContribution d + data.aFiberContribution d := by
          rw [data.fixed_contribution d hd, data.aFiber_contribution d hd]
    _ = 38 := data.contribution_sum d hd

/-- The filtered cardinality of the residual is the sum of the two local
fixed/A-fiber filtered cardinalities whenever the residual is their disjoint
union. -/
theorem residual_filter_card
    (_data : FixedAFiberContribution38Data h input k aPart)
    (hdisjoint :
      Disjoint (rotationOneFixedResidualPart h input k) aPart)
    (hresidual :
      reflectionCopyResidual h input.base k =
        rotationOneFixedResidualPart h input k ∪ aPart)
    (p : V → Prop) [DecidablePred p] :
    ((reflectionCopyResidual h input.base k).filter p).card =
      ((rotationOneFixedResidualPart h input k).filter p).card +
        (aPart.filter p).card := by
  rw [hresidual]
  exact filter_union_card_eq_add_of_disjoint hdisjoint p

/-- Build the existing fixed/A-fiber criterion from local contribution data. -/
noncomputable def toFixedAFiberCriteria38Witness
    {aSide : ReflectionResidualAFiberSide.{u, uP} h input k}
    (data : FixedAFiberContribution38Data h input k aSide.aPart)
    (reflection_not_mem_orbitFamilyUnion :
      ∀ r : Fin 56,
        h.smul (DihedralGroup.sr k) (input.base r) ∉ input.orbitFamilyUnion)
    (residual_eq :
      reflectionCopyResidual h input.base k =
        rotationOneFixedResidualPart h input k ∪ aSide.aPart) :
    AdjacentMovedReflectionFixedAFiberCriteria38Witness h input where
  k := k
  reflection_not_mem_orbitFamilyUnion :=
    reflection_not_mem_orbitFamilyUnion
  aSide := aSide
  residual_eq := residual_eq
  residual_contribution := data.residual_contribution

/-- Build the downstream split-avoidance witness directly from local
fixed/A-fiber contribution data. -/
noncomputable def toAvoidanceSplit38Witness
    {aSide : ReflectionResidualAFiberSide.{u, uP} h input k}
    (data : FixedAFiberContribution38Data h input k aSide.aPart)
    (reflection_not_mem_orbitFamilyUnion :
      ∀ r : Fin 56,
        h.smul (DihedralGroup.sr k) (input.base r) ∉ input.orbitFamilyUnion)
    (residual_eq :
      reflectionCopyResidual h input.base k =
        rotationOneFixedResidualPart h input k ∪ aSide.aPart) :
    AdjacentMovedReflectionAvoidanceSplit38Witness h input :=
  (data.toFixedAFiberCriteria38Witness
    reflection_not_mem_orbitFamilyUnion residual_eq).toAvoidanceSplit38Witness

/-- Build the canonical A-fiber criterion from local contribution data. -/
noncomputable def toCanonicalAFiberCriteria38Witness
    {coords : AFiberCoordinates.{u, uP} Γ} {indices : Finset (ZMod 19)}
    (data : FixedAFiberContribution38Data h input k
      (coords.fiberUnion indices))
    (reflection_not_mem_orbitFamilyUnion :
      ∀ r : Fin 56,
        h.smul (DihedralGroup.sr k) (input.base r) ∉ input.orbitFamilyUnion)
    (moving_eq_aFiber :
      rotationOneMovingResidualPart h input k = coords.fiberUnion indices) :
    AdjacentMovedReflectionCanonicalAFiberCriteria38Witness h input where
  k := k
  reflection_not_mem_orbitFamilyUnion :=
    reflection_not_mem_orbitFamilyUnion
  coords := coords
  indices := indices
  moving_eq_aFiber := moving_eq_aFiber
  residual_contribution := data.residual_contribution

end FixedAFiberContribution38Data

namespace AdjacentMovedReflectionFixedAFiberCriteria38Witness

variable {h : D19ActsOnMoore57 V Γ}
variable {input : OrbitBaseSelectionInput h}
variable {k : ZMod 19}
variable {aSide : ReflectionResidualAFiberSide.{u, uP} h input k}

/-- Constructor wrapper for the fixed/A-fiber criterion from split local
contribution data. -/
noncomputable def of_contributionData
    (data : FixedAFiberContribution38Data h input k aSide.aPart)
    (reflection_not_mem_orbitFamilyUnion :
      ∀ r : Fin 56,
        h.smul (DihedralGroup.sr k) (input.base r) ∉ input.orbitFamilyUnion)
    (residual_eq :
      reflectionCopyResidual h input.base k =
        rotationOneFixedResidualPart h input k ∪ aSide.aPart) :
    AdjacentMovedReflectionFixedAFiberCriteria38Witness h input :=
  data.toFixedAFiberCriteria38Witness
    reflection_not_mem_orbitFamilyUnion residual_eq

end AdjacentMovedReflectionFixedAFiberCriteria38Witness

namespace AdjacentMovedReflectionCanonicalAFiberCriteria38Witness

variable {h : D19ActsOnMoore57 V Γ}
variable {input : OrbitBaseSelectionInput h}
variable {k : ZMod 19}
variable {coords : AFiberCoordinates.{u, uP} Γ}
variable {indices : Finset (ZMod 19)}

/-- Constructor wrapper for the canonical A-fiber criterion from split local
contribution data. -/
noncomputable def of_contributionData
    (data : FixedAFiberContribution38Data h input k
      (coords.fiberUnion indices))
    (reflection_not_mem_orbitFamilyUnion :
      ∀ r : Fin 56,
        h.smul (DihedralGroup.sr k) (input.base r) ∉ input.orbitFamilyUnion)
    (moving_eq_aFiber :
      rotationOneMovingResidualPart h input k = coords.fiberUnion indices) :
    AdjacentMovedReflectionCanonicalAFiberCriteria38Witness h input :=
  data.toCanonicalAFiberCriteria38Witness
    reflection_not_mem_orbitFamilyUnion moving_eq_aFiber

end AdjacentMovedReflectionCanonicalAFiberCriteria38Witness

namespace AdjacentMovedReflectionAvoidanceSplit38Witness

variable {h : D19ActsOnMoore57 V Γ}
variable {input : OrbitBaseSelectionInput h}
variable {k : ZMod 19}
variable {aSide : ReflectionResidualAFiberSide.{u, uP} h input k}

/-- Constructor wrapper from local fixed/A-fiber contribution data to the
existing split-avoidance witness. -/
noncomputable def of_fixedAFiberContributionData
    (data : FixedAFiberContribution38Data h input k aSide.aPart)
    (reflection_not_mem_orbitFamilyUnion :
      ∀ r : Fin 56,
        h.smul (DihedralGroup.sr k) (input.base r) ∉ input.orbitFamilyUnion)
    (residual_eq :
      reflectionCopyResidual h input.base k =
        rotationOneFixedResidualPart h input k ∪ aSide.aPart) :
    AdjacentMovedReflectionAvoidanceSplit38Witness h input :=
  data.toAvoidanceSplit38Witness
    reflection_not_mem_orbitFamilyUnion residual_eq

end AdjacentMovedReflectionAvoidanceSplit38Witness

end Moore57
