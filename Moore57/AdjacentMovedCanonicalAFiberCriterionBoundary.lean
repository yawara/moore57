import Moore57.AFiberHybridBoundaryFromCriteria

/-!
# Boundary bridges for the canonical adjacent-moved A-fiber criterion

This file records low-level bridges around
`AdjacentMovedReflectionCanonicalAFiberCriteria38Witness`.  The bridges do not
change the criterion: they expose its fields as existing inclusion,
fixed/A-fiber, avoidance-split, and contribution-data criteria.
-/

namespace Moore57

open Finset

universe u uP

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

namespace AdjacentMovedReflectionCanonicalAFiberCriteria38Witness

variable {h : D19ActsOnMoore57 V Γ}
variable {input : OrbitBaseSelectionInput h}

/-- Recover the canonical equality-form criterion from the fixed/A-fiber
criterion.  The fixed/A-fiber criterion already proves that its A-side is the
canonical moving residual part. -/
noncomputable def of_fixedAFiberCriteria
    (w : AdjacentMovedReflectionFixedAFiberCriteria38Witness.{u, uP}
      h input) :
    AdjacentMovedReflectionCanonicalAFiberCriteria38Witness.{u, uP}
      h input where
  k := w.k
  reflection_not_mem_orbitFamilyUnion :=
    w.reflection_not_mem_orbitFamilyUnion
  coords := w.aSide.coords
  indices := w.aSide.indices
  moving_eq_aFiber := by
    simpa [ReflectionResidualAFiberSide.aPart] using
      w.aPart_eq_rotationOneMovingResidualPart.symm
  residual_contribution := by
    intro d hd
    simpa [ReflectionResidualAFiberSide.aPart] using
      w.residual_contribution d hd

/-- The canonical criterion exposes its split fixed/A-fiber contribution data
by naming the two filtered cardinality functions. -/
noncomputable def toFixedAFiberContribution38Data
    (w :
      AdjacentMovedReflectionCanonicalAFiberCriteria38Witness.{u, uP}
        h input) :
    FixedAFiberContribution38Data h input w.k
      (w.coords.fiberUnion w.indices) where
  fixedContribution := fixedAFiberFixedCard h input w.k
  aFiberContribution :=
    fixedAFiberAFiberCard h (w.coords.fiberUnion w.indices)
  fixed_contribution := by
    intro d hd
    rfl
  aFiber_contribution := by
    intro d hd
    rfl
  contribution_sum := by
    intro d hd
    simpa [fixedAFiberFixedCard, fixedAFiberAFiberCard] using
      w.residual_contribution d hd

/-- Method-form nonempty wrapper for the contribution data extracted from a
canonical criterion. -/
theorem contributionData_nonempty
    (w :
      AdjacentMovedReflectionCanonicalAFiberCriteria38Witness.{u, uP}
        h input) :
    Nonempty
      (FixedAFiberContribution38Data h input w.k
        (w.coords.fiberUnion w.indices)) :=
  ⟨w.toFixedAFiberContribution38Data⟩

/-- Build the canonical criterion from split fixed/A-fiber contribution data,
reflected-base avoidance, and the canonical moving/A-fiber equality. -/
theorem nonempty_of_contributionData
    {k : ZMod 19} {coords : AFiberCoordinates.{u, uP} Γ}
    {indices : Finset (ZMod 19)}
    (data : FixedAFiberContribution38Data h input k
      (coords.fiberUnion indices))
    (reflection_not_mem_orbitFamilyUnion :
      ∀ r : Fin 56,
        h.smul (DihedralGroup.sr k) (input.base r) ∉
          input.orbitFamilyUnion)
    (moving_eq_aFiber :
      rotationOneMovingResidualPart h input k =
        coords.fiberUnion indices) :
    Nonempty
      (AdjacentMovedReflectionCanonicalAFiberCriteria38Witness.{u, uP}
        h input) :=
  ⟨data.toCanonicalAFiberCriteria38Witness
    reflection_not_mem_orbitFamilyUnion moving_eq_aFiber⟩

/-- Nonempty form when the split fixed/A-fiber contribution data is itself
provided as a `Nonempty` hypothesis. -/
theorem nonempty_of_contributionData_nonempty
    {k : ZMod 19} {coords : AFiberCoordinates.{u, uP} Γ}
    {indices : Finset (ZMod 19)}
    (data :
      Nonempty
        (FixedAFiberContribution38Data h input k
          (coords.fiberUnion indices)))
    (reflection_not_mem_orbitFamilyUnion :
      ∀ r : Fin 56,
        h.smul (DihedralGroup.sr k) (input.base r) ∉
          input.orbitFamilyUnion)
    (moving_eq_aFiber :
      rotationOneMovingResidualPart h input k =
        coords.fiberUnion indices) :
    Nonempty
      (AdjacentMovedReflectionCanonicalAFiberCriteria38Witness.{u, uP}
        h input) := by
  rcases data with ⟨data⟩
  exact nonempty_of_contributionData data
    reflection_not_mem_orbitFamilyUnion moving_eq_aFiber

/-- Build the canonical criterion from the direct A-fiber-cardinality boundary,
using the existing zero contribution theorem for the canonical fixed residual
side. -/
noncomputable def of_aFiberCardinalityBoundary
    {k : ZMod 19} {coords : AFiberCoordinates.{u, uP} Γ}
    {indices : Finset (ZMod 19)}
    (boundary : AFiberCardinality38Boundary h coords indices)
    (reflection_not_mem_orbitFamilyUnion :
      ∀ r : Fin 56,
        h.smul (DihedralGroup.sr k) (input.base r) ∉
          input.orbitFamilyUnion)
    (moving_eq_aFiber :
      rotationOneMovingResidualPart h input k =
        coords.fiberUnion indices) :
    AdjacentMovedReflectionCanonicalAFiberCriteria38Witness.{u, uP}
      h input := by
  let onlyData :
      AFiberOnlyContribution38Data h input k
        (coords.fiberUnion indices) :=
    boundary.toAFiberOnlyContribution38Data input k
  let data :
      FixedAFiberContribution38Data h input k
        (coords.fiberUnion indices) :=
    onlyData.toFixedAFiberContribution38Data
  exact data.toCanonicalAFiberCriteria38Witness
      reflection_not_mem_orbitFamilyUnion moving_eq_aFiber

/-- Nonempty wrapper for `of_aFiberCardinalityBoundary`. -/
theorem nonempty_of_aFiberCardinalityBoundary
    {k : ZMod 19} {coords : AFiberCoordinates.{u, uP} Γ}
    {indices : Finset (ZMod 19)}
    (boundary : AFiberCardinality38Boundary h coords indices)
    (reflection_not_mem_orbitFamilyUnion :
      ∀ r : Fin 56,
        h.smul (DihedralGroup.sr k) (input.base r) ∉
          input.orbitFamilyUnion)
    (moving_eq_aFiber :
      rotationOneMovingResidualPart h input k =
        coords.fiberUnion indices) :
    Nonempty
      (AdjacentMovedReflectionCanonicalAFiberCriteria38Witness.{u, uP}
        h input) :=
  ⟨of_aFiberCardinalityBoundary boundary
    reflection_not_mem_orbitFamilyUnion moving_eq_aFiber⟩

/-- A branch-coordinate constructor for the canonical criterion. -/
noncomputable def ofBranches_contributionData
    (hΓ : IsMoore57 Γ) (u : V) (a : ZMod 19 → V)
    (hub : ∀ i : ZMod 19, Γ.Adj u (a i))
    (hinj : Function.Injective a)
    {k : ZMod 19} {indices : Finset (ZMod 19)}
    (data :
      FixedAFiberContribution38Data h input k
        ((AFiberCoordinates.ofBranches hΓ u a hub hinj).fiberUnion
          indices))
    (reflection_not_mem_orbitFamilyUnion :
      ∀ r : Fin 56,
        h.smul (DihedralGroup.sr k) (input.base r) ∉
          input.orbitFamilyUnion)
    (moving_eq_aFiber :
      rotationOneMovingResidualPart h input k =
        (AFiberCoordinates.ofBranches hΓ u a hub hinj).fiberUnion
          indices) :
    AdjacentMovedReflectionCanonicalAFiberCriteria38Witness.{u, u}
      h input :=
  data.toCanonicalAFiberCriteria38Witness
    reflection_not_mem_orbitFamilyUnion moving_eq_aFiber

/-- Nonempty wrapper for the branch-coordinate constructor. -/
theorem nonempty_ofBranches_contributionData
    (hΓ : IsMoore57 Γ) (u : V) (a : ZMod 19 → V)
    (hub : ∀ i : ZMod 19, Γ.Adj u (a i))
    (hinj : Function.Injective a)
    {k : ZMod 19} {indices : Finset (ZMod 19)}
    (data :
      FixedAFiberContribution38Data h input k
        ((AFiberCoordinates.ofBranches hΓ u a hub hinj).fiberUnion
          indices))
    (reflection_not_mem_orbitFamilyUnion :
      ∀ r : Fin 56,
        h.smul (DihedralGroup.sr k) (input.base r) ∉
          input.orbitFamilyUnion)
    (moving_eq_aFiber :
      rotationOneMovingResidualPart h input k =
        (AFiberCoordinates.ofBranches hΓ u a hub hinj).fiberUnion
          indices) :
    Nonempty
      (AdjacentMovedReflectionCanonicalAFiberCriteria38Witness.{u, u}
        h input) :=
  ⟨ofBranches_contributionData hΓ u a hub hinj data
    reflection_not_mem_orbitFamilyUnion moving_eq_aFiber⟩

/-- A canonical criterion gives the inclusion-form canonical criterion at the
`Nonempty` level. -/
theorem nonempty_to_inclusionCriteria38Witness :
    Nonempty
        (AdjacentMovedReflectionCanonicalAFiberCriteria38Witness.{u, uP}
          h input) →
      Nonempty
        (AdjacentMovedReflectionCanonicalAFiberInclusionCriteria38Witness.{u, uP}
          h input) := by
  rintro ⟨w⟩
  exact ⟨w.toInclusionCriteria38Witness⟩

/-- The inclusion-form canonical criterion gives the equality-form canonical
criterion at the `Nonempty` level. -/
theorem nonempty_of_inclusionCriteria38Witness :
    Nonempty
        (AdjacentMovedReflectionCanonicalAFiberInclusionCriteria38Witness.{u, uP}
          h input) →
      Nonempty
        (AdjacentMovedReflectionCanonicalAFiberCriteria38Witness.{u, uP}
          h input) := by
  rintro ⟨w⟩
  exact ⟨w.toCanonicalAFiberCriteria38Witness⟩

/-- Equality-form and inclusion-form canonical criteria are equivalent at the
`Nonempty` level. -/
theorem nonempty_iff_inclusionCriteria38Witness :
    Nonempty
        (AdjacentMovedReflectionCanonicalAFiberCriteria38Witness.{u, uP}
          h input) ↔
      Nonempty
        (AdjacentMovedReflectionCanonicalAFiberInclusionCriteria38Witness.{u, uP}
          h input) := by
  constructor
  · exact nonempty_to_inclusionCriteria38Witness
  · exact nonempty_of_inclusionCriteria38Witness

/-- A canonical criterion gives the fixed/A-fiber criterion at the `Nonempty`
level. -/
theorem nonempty_to_fixedAFiberCriteria38Witness :
    Nonempty
        (AdjacentMovedReflectionCanonicalAFiberCriteria38Witness.{u, uP}
          h input) →
      Nonempty
        (AdjacentMovedReflectionFixedAFiberCriteria38Witness.{u, uP}
          h input) := by
  rintro ⟨w⟩
  exact ⟨w.toFixedAFiberCriteria38Witness⟩

/-- The fixed/A-fiber criterion recovers the canonical criterion at the
`Nonempty` level. -/
theorem nonempty_of_fixedAFiberCriteria38Witness :
    Nonempty
        (AdjacentMovedReflectionFixedAFiberCriteria38Witness.{u, uP}
          h input) →
      Nonempty
        (AdjacentMovedReflectionCanonicalAFiberCriteria38Witness.{u, uP}
          h input) := by
  rintro ⟨w⟩
  exact ⟨of_fixedAFiberCriteria w⟩

/-- Canonical and fixed/A-fiber criteria are equivalent at the `Nonempty`
level. -/
theorem nonempty_iff_fixedAFiberCriteria38Witness :
    Nonempty
        (AdjacentMovedReflectionCanonicalAFiberCriteria38Witness.{u, uP}
          h input) ↔
      Nonempty
        (AdjacentMovedReflectionFixedAFiberCriteria38Witness.{u, uP}
          h input) := by
  constructor
  · exact nonempty_to_fixedAFiberCriteria38Witness
  · exact nonempty_of_fixedAFiberCriteria38Witness

/-- A canonical criterion gives the existing split-avoidance witness at the
`Nonempty` level. -/
theorem nonempty_to_avoidanceSplit38Witness :
    Nonempty
        (AdjacentMovedReflectionCanonicalAFiberCriteria38Witness.{u, uP}
          h input) →
      Nonempty (AdjacentMovedReflectionAvoidanceSplit38Witness h input) := by
  rintro ⟨w⟩
  exact ⟨w.toAvoidanceSplit38Witness⟩

/-- A canonical criterion also gives the compact avoidance criterion through
the existing split-avoidance conversion. -/
theorem nonempty_to_avoidanceComplementResidual38Witness :
    Nonempty
        (AdjacentMovedReflectionCanonicalAFiberCriteria38Witness.{u, uP}
          h input) →
      Nonempty
        (AdjacentMovedReflectionAvoidanceComplementResidual38Witness
          h input) := by
  rintro ⟨w⟩
  exact ⟨w.toAvoidanceSplit38Witness.toAvoidanceComplementResidual38Witness⟩

end AdjacentMovedReflectionCanonicalAFiberCriteria38Witness

namespace AdjacentMovedReflectionCanonicalAFiberInclusionCriteria38Witness

variable {h : D19ActsOnMoore57 V Γ}
variable {input : OrbitBaseSelectionInput h}

/-- Symmetric spelling of the canonical/inclusion `Nonempty` bridge. -/
theorem nonempty_iff_canonicalAFiberCriteria38Witness :
    Nonempty
        (AdjacentMovedReflectionCanonicalAFiberInclusionCriteria38Witness.{u, uP}
          h input) ↔
      Nonempty
        (AdjacentMovedReflectionCanonicalAFiberCriteria38Witness.{u, uP}
          h input) :=
  (AdjacentMovedReflectionCanonicalAFiberCriteria38Witness.nonempty_iff_inclusionCriteria38Witness
    (h := h) (input := input)).symm

end AdjacentMovedReflectionCanonicalAFiberInclusionCriteria38Witness

namespace AdjacentMovedReflectionFixedAFiberCriteria38Witness

variable {h : D19ActsOnMoore57 V Γ}
variable {input : OrbitBaseSelectionInput h}

/-- Symmetric spelling of the canonical/fixed-A-fiber `Nonempty` bridge. -/
theorem nonempty_iff_canonicalAFiberCriteria38Witness :
    Nonempty
        (AdjacentMovedReflectionFixedAFiberCriteria38Witness.{u, uP}
          h input) ↔
      Nonempty
        (AdjacentMovedReflectionCanonicalAFiberCriteria38Witness.{u, uP}
          h input) :=
  (AdjacentMovedReflectionCanonicalAFiberCriteria38Witness.nonempty_iff_fixedAFiberCriteria38Witness
    (h := h) (input := input)).symm

end AdjacentMovedReflectionFixedAFiberCriteria38Witness

namespace AdjacentMovedReflectionAvoidanceSplit38Witness

variable {h : D19ActsOnMoore57 V Γ}
variable {input : OrbitBaseSelectionInput h}

/-- Constructor wrapper from the canonical criterion at the `Nonempty` level. -/
theorem nonempty_of_canonicalAFiberCriteria38Witness :
    Nonempty
        (AdjacentMovedReflectionCanonicalAFiberCriteria38Witness.{u, uP}
          h input) →
      Nonempty (AdjacentMovedReflectionAvoidanceSplit38Witness h input) :=
  AdjacentMovedReflectionCanonicalAFiberCriteria38Witness.nonempty_to_avoidanceSplit38Witness
    (h := h) (input := input)

end AdjacentMovedReflectionAvoidanceSplit38Witness

end Moore57
