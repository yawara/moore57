import Moore57.D19OnMoore57.Final.Inputs
import Moore57.D19OnMoore57.AdjacentMoved.TwoCopyCriteria
import Moore57.D19OnMoore57.Orbit.BaseSelectionEnumeration

/-!
# Constructive final D19 input packaging

This file gives a more constructive high-level boundary for the final D19
contradiction inputs: orbit bases are supplied by an explicit coordinate
enumeration, and the adjacent-moved contribution is supplied by the specialized
two-copy partition witness with residual contribution `38`.
-/

namespace Moore57

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- Constructive final input record for the D19 contradiction.

Compared with `D19FinalInputs`, this asks for the orbit base via an injective
coordinate enumeration and asks for the adjacent-moved decomposition via the
specialized two-copy partition witness whose residual contribution is `38`. -/
structure D19ConstructiveFinalInputs (h : D19ActsOnMoore57 V Γ) where
  /-- Split final character input. -/
  character : D19FinalCharacterInputs h
  /-- Constructive enumeration of the selected 56 moved rotation orbits. -/
  orbitBase : OrbitBaseSelectionEnumeration h
  /-- Constructive two-copy adjacent-moved partition over the selected bases. -/
  adjacentMoved :
    AdjacentMovedTwoCopyPartition38Witness h orbitBase.base

namespace D19ConstructiveFinalInputs

variable {h : D19ActsOnMoore57 V Γ}

/-- Forget the constructive witnesses down to the final input boundary. -/
noncomputable def toD19FinalInputs
    (data : D19ConstructiveFinalInputs h) :
    D19FinalInputs h where
  character := data.character
  orbitBase := data.orbitBase.toWitness
  fixedOrAContribution := fixedOrAContribution38
  fixed_or_A_contribution := by
    intro d hd
    rfl
  adjacentMovedDecomposition := by
    simpa [OrbitBaseSelectionEnumeration.toWitness,
      OrbitBaseSelectionWitness.ofOrbitCoordinateInjective] using
      data.adjacentMoved.toDecomposition

/-- Constructive final inputs cannot exist. -/
theorem not_nonempty (h : D19ActsOnMoore57 V Γ) :
    ¬ Nonempty (D19ConstructiveFinalInputs h) := by
  rintro ⟨data⟩
  exact D19FinalInputs.not_nonempty h ⟨data.toD19FinalInputs⟩

/-- Convenience constructor from old bundled `TraceCharacterData`, an orbit
enumeration, and the two-copy-`38` adjacent-moved witness. -/
noncomputable def ofTraceCharacterData
    (h : D19ActsOnMoore57 V Γ)
    (hold : TraceCharacterData Γ h.rotation h.a1)
    (orbitBase : OrbitBaseSelectionEnumeration h)
    (adjacentMoved :
      AdjacentMovedTwoCopyPartition38Witness h orbitBase.base) :
    D19ConstructiveFinalInputs h where
  character := D19FinalCharacterInputs.ofTraceCharacterData h hold
  orbitBase := orbitBase
  adjacentMoved := adjacentMoved

/-- Constructor from a final character input, an embedding-valued orbit
enumeration, and the matching two-copy-`38` witness. -/
noncomputable def ofEmbedding
    (character : D19FinalCharacterInputs h)
    (orbitBase : OrbitBaseSelectionEmbeddingWitness h)
    (adjacentMoved :
      AdjacentMovedTwoCopyPartition38Witness h orbitBase.base) :
    D19ConstructiveFinalInputs h where
  character := character
  orbitBase := orbitBase.toEnumeration
  adjacentMoved := by
    simpa [OrbitBaseSelectionEmbeddingWitness.toEnumeration] using
      adjacentMoved

/-- Convert a subtype-equivalence orbit witness into the enumeration form used
by `D19ConstructiveFinalInputs`. -/
noncomputable def enumerationOfSubtypeEquiv
    (orbitBase : OrbitBaseSelectionSubtypeEquivWitness h) :
    OrbitBaseSelectionEnumeration h where
  base := orbitBase.base
  coord := fun qi => orbitBase.coordEquiv qi
  coord_eq_rotation := orbitBase.coord_eq_rotation
  coord_injective := by
    intro qi qj heq
    apply orbitBase.coordEquiv.injective
    apply Subtype.ext
    exact heq

/-- Constructor from a final character input, a subtype-equivalence orbit
enumeration, and the matching two-copy-`38` witness. -/
noncomputable def ofSubtypeEquiv
    (character : D19FinalCharacterInputs h)
    (orbitBase : OrbitBaseSelectionSubtypeEquivWitness h)
    (adjacentMoved :
      AdjacentMovedTwoCopyPartition38Witness h orbitBase.base) :
    D19ConstructiveFinalInputs h where
  character := character
  orbitBase := enumerationOfSubtypeEquiv orbitBase
  adjacentMoved := by
    simpa [enumerationOfSubtypeEquiv] using
      adjacentMoved

/-- Old bundled `TraceCharacterData` plus an embedding-valued orbit
enumeration gives constructive final inputs. -/
noncomputable def ofTraceCharacterDataEmbedding
    (h : D19ActsOnMoore57 V Γ)
    (hold : TraceCharacterData Γ h.rotation h.a1)
    (orbitBase : OrbitBaseSelectionEmbeddingWitness h)
    (adjacentMoved :
      AdjacentMovedTwoCopyPartition38Witness h orbitBase.base) :
    D19ConstructiveFinalInputs h :=
  ofEmbedding (D19FinalCharacterInputs.ofTraceCharacterData h hold)
    orbitBase adjacentMoved

/-- Old bundled `TraceCharacterData` plus a subtype-equivalence orbit
enumeration gives constructive final inputs. -/
noncomputable def ofTraceCharacterDataSubtypeEquiv
    (h : D19ActsOnMoore57 V Γ)
    (hold : TraceCharacterData Γ h.rotation h.a1)
    (orbitBase : OrbitBaseSelectionSubtypeEquivWitness h)
    (adjacentMoved :
      AdjacentMovedTwoCopyPartition38Witness h orbitBase.base) :
    D19ConstructiveFinalInputs h :=
  ofSubtypeEquiv (D19FinalCharacterInputs.ofTraceCharacterData h hold)
    orbitBase adjacentMoved

end D19ConstructiveFinalInputs

end Moore57
