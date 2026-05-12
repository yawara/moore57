import Moore57.D19OnMoore57.Orbit.BaseSelectionCriteria

/-!
# Enumeration criteria for selecting the 56 rotation-orbit bases

This file gives higher-level constructors for `OrbitBaseSelectionWitness`.
Instead of proving injectivity of the concrete orbit-coordinate map directly,
one may provide a separate enumeration, an embedding, or a bijection with a
subtype of vertices, together with the statement that it agrees with the
rotation-coordinate map.
-/

namespace Moore57

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- A coordinate enumeration of the selected rotation orbits.

The map `coord` is allowed to be any injective enumeration, as long as it agrees
pointwise with `(q, i) ↦ h.rotation i (base q)`. -/
structure OrbitBaseSelectionEnumeration (h : D19ActsOnMoore57 V Γ) where
  /-- One representative for each of the 56 rotation orbits. -/
  base : Fin 56 → V
  /-- The enumerating map for the `56 * 19` orbit coordinates. -/
  coord : Fin 56 × ZMod 19 → V
  /-- The enumeration agrees with the rotation-coordinate map. -/
  coord_eq_rotation :
    ∀ qi : Fin 56 × ZMod 19, coord qi = h.rotation qi.2 (base qi.1)
  /-- The enumeration has no repeated vertex. -/
  coord_injective : Function.Injective coord

namespace OrbitBaseSelectionEnumeration

variable {h : D19ActsOnMoore57 V Γ}

/-- The coordinate enumeration proves injectivity of the concrete
rotation-coordinate map required by `OrbitBaseSelectionWitness`. -/
theorem orbitCoordinate_injective (w : OrbitBaseSelectionEnumeration h) :
    Function.Injective
      (fun qi : Fin 56 × ZMod 19 => h.rotation qi.2 (w.base qi.1)) := by
  intro qi qj heq
  apply w.coord_injective
  calc
    w.coord qi = h.rotation qi.2 (w.base qi.1) := w.coord_eq_rotation qi
    _ = h.rotation qj.2 (w.base qj.1) := heq
    _ = w.coord qj := (w.coord_eq_rotation qj).symm

/-- Convert a coordinate enumeration into the existing base-selection witness. -/
noncomputable def toWitness
    (w : OrbitBaseSelectionEnumeration h) :
    OrbitBaseSelectionWitness h :=
  OrbitBaseSelectionWitness.ofOrbitCoordinateInjective
    w.base w.orbitCoordinate_injective

/-- Convert a coordinate enumeration directly into the downstream input. -/
noncomputable def toInput
    (w : OrbitBaseSelectionEnumeration h) :
    OrbitBaseSelectionInput h :=
  w.toWitness.toInput

/-- The selected orbit-family union has cardinality `1064`. -/
theorem orbitFamilyUnion_card (w : OrbitBaseSelectionEnumeration h) :
    (h.orbitFamilyUnion w.base).card = 1064 :=
  w.toWitness.orbitFamilyUnion_card

/-- The downstream input produced from the enumeration has orbit-union
cardinality `1064`. -/
theorem input_orbitFamilyUnion_card (w : OrbitBaseSelectionEnumeration h) :
    w.toInput.orbitFamilyUnion.card = 1064 :=
  w.toInput.orbitFamilyUnion_card

end OrbitBaseSelectionEnumeration

/-- An embedding-valued coordinate witness for the selected rotation orbits. -/
structure OrbitBaseSelectionEmbeddingWitness (h : D19ActsOnMoore57 V Γ) where
  /-- One representative for each of the 56 rotation orbits. -/
  base : Fin 56 → V
  /-- An embedded copy of the orbit-coordinate type inside the vertex type. -/
  embedding : Fin 56 × ZMod 19 ↪ V
  /-- The embedding agrees with the rotation-coordinate map. -/
  embedding_eq_rotation :
    ∀ qi : Fin 56 × ZMod 19, embedding qi = h.rotation qi.2 (base qi.1)

namespace OrbitBaseSelectionEmbeddingWitness

variable {h : D19ActsOnMoore57 V Γ}

/-- An embedding witness is a coordinate enumeration. -/
noncomputable def toEnumeration
    (w : OrbitBaseSelectionEmbeddingWitness h) :
    OrbitBaseSelectionEnumeration h where
  base := w.base
  coord := w.embedding
  coord_eq_rotation := w.embedding_eq_rotation
  coord_injective := w.embedding.injective

/-- Convert an embedding witness into the existing base-selection witness. -/
noncomputable def toWitness
    (w : OrbitBaseSelectionEmbeddingWitness h) :
    OrbitBaseSelectionWitness h :=
  w.toEnumeration.toWitness

/-- Convert an embedding witness directly into the downstream input. -/
noncomputable def toInput
    (w : OrbitBaseSelectionEmbeddingWitness h) :
    OrbitBaseSelectionInput h :=
  w.toWitness.toInput

/-- The selected orbit-family union has cardinality `1064`. -/
theorem orbitFamilyUnion_card (w : OrbitBaseSelectionEmbeddingWitness h) :
    (h.orbitFamilyUnion w.base).card = 1064 :=
  w.toWitness.orbitFamilyUnion_card

end OrbitBaseSelectionEmbeddingWitness

/-- A bijection from orbit coordinates to a vertex subtype witnessing the
selected rotation orbits.

This is useful when the `56 * 19` vertices have first been isolated as a set
and the coordinate construction is naturally an equivalence with that subtype. -/
structure OrbitBaseSelectionSubtypeEquivWitness (h : D19ActsOnMoore57 V Γ) where
  /-- One representative for each of the 56 rotation orbits. -/
  base : Fin 56 → V
  /-- The vertex set covered by the coordinates. -/
  carrier : Set V
  /-- A bijection from orbit coordinates to the carrier subtype. -/
  coordEquiv : Fin 56 × ZMod 19 ≃ carrier
  /-- The bijection agrees with the rotation-coordinate map after coercion to
  vertices. -/
  coord_eq_rotation :
    ∀ qi : Fin 56 × ZMod 19,
      (coordEquiv qi : V) = h.rotation qi.2 (base qi.1)

namespace OrbitBaseSelectionSubtypeEquivWitness

variable {h : D19ActsOnMoore57 V Γ}

/-- A subtype-equivalence witness proves injectivity of the concrete
rotation-coordinate map. -/
theorem orbitCoordinate_injective
    (w : OrbitBaseSelectionSubtypeEquivWitness h) :
    Function.Injective
      (fun qi : Fin 56 × ZMod 19 => h.rotation qi.2 (w.base qi.1)) := by
  intro qi qj heq
  apply w.coordEquiv.injective
  apply Subtype.ext
  calc
    (w.coordEquiv qi : V) = h.rotation qi.2 (w.base qi.1) :=
      w.coord_eq_rotation qi
    _ = h.rotation qj.2 (w.base qj.1) := heq
    _ = (w.coordEquiv qj : V) := (w.coord_eq_rotation qj).symm

/-- Convert a subtype-equivalence witness into the existing base-selection
witness. -/
noncomputable def toWitness
    (w : OrbitBaseSelectionSubtypeEquivWitness h) :
    OrbitBaseSelectionWitness h :=
  OrbitBaseSelectionWitness.ofOrbitCoordinateInjective
    w.base w.orbitCoordinate_injective

/-- Convert a subtype-equivalence witness directly into the downstream input. -/
noncomputable def toInput
    (w : OrbitBaseSelectionSubtypeEquivWitness h) :
    OrbitBaseSelectionInput h :=
  w.toWitness.toInput

/-- The selected orbit-family union has cardinality `1064`. -/
theorem orbitFamilyUnion_card
    (w : OrbitBaseSelectionSubtypeEquivWitness h) :
    (h.orbitFamilyUnion w.base).card = 1064 :=
  w.toWitness.orbitFamilyUnion_card

end OrbitBaseSelectionSubtypeEquivWitness

namespace OrbitBaseSelectionWitness

variable {h : D19ActsOnMoore57 V Γ}

/-- Build a base-selection witness from an injective coordinate enumeration
that agrees with the rotation-coordinate map. -/
noncomputable def ofEnumeration
    (w : OrbitBaseSelectionEnumeration h) :
    OrbitBaseSelectionWitness h :=
  w.toWitness

/-- Build a base-selection witness from an embedding-valued coordinate
enumeration. -/
noncomputable def ofEmbedding
    (w : OrbitBaseSelectionEmbeddingWitness h) :
    OrbitBaseSelectionWitness h :=
  w.toWitness

/-- Build a base-selection witness from a bijection with a vertex subtype. -/
noncomputable def ofSubtypeEquiv
    (w : OrbitBaseSelectionSubtypeEquivWitness h) :
    OrbitBaseSelectionWitness h :=
  w.toWitness

end OrbitBaseSelectionWitness

namespace OrbitBaseSelectionInput

variable {h : D19ActsOnMoore57 V Γ}

/-- Build the downstream base-selection input from an injective coordinate
enumeration that agrees with the rotation-coordinate map. -/
noncomputable def ofEnumeration
    (w : OrbitBaseSelectionEnumeration h) :
    OrbitBaseSelectionInput h :=
  w.toInput

/-- Build the downstream base-selection input from an embedding-valued
coordinate enumeration. -/
noncomputable def ofEmbedding
    (w : OrbitBaseSelectionEmbeddingWitness h) :
    OrbitBaseSelectionInput h :=
  w.toInput

/-- Build the downstream base-selection input from a bijection with a vertex
subtype. -/
noncomputable def ofSubtypeEquiv
    (w : OrbitBaseSelectionSubtypeEquivWitness h) :
    OrbitBaseSelectionInput h :=
  w.toInput

end OrbitBaseSelectionInput

end Moore57
