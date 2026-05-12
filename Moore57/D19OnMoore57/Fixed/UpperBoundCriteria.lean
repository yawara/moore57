import Moore57.D19OnMoore57.Rotation.FixedUpperBoundInputs
import Moore57.D19OnMoore57.Fixed.InducedSubgraph

/-!
# Practical criteria for the rotation-one fixed-vertex upper bound

This file packages common finite-cardinality witnesses for the remaining input
`fixedVertexCount (h.rotation 1) ≤ 19`.
-/

namespace Moore57

namespace D19ActsOnMoore57

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- A generic cardinal bound from an injective map into a finite type of
cardinality at most `n`. -/
theorem fintype_card_le_of_injective_to_bounded
    {α ι : Type*} [Fintype α] [Fintype ι] {n : ℕ}
    (f : α → ι) (hf : Function.Injective f) (hι : Fintype.card ι ≤ n) :
    Fintype.card α ≤ n :=
  (Fintype.card_le_of_injective f hf).trans hι

/-- A subtype of `Fin n` has cardinality at most `n`. -/
theorem fintype_card_subtype_fin_le
    {n : ℕ} (p : Fin n → Prop) [Fintype {i : Fin n // p i}] :
    Fintype.card {i : Fin n // p i} ≤ n := by
  simpa using Fintype.card_subtype_le p

/-- An injective classification of rotation-one fixed vertices by `Fin 19`
gives the desired upper bound. -/
theorem fixedVertexCount_rotation_one_le_nineteen_of_injective
    (h : D19ActsOnMoore57 V Γ)
    (f : fixedVertexSet (h.rotation 1) → Fin 19)
    (hf : Function.Injective f) :
    fixedVertexCount (h.rotation 1) ≤ 19 := by
  rw [fixedVertexCount_eq_card_fixedVertexSet]
  exact Fintype.card_le_of_injective f hf

/-- An equivalence from rotation-one fixed vertices to any subtype of `Fin 19`
gives the desired upper bound. -/
theorem fixedVertexCount_rotation_one_le_nineteen_of_equiv_subtype_fin
    (h : D19ActsOnMoore57 V Γ)
    {p : Fin 19 → Prop} [Fintype {i : Fin 19 // p i}]
    (e : fixedVertexSet (h.rotation 1) ≃ {i : Fin 19 // p i}) :
    fixedVertexCount (h.rotation 1) ≤ 19 := by
  rw [fixedVertexCount_eq_card_fixedVertexSet]
  exact (Fintype.card_congr e).le.trans (fintype_card_subtype_fin_le p)

/-- An equivalence from rotation-one fixed vertices to a finite set-indexed
subtype of `Fin 19` gives the desired upper bound. -/
theorem fixedVertexCount_rotation_one_le_nineteen_of_equiv_set_fin
    (h : D19ActsOnMoore57 V Γ)
    (s : Set (Fin 19)) [Fintype s]
    (e : fixedVertexSet (h.rotation 1) ≃ s) :
    fixedVertexCount (h.rotation 1) ≤ 19 := by
  rw [fixedVertexCount_eq_card_fixedVertexSet]
  exact (Fintype.card_congr e).le.trans (set_fintype_card_le_univ s)

/-- A reusable witness that rotation-one fixed vertices inject into some finite
type of cardinality at most nineteen. -/
structure RotationOneFixedBoundWitness (h : D19ActsOnMoore57 V Γ) where
  /-- The finite indexing type used by a classification of fixed vertices. -/
  ι : Type*
  /-- The indexing type is finite. -/
  fintype_ι : Fintype ι
  /-- The indexing type has at most nineteen elements. -/
  card_le_nineteen : Fintype.card ι ≤ 19
  /-- The classified/factored map from rotation-one fixed vertices. -/
  fixedEmbedding : fixedVertexSet (h.rotation 1) ↪ ι

namespace RotationOneFixedBoundWitness

variable {h : D19ActsOnMoore57 V Γ}

/-- The witness implies the rotation-one fixed-count upper bound. -/
theorem fixedVertexCount_rotation_one_le_nineteen
    (w : RotationOneFixedBoundWitness h) :
    fixedVertexCount (h.rotation 1) ≤ 19 := by
  classical
  rw [fixedVertexCount_eq_card_fixedVertexSet]
  letI := w.fintype_ι
  exact (Fintype.card_le_of_embedding w.fixedEmbedding).trans w.card_le_nineteen

/-- Convert a rotation-one finite classification witness into the existing
upper-bound input for all nontrivial rotations. -/
def toRotationFixedUpperBoundInput
    (w : RotationOneFixedBoundWitness h) :
    RotationFixedUpperBoundInput h :=
  RotationFixedUpperBoundInput.of_rotation_one_le_nineteen
    w.fixedVertexCount_rotation_one_le_nineteen

end RotationOneFixedBoundWitness

/-- Build the existing upper-bound input directly from an injective
classification by `Fin 19`. -/
def RotationFixedUpperBoundInput.of_rotation_one_injective_fin
    (h : D19ActsOnMoore57 V Γ)
    (f : fixedVertexSet (h.rotation 1) → Fin 19)
    (hf : Function.Injective f) :
    RotationFixedUpperBoundInput h :=
  RotationFixedUpperBoundInput.of_rotation_one_le_nineteen
    (h.fixedVertexCount_rotation_one_le_nineteen_of_injective f hf)

/-- Build the existing upper-bound input directly from an equivalence with a
subtype of `Fin 19`. -/
def RotationFixedUpperBoundInput.of_rotation_one_equiv_subtype_fin
    (h : D19ActsOnMoore57 V Γ)
    {p : Fin 19 → Prop} [Fintype {i : Fin 19 // p i}]
    (e : fixedVertexSet (h.rotation 1) ≃ {i : Fin 19 // p i}) :
    RotationFixedUpperBoundInput h :=
  RotationFixedUpperBoundInput.of_rotation_one_le_nineteen
    (h.fixedVertexCount_rotation_one_le_nineteen_of_equiv_subtype_fin e)

end D19ActsOnMoore57

end Moore57
