import Moore57.FixedUpperBoundEnumeration
import Mathlib.Data.Set.Subsingleton

/-!
# Unique fixed-point criteria for rotation fixed upper bounds

This file packages the common case where rotation by `1` has at most one, or
exactly one, fixed vertex.  The upper-bound input then follows by classifying
the fixed vertices by `PUnit`.
-/

namespace Moore57

namespace D19ActsOnMoore57

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- If the rotation-one fixed set is a subsingleton, then it has cardinality at
most one. -/
theorem fixedVertexCount_rotation_one_le_one_of_fixedVertexSet_subsingleton
    (h : D19ActsOnMoore57 V Γ)
    (hss : (fixedVertexSet (h.rotation 1)).Subsingleton) :
    fixedVertexCount (h.rotation 1) ≤ 1 := by
  rw [fixedVertexCount_eq_card_fixedVertexSet]
  exact Fintype.card_le_one_iff_subsingleton.mpr
    ((Set.subsingleton_coe _).mpr hss)

/-- If the rotation-one fixed set is a subsingleton, then the D19 fixed upper
bound `≤ 19` follows. -/
theorem fixedVertexCount_rotation_one_le_nineteen_of_fixedVertexSet_subsingleton
    (h : D19ActsOnMoore57 V Γ)
    (hss : (fixedVertexSet (h.rotation 1)).Subsingleton) :
    fixedVertexCount (h.rotation 1) ≤ 19 :=
  (h.fixedVertexCount_rotation_one_le_one_of_fixedVertexSet_subsingleton hss).trans
    (by decide)

/-- A singleton description of the rotation-one fixed set gives exact fixed
count `1`. -/
theorem fixedVertexCount_rotation_one_eq_one_of_fixedVertexSet_eq_singleton
    (h : D19ActsOnMoore57 V Γ)
    {v0 : V}
    (hset : fixedVertexSet (h.rotation 1) = ({v0} : Set V)) :
  fixedVertexCount (h.rotation 1) = 1 := by
  classical
  rw [fixedVertexCount_eq_card_fixedVertexSet]
  simp [hset]

/-- A singleton description of the rotation-one fixed set gives the fixed
upper bound `≤ 19`. -/
theorem fixedVertexCount_rotation_one_le_nineteen_of_fixedVertexSet_eq_singleton
    (h : D19ActsOnMoore57 V Γ)
    {v0 : V}
    (hset : fixedVertexSet (h.rotation 1) = ({v0} : Set V)) :
    fixedVertexCount (h.rotation 1) ≤ 19 := by
  rw [h.fixedVertexCount_rotation_one_eq_one_of_fixedVertexSet_eq_singleton hset]
  decide

/-- A unique fixed point for rotation by `1` identifies the fixed set with a
singleton. -/
theorem exists_fixedVertexSet_rotation_one_eq_singleton_of_existsUnique
    (h : D19ActsOnMoore57 V Γ)
    (hunique : ∃! v : V, h.rotation 1 v = v) :
    ∃ v0 : V, fixedVertexSet (h.rotation 1) = ({v0} : Set V) := by
  rcases hunique with ⟨v0, hv0, huniq⟩
  refine ⟨v0, ?_⟩
  rw [Set.eq_singleton_iff_unique_mem]
  exact ⟨by simpa using hv0, fun v hv => huniq v (by simpa using hv)⟩

/-- A unique fixed point for rotation by `1` gives exact fixed count `1`. -/
theorem fixedVertexCount_rotation_one_eq_one_of_existsUnique
    (h : D19ActsOnMoore57 V Γ)
    (hunique : ∃! v : V, h.rotation 1 v = v) :
    fixedVertexCount (h.rotation 1) = 1 := by
  rcases h.exists_fixedVertexSet_rotation_one_eq_singleton_of_existsUnique hunique with
    ⟨v0, hset⟩
  exact h.fixedVertexCount_rotation_one_eq_one_of_fixedVertexSet_eq_singleton
    (v0 := v0) hset

/-- A unique fixed point for rotation by `1` gives the fixed upper bound
`≤ 19`. -/
theorem fixedVertexCount_rotation_one_le_nineteen_of_existsUnique
    (h : D19ActsOnMoore57 V Γ)
    (hunique : ∃! v : V, h.rotation 1 v = v) :
    fixedVertexCount (h.rotation 1) ≤ 19 := by
  rw [h.fixedVertexCount_rotation_one_eq_one_of_existsUnique hunique]
  decide

namespace RotationOneFixedBoundWitness

variable {h : D19ActsOnMoore57 V Γ}

/-- A subsingleton rotation-one fixed set gives the generic fixed-bound
witness, by embedding the fixed vertices into `PUnit`. -/
def of_rotation_one_fixedVertexSet_subsingleton
    (hss : (fixedVertexSet (h.rotation 1)).Subsingleton) :
    RotationOneFixedBoundWitness h where
  ι := PUnit.{1}
  fintype_ι := inferInstance
  card_le_nineteen := by
    rw [Fintype.card_punit]
    decide
  fixedEmbedding := {
    toFun _ := PUnit.unit
    inj' := by
      intro x y _
      exact Subtype.ext (hss x.2 y.2)
  }

/-- A singleton rotation-one fixed set gives the generic fixed-bound witness. -/
def of_rotation_one_fixedVertexSet_eq_singleton
    {v0 : V}
    (hset : fixedVertexSet (h.rotation 1) = ({v0} : Set V)) :
    RotationOneFixedBoundWitness h :=
  of_rotation_one_fixedVertexSet_subsingleton
    (by
      rw [hset]
      exact Set.subsingleton_singleton)

/-- A unique rotation-one fixed point gives the generic fixed-bound witness. -/
def of_existsUnique_rotation_one_fixed
    (hunique : ∃! v : V, h.rotation 1 v = v) :
    RotationOneFixedBoundWitness h :=
  of_rotation_one_fixedVertexSet_subsingleton
    (by
      rcases hunique with ⟨v0, _hv0, huniq⟩
      exact Set.subsingleton_of_forall_eq v0
        (fun v hv => huniq v (by simpa using hv)))

end RotationOneFixedBoundWitness

namespace RotationFixedUpperBoundInput

/-- Build the fixed upper-bound input from a subsingleton rotation-one fixed
set. -/
def of_rotation_one_fixedVertexSet_subsingleton
    (h : D19ActsOnMoore57 V Γ)
    (hss : (fixedVertexSet (h.rotation 1)).Subsingleton) :
    RotationFixedUpperBoundInput h :=
  (RotationOneFixedBoundWitness.of_rotation_one_fixedVertexSet_subsingleton
    (h := h) hss).toRotationFixedUpperBoundInput

/-- Build the fixed upper-bound input from a singleton rotation-one fixed set. -/
def of_rotation_one_fixedVertexSet_eq_singleton
    (h : D19ActsOnMoore57 V Γ)
    {v0 : V}
    (hset : fixedVertexSet (h.rotation 1) = ({v0} : Set V)) :
    RotationFixedUpperBoundInput h :=
  (RotationOneFixedBoundWitness.of_rotation_one_fixedVertexSet_eq_singleton
    (h := h) hset).toRotationFixedUpperBoundInput

/-- Build the fixed upper-bound input from a unique rotation-one fixed point. -/
def of_existsUnique_rotation_one_fixed
    (h : D19ActsOnMoore57 V Γ)
    (hunique : ∃! v : V, h.rotation 1 v = v) :
    RotationFixedUpperBoundInput h :=
  (RotationOneFixedBoundWitness.of_existsUnique_rotation_one_fixed
    (h := h) hunique).toRotationFixedUpperBoundInput

end RotationFixedUpperBoundInput

end D19ActsOnMoore57

end Moore57
