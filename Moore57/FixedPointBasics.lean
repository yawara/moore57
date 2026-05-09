import Moore57.D19Contradiction

namespace Moore57

/-- The set of fixed vertices of a permutation. -/
noncomputable def fixedVertexSet {V : Type*} (σ : Equiv.Perm V) : Set V :=
  {v | σ v = v}

instance fixedVertexSet.fintype {V : Type*} [Fintype V] [DecidableEq V]
    (σ : Equiv.Perm V) : Fintype (fixedVertexSet σ) := by
  dsimp [fixedVertexSet]
  infer_instance

@[simp] theorem mem_fixedVertexSet {V : Type*} {σ : Equiv.Perm V} {v : V} :
    v ∈ fixedVertexSet σ ↔ σ v = v := by
  rfl

@[simp] theorem fixedVertexSet_one {V : Type*} :
    fixedVertexSet (1 : Equiv.Perm V) = Set.univ := by
  ext v
  simp [fixedVertexSet]

theorem fixedVertexSet_toFinset_eq_filter
    {V : Type*} [Fintype V] [DecidableEq V] (σ : Equiv.Perm V) :
    (fixedVertexSet σ).toFinset =
      (Finset.univ : Finset V).filter (fun v => σ v = v) := by
  classical
  ext v
  simp [fixedVertexSet]

/-- The earlier fixed-point count is the cardinality of the fixed-point set. -/
theorem fixedVertexCount_eq_card_fixedVertexSet
    {V : Type*} [Fintype V] [DecidableEq V] (σ : Equiv.Perm V) :
    fixedVertexCount σ = Fintype.card (fixedVertexSet σ) := by
  classical
  rw [← Set.toFinset_card, fixedVertexSet_toFinset_eq_filter]
  rfl

theorem fixedVertexSet_eq_support_compl
    {V : Type*} [Fintype V] [DecidableEq V] (σ : Equiv.Perm V) :
    fixedVertexSet σ = (σ.supportᶜ : Set V) := by
  ext v
  simp [fixedVertexSet, Equiv.Perm.support]

namespace D19ActsOnMoore57

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

@[simp] theorem fixedVertexSet_rotation_zero (h : D19ActsOnMoore57 V Γ) :
    fixedVertexSet (h.rotation 0) = Set.univ := by
  simp

theorem card_fixedVertexSet_rotation_modEq_card
    (h : D19ActsOnMoore57 V Γ) (d : ZMod 19) :
    Fintype.card V ≡ Fintype.card (fixedVertexSet (h.rotation d)) [MOD 19] := by
  simpa [fixedVertexCount_eq_card_fixedVertexSet] using
    h.fixedVertexCount_rotation_modEq_card d

theorem card_fixedVertexSet_rotation_modEq_one
    (h : D19ActsOnMoore57 V Γ) (d : ZMod 19) :
    Fintype.card (fixedVertexSet (h.rotation d)) ≡ 1 [MOD 19] := by
  simpa [fixedVertexCount_eq_card_fixedVertexSet] using
    h.fixedVertexCount_rotation_modEq_one d

theorem card_fixedVertexSet_rotation_pos
    (h : D19ActsOnMoore57 V Γ) (d : ZMod 19) :
    0 < Fintype.card (fixedVertexSet (h.rotation d)) := by
  simpa [fixedVertexCount_eq_card_fixedVertexSet] using
    h.fixedVertexCount_rotation_pos d

theorem card_fixedVertexSet_rotation_lt_card
    (h : D19ActsOnMoore57 V Γ) {d : ZMod 19} (hd : d ≠ 0) :
    Fintype.card (fixedVertexSet (h.rotation d)) < Fintype.card V := by
  simpa [fixedVertexCount_eq_card_fixedVertexSet] using
    h.fixedVertexCount_rotation_lt_card hd

end D19ActsOnMoore57

end Moore57
