import Moore57.D19Contradiction
import Moore57.Foundations.GroupAction.FixedPoints

namespace Moore57

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
