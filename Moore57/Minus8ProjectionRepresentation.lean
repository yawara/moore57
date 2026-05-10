import Moore57.E7ProjectionCharacterBridge

/-!
# The complementary `(-8)` projection representation

This file constructs the complementary projection

`I - E57 - E7`

where `E57` is the rank-one all-ones projection.  The representation and trace
bridge follow the same pattern as the `E7` projection files.
-/

namespace Moore57

section HigmanTrace

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The rank-one projection onto the constant vectors. -/
noncomputable def E57Matrix (V : Type*) [Fintype V] : Matrix V V ℚ :=
  (1 / 3250 : ℚ) • allOnesMatrix V

/-- The complementary `(-8)` projection matrix `I - E57 - E7`. -/
noncomputable def minus8Matrix
    (Γ : SimpleGraph V) [DecidableRel Γ.Adj] : Matrix V V ℚ :=
  1 - E57Matrix V - E7Matrix Γ

omit [DecidableEq V] in
theorem E57Matrix_mul_E57Matrix_eq_E57Matrix
    {Γ : SimpleGraph V} [DecidableRel Γ.Adj] (hΓ : IsMoore57 Γ) :
    E57Matrix V * E57Matrix V = E57Matrix V := by
  rw [E57Matrix, Matrix.smul_mul, Matrix.mul_smul,
    allOnesMatrix_mul_allOnesMatrix_of_moore hΓ]
  ext v w
  simp [allOnesMatrix]

omit [DecidableEq V] in
theorem E57Matrix_isIdempotentElem
    {Γ : SimpleGraph V} [DecidableRel Γ.Adj] (hΓ : IsMoore57 Γ) :
    IsIdempotentElem (E57Matrix V) := by
  exact E57Matrix_mul_E57Matrix_eq_E57Matrix hΓ

/-- The rank-one all-ones projection commutes with every permutation matrix. -/
theorem E57Matrix_mul_permMatrix_eq_permMatrix_mul_E57Matrix
    (σ : Equiv.Perm V) :
    E57Matrix V * permMatrix σ = permMatrix σ * E57Matrix V := by
  rw [E57Matrix, Matrix.smul_mul, Matrix.mul_smul,
    allOnesMatrix_mul_permMatrix_eq_permMatrix_mul_allOnesMatrix σ]

/-- The `E57` and `E7` projections are orthogonal in this order. -/
theorem E57Matrix_mul_E7Matrix_eq_zero
    {Γ : SimpleGraph V} [DecidableRel Γ.Adj] (hΓ : IsMoore57 Γ) :
    E57Matrix V * E7Matrix Γ = 0 := by
  classical
  rw [E57Matrix, E7Matrix]
  simp only [Matrix.smul_mul, Matrix.mul_sub, Matrix.mul_add, Matrix.mul_smul,
    Matrix.mul_one]
  rw [allOnesMatrix_mul_adjMatrix hΓ, allOnesMatrix_mul_allOnesMatrix_of_moore hΓ]
  ext v w
  simp [allOnesMatrix]
  ring

/-- The `E57` and `E7` projections are orthogonal in the opposite order. -/
theorem E7Matrix_mul_E57Matrix_eq_zero
    {Γ : SimpleGraph V} [DecidableRel Γ.Adj] (hΓ : IsMoore57 Γ) :
    E7Matrix Γ * E57Matrix V = 0 := by
  classical
  rw [E57Matrix, E7Matrix]
  simp only [Matrix.mul_smul, Matrix.sub_mul, Matrix.add_mul, Matrix.smul_mul,
    Matrix.one_mul]
  rw [adjMatrix_mul_allOnesMatrix hΓ, allOnesMatrix_mul_allOnesMatrix_of_moore hΓ]
  ext v w
  simp [allOnesMatrix]
  ring

/-- The complementary `(-8)` matrix is idempotent. -/
theorem minus8Matrix_mul_minus8Matrix_eq_minus8Matrix
    {Γ : SimpleGraph V} [DecidableRel Γ.Adj] (hΓ : IsMoore57 Γ) :
    minus8Matrix Γ * minus8Matrix Γ = minus8Matrix Γ := by
  classical
  have h57 : E57Matrix V * E57Matrix V = E57Matrix V :=
    E57Matrix_mul_E57Matrix_eq_E57Matrix hΓ
  have h7 : E7Matrix Γ * E7Matrix Γ = E7Matrix Γ :=
    E7Matrix_mul_E7Matrix_eq_E7Matrix hΓ
  have h577 : E57Matrix V * E7Matrix Γ = 0 :=
    E57Matrix_mul_E7Matrix_eq_zero hΓ
  have h757 : E7Matrix Γ * E57Matrix V = 0 :=
    E7Matrix_mul_E57Matrix_eq_zero hΓ
  rw [minus8Matrix]
  ext v w
  simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one,
    Matrix.sub_apply]
  rw [show (E57Matrix V * E57Matrix V) v w = E57Matrix V v w by
      exact congrFun (congrFun h57 v) w,
    show (E7Matrix Γ * E7Matrix Γ) v w = E7Matrix Γ v w by
      exact congrFun (congrFun h7 v) w,
    show (E57Matrix V * E7Matrix Γ) v w = 0 by
      exact congrFun (congrFun h577 v) w,
    show (E7Matrix Γ * E57Matrix V) v w = 0 by
      exact congrFun (congrFun h757 v) w]
  ring

theorem minus8Matrix_isIdempotentElem
    {Γ : SimpleGraph V} [DecidableRel Γ.Adj] (hΓ : IsMoore57 Γ) :
    IsIdempotentElem (minus8Matrix Γ) := by
  exact minus8Matrix_mul_minus8Matrix_eq_minus8Matrix hΓ

/-- The complementary `(-8)` projection commutes with every graph automorphism. -/
theorem minus8Matrix_mul_permMatrix_eq_permMatrix_mul_minus8Matrix
    (Γ : SimpleGraph V) [DecidableRel Γ.Adj] (σ : Equiv.Perm V)
    (haut : ∀ v w, Γ.Adj v w ↔ Γ.Adj (σ v) (σ w)) :
    minus8Matrix Γ * permMatrix σ = permMatrix σ * minus8Matrix Γ := by
  classical
  simp [minus8Matrix, Matrix.sub_mul, Matrix.mul_sub,
    E57Matrix_mul_permMatrix_eq_permMatrix_mul_E57Matrix σ,
    E7Matrix_mul_permMatrix_eq_permMatrix_mul_E7Matrix Γ σ haut]

/-- Matrix commutation for `minus8Matrix`, transported through `Matrix.toLin'`. -/
theorem minus8Matrix_toLin'_commute_permMatrix_toLin'
    (Γ : SimpleGraph V) [DecidableRel Γ.Adj] (σ : Equiv.Perm V)
    (haut : ∀ v w, Γ.Adj v w ↔ Γ.Adj (σ v) (σ w)) :
    Commute (minus8Matrix Γ).toLin' (permMatrix σ).toLin' :=
  toLin'_commute_of_mul_eq
    (minus8Matrix_mul_permMatrix_eq_permMatrix_mul_minus8Matrix Γ σ haut)

theorem minus8Matrix_toLin'_isIdempotentElem
    {Γ : SimpleGraph V} [DecidableRel Γ.Adj] (hΓ : IsMoore57 Γ) :
    IsIdempotentElem (minus8Matrix Γ).toLin' := by
  rw [IsIdempotentElem, Module.End.mul_eq_comp, ← matrix_toLin'_mul,
    minus8Matrix_mul_minus8Matrix_eq_minus8Matrix hΓ]

/-- `trace(E57 * P_σ) = 1` for Moore57 graphs. -/
theorem trace_E57Matrix_mul_permMatrix_eq_one
    {Γ : SimpleGraph V} [DecidableRel Γ.Adj] (hΓ : IsMoore57 Γ)
    (σ : Equiv.Perm V) :
    Matrix.trace (E57Matrix V * permMatrix σ) = 1 := by
  rw [E57Matrix, Matrix.smul_mul, Matrix.trace_smul,
    trace_allOnes_mul_permMatrix σ, hΓ.card]
  norm_num

/-- Matrix trace of the `(-8)` projection followed by a permutation matrix. -/
theorem trace_minus8Matrix_mul_permMatrix_eq
    {Γ : SimpleGraph V} [DecidableRel Γ.Adj] (hΓ : IsMoore57 Γ)
    (σ : Equiv.Perm V) :
    Matrix.trace (minus8Matrix Γ * permMatrix σ) =
      Matrix.trace (permMatrix σ) - 1 -
        Matrix.trace (E7Matrix Γ * permMatrix σ) := by
  rw [minus8Matrix, Matrix.sub_mul, Matrix.sub_mul, Matrix.one_mul]
  rw [show Matrix.trace
        (permMatrix σ - E57Matrix V * permMatrix σ - E7Matrix Γ * permMatrix σ) =
      Matrix.trace (permMatrix σ) -
        Matrix.trace (E57Matrix V * permMatrix σ) -
          Matrix.trace (E7Matrix Γ * permMatrix σ) by
    simp [Matrix.trace, Finset.sum_sub_distrib]]
  rw [trace_E57Matrix_mul_permMatrix_eq_one hΓ σ]

/-- Restricting a permutation matrix to the range of the `(-8)` projection has
trace equal to the concrete `minus8Matrix` trace. -/
theorem trace_restrict_minus8Range_permMatrix_toLin'_eq_matrix_trace
    {Γ : SimpleGraph V} [DecidableRel Γ.Adj]
    (hΓ : IsMoore57 Γ) (σ : Equiv.Perm V)
    (haut : ∀ v w, Γ.Adj v w ↔ Γ.Adj (σ v) (σ w)) :
    LinearMap.trace ℚ (LinearMap.range (minus8Matrix Γ).toLin')
        ((permMatrix σ).toLin'.restrict (by
          intro x hx
          exact ((Module.End.mem_invtSubmodule_iff_mapsTo
            (f := (permMatrix σ).toLin')).mp
              ((LinearMap.IsIdempotentElem.commute_iff
                (minus8Matrix_toLin'_isIdempotentElem hΓ)
                (T := (permMatrix σ).toLin')).mp
                (minus8Matrix_toLin'_commute_permMatrix_toLin' Γ σ haut)).1) hx)) =
      Matrix.trace (minus8Matrix Γ * permMatrix σ) := by
  have hcomm :
      Commute (minus8Matrix Γ).toLin' (permMatrix σ).toLin' :=
    minus8Matrix_toLin'_commute_permMatrix_toLin' Γ σ haut
  rw [Moore57.LinearMap.trace_restrict_range_eq_trace_comp_of_isIdempotentElem
    (p := (minus8Matrix Γ).toLin') (f := (permMatrix σ).toLin')
    (minus8Matrix_toLin'_isIdempotentElem hΓ) hcomm]
  rw [show (minus8Matrix Γ).toLin' ∘ₗ (permMatrix σ).toLin' =
      (minus8Matrix Γ * permMatrix σ).toLin' by
        rw [matrix_toLin'_mul]]
  exact trace_toLin'_eq_matrix_trace (minus8Matrix Γ * permMatrix σ)

end HigmanTrace

namespace D19ActsOnMoore57

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- The concrete `(-8)` range representation for a `D19ActsOnMoore57` action. -/
noncomputable def minus8ProjectionRepresentation
    (h : D19ActsOnMoore57 V Γ) :
    _root_.Representation ℚ (DihedralGroup 19)
      (_root_.LinearMap.range (minus8Matrix Γ).toLin') :=
  Representation.onCommutingRange h.vertexPermutationMatrixRepresentationOnPi
    (minus8Matrix Γ).toLin' fun g =>
      minus8Matrix_toLin'_commute_permMatrix_toLin' Γ (h.smulEquiv g) <| by
        intro v w
        simpa using h.smul_adj g v w

@[simp]
theorem minus8ProjectionRepresentation_apply_coe
    (h : D19ActsOnMoore57 V Γ) (g : DihedralGroup 19)
    (x : _root_.LinearMap.range (minus8Matrix Γ).toLin') :
    (((h.minus8ProjectionRepresentation) g x :
        _root_.LinearMap.range (minus8Matrix Γ).toLin') : V → ℚ) =
      (permMatrix (h.smulEquiv g)).toLin' x :=
  rfl

/-- D19 specialization of the `(-8)` projection-range trace bridge. -/
theorem trace_restrict_minus8Range_smulEquiv_toLin'_eq_matrix_trace
    (h : D19ActsOnMoore57 V Γ) (g : DihedralGroup 19) :
    LinearMap.trace ℚ (LinearMap.range (minus8Matrix Γ).toLin')
        ((permMatrix (h.smulEquiv g)).toLin'.restrict (by
          intro x hx
          exact ((Module.End.mem_invtSubmodule_iff_mapsTo
            (f := (permMatrix (h.smulEquiv g)).toLin')).mp
              ((LinearMap.IsIdempotentElem.commute_iff
                (minus8Matrix_toLin'_isIdempotentElem h.isMoore)
                (T := (permMatrix (h.smulEquiv g)).toLin')).mp
                (minus8Matrix_toLin'_commute_permMatrix_toLin' Γ (h.smulEquiv g)
                  (by
                    intro v w
                    exact h.smul_adj g v w))).1) hx)) =
      Matrix.trace (minus8Matrix Γ * permMatrix (h.smulEquiv g)) :=
  trace_restrict_minus8Range_permMatrix_toLin'_eq_matrix_trace h.isMoore
    (h.smulEquiv g) (by
      intro v w
      exact h.smul_adj g v w)

/-- The mathlib character of the concrete `(-8)` range representation is the
expected complementary trace. -/
theorem minus8ProjectionRepresentation_character_eq_matrix_trace
    (h : D19ActsOnMoore57 V Γ) (g : DihedralGroup 19) :
    (h.minus8ProjectionRepresentation).character g =
      Matrix.trace (permMatrix (h.smulEquiv g)) - 1 -
        Matrix.trace (E7Matrix Γ * permMatrix (h.smulEquiv g)) := by
  have hmap :
      h.minus8ProjectionRepresentation g =
        (permMatrix (h.smulEquiv g)).toLin'.restrict (by
          intro x hx
          exact ((Module.End.mem_invtSubmodule_iff_mapsTo
            (f := (permMatrix (h.smulEquiv g)).toLin')).mp
              ((LinearMap.IsIdempotentElem.commute_iff
                (minus8Matrix_toLin'_isIdempotentElem h.isMoore)
                (T := (permMatrix (h.smulEquiv g)).toLin')).mp
                (minus8Matrix_toLin'_commute_permMatrix_toLin' Γ (h.smulEquiv g)
                  (by
                    intro v w
                    exact h.smul_adj g v w))).1) hx) := by
    ext x
    rfl
  rw [Representation.character, hmap]
  rw [h.trace_restrict_minus8Range_smulEquiv_toLin'_eq_matrix_trace g]
  exact trace_minus8Matrix_mul_permMatrix_eq h.isMoore (h.smulEquiv g)

end D19ActsOnMoore57

end Moore57
