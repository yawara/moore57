import Moore57.D19OnMoore57.Involution.CountParity
import Moore57.D19OnMoore57.HigmanTrace.Congruence

/-!
# Arithmetic connectors for involution and Higman counts

This file contains only arithmetic consequences of already exposed count
inputs.  In particular, the fixed-induced edge-count formula is always an
explicit hypothesis; this file does not assert that such a formula has been
proved geometrically.
-/

namespace Moore57

noncomputable section

namespace InvolutionHigmanCountArithmetic

/-- If `a₁ = 3250 - 58*a₀ + 2*e` and Higman's congruence holds, then twice the
fixed-induced edge count has the forced residue modulo `15`.  This avoids
encoding the modular inverse of `2` as a separate arithmetic fact. -/
theorem edgeCountFormula_higman_twice_edges_intModEq
    {a0 a1 e : ℤ}
    (hformula : a1 = 3250 - 58 * a0 + 2 * e)
    (hhigman : a1 ≡ 7 * a0 + 5 [ZMOD 15]) :
    2 * e ≡ 5 * a0 - 5 [ZMOD 15] := by
  rw [Int.modEq_iff_dvd] at hhigman ⊢
  obtain ⟨q, hq⟩ := hhigman
  refine ⟨q - 4 * a0 + 216, ?_⟩
  omega

/-- Star-edge specialization of
`edgeCountFormula_higman_twice_edges_intModEq`: if the fixed-induced edge count is
`a₀ - 1`, then `a₀ ≡ 1 (mod 5)`. -/
theorem starEdgeCountFormula_higman_a0_intModEq_five
    {a0 a1 : ℤ}
    (hformula : a1 = 3250 - 58 * a0 + 2 * (a0 - 1))
    (hhigman : a1 ≡ 7 * a0 + 5 [ZMOD 15]) :
    a0 ≡ 1 [ZMOD 5] := by
  have hedges :
      2 * (a0 - 1) ≡ 5 * a0 - 5 [ZMOD 15] :=
    edgeCountFormula_higman_twice_edges_intModEq
      (a0 := a0) (a1 := a1) (e := a0 - 1) hformula hhigman
  rw [Int.modEq_iff_dvd] at hedges ⊢
  obtain ⟨q, hq⟩ := hedges
  refine ⟨-q, ?_⟩
  omega

/-- Integer form of the star-edge formula gives the concrete adjacent-moved
count `3248 - 56*a₀`. -/
theorem starEdgeCountFormula_a1_eq
    {a0 a1 : ℤ}
    (hformula : a1 = 3250 - 58 * a0 + 2 * (a0 - 1)) :
    a1 = 3248 - 56 * a0 := by
  omega

/-- With a star-edge formula, Higman's congruence, involution parity for
`a₀`, and explicit bounds `52 ≤ a₀ ≤ 56`, the only possible fixed count is
`56`. -/
theorem starEdgeCountFormula_a0_eq_56_of_bounds
    {a0 a1 : ℤ}
    (hformula : a1 = 3250 - 58 * a0 + 2 * (a0 - 1))
    (hhigman : a1 ≡ 7 * a0 + 5 [ZMOD 15])
    (ha0_even : 2 ∣ a0)
    (ha0_lower : 52 ≤ a0)
    (ha0_upper : a0 ≤ 56) :
    a0 = 56 := by
  have hmod5 :
      a0 ≡ 1 [ZMOD 5] :=
    starEdgeCountFormula_higman_a0_intModEq_five hformula hhigman
  rw [Int.modEq_iff_dvd] at hmod5
  obtain ⟨p, hp⟩ := hmod5
  obtain ⟨q, hq⟩ := ha0_even
  omega

end InvolutionHigmanCountArithmetic

open InvolutionHigmanCountArithmetic

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

namespace IsMoore57

/-- Raw involution/Higman connector for an arbitrary automorphism once the
trace is known to be integral and the edge-count formula is supplied as a
hypothesis. -/
theorem edgeCountFormula_twice_edges_intModEq
    (hΓ : IsMoore57 Γ) (σ : Equiv.Perm V) {z : ℤ} {e : ℤ}
    (htrace :
      Matrix.trace (E7Matrix Γ * permMatrix σ) = (z : ℚ))
    (hformula :
      (adjacentMovedCount Γ σ : ℤ) =
        3250 - 58 * (fixedVertexCount σ : ℤ) + 2 * e) :
    2 * e ≡ 5 * (fixedVertexCount σ : ℤ) - 5 [ZMOD 15] :=
  edgeCountFormula_higman_twice_edges_intModEq hformula
    (hΓ.higman_trace_int_intModEq σ htrace)

/-- Star-edge specialization for an arbitrary automorphism once the trace is
known to be integral and the star-edge formula is supplied explicitly. -/
theorem starEdgeCountFormula_fixedVertexCount_intModEq_five
    (hΓ : IsMoore57 Γ) (σ : Equiv.Perm V) {z : ℤ}
    (htrace :
      Matrix.trace (E7Matrix Γ * permMatrix σ) = (z : ℚ))
    (hformula :
      (adjacentMovedCount Γ σ : ℤ) =
        3250 - 58 * (fixedVertexCount σ : ℤ) +
          2 * ((fixedVertexCount σ : ℤ) - 1)) :
    (fixedVertexCount σ : ℤ) ≡ 1 [ZMOD 5] :=
  starEdgeCountFormula_higman_a0_intModEq_five hformula
    (hΓ.higman_trace_int_intModEq σ htrace)

/-- If the star-edge formula and explicit `52..56` bounds are available, an
involutive automorphism has exactly `56` fixed vertices. -/
theorem starEdgeCountFormula_fixedVertexCount_eq_56_of_bounds
    (hΓ : IsMoore57 Γ) (σ : Equiv.Perm V)
    (hinv : Function.Involutive σ) {z : ℤ}
    (htrace :
      Matrix.trace (E7Matrix Γ * permMatrix σ) = (z : ℚ))
    (hformula :
      (adjacentMovedCount Γ σ : ℤ) =
        3250 - 58 * (fixedVertexCount σ : ℤ) +
          2 * ((fixedVertexCount σ : ℤ) - 1))
    (hfixed_lower : 52 ≤ (fixedVertexCount σ : ℤ))
    (hfixed_upper : (fixedVertexCount σ : ℤ) ≤ 56) :
    fixedVertexCount σ = 56 := by
  have hcard : Fintype.card V = 3250 := hΓ.card
  have hsupport_even :
      2 ∣ Fintype.card V - fixedVertexCount σ :=
    two_dvd_card_sub_fixedVertexCount_of_involutive σ hinv
  have hfixed_even_int : 2 ∣ (fixedVertexCount σ : ℤ) := by
    obtain ⟨q, hq⟩ := hsupport_even
    refine ⟨1625 - q, ?_⟩
    omega
  have hfixed_int :
      (fixedVertexCount σ : ℤ) = 56 :=
    starEdgeCountFormula_a0_eq_56_of_bounds hformula
      (hΓ.higman_trace_int_intModEq σ htrace)
      hfixed_even_int hfixed_lower hfixed_upper
  exact_mod_cast hfixed_int

end IsMoore57

namespace D19ActsOnMoore57

variable {h : D19ActsOnMoore57 V Γ}

namespace D19LinearCharacterInput

/-- Reflection connector from packaged D19 linear-character input and an
explicit edge-count formula. -/
theorem reflection_edgeCountFormula_twice_edges_intModEq
    (hin : D19LinearCharacterInput h) (k : ZMod 19) {e : ℤ}
    (hformula :
      (adjacentMovedCount Γ (h.smulEquiv (DihedralGroup.sr k)) : ℤ) =
        3250 -
          58 * (fixedVertexCount (h.smulEquiv (DihedralGroup.sr k)) : ℤ) +
            2 * e) :
    2 * e ≡
      5 * (fixedVertexCount (h.smulEquiv (DihedralGroup.sr k)) : ℤ) - 5
        [ZMOD 15] :=
  edgeCountFormula_higman_twice_edges_intModEq hformula
    (Int.natCast_modEq_iff.mpr (hin.reflection_higman_natModEq k))

/-- Reflection star-edge connector: under the explicit star-edge count formula,
the reflection fixed count is `1 mod 5`. -/
theorem reflection_starEdgeCountFormula_fixedVertexCount_intModEq_five
    (hin : D19LinearCharacterInput h) (k : ZMod 19)
    (hformula :
      (adjacentMovedCount Γ (h.smulEquiv (DihedralGroup.sr k)) : ℤ) =
        3250 -
          58 * (fixedVertexCount (h.smulEquiv (DihedralGroup.sr k)) : ℤ) +
            2 * ((fixedVertexCount (h.smulEquiv (DihedralGroup.sr k)) : ℤ) - 1)) :
    (fixedVertexCount (h.smulEquiv (DihedralGroup.sr k)) : ℤ) ≡ 1
      [ZMOD 5] :=
  starEdgeCountFormula_higman_a0_intModEq_five hformula
    (Int.natCast_modEq_iff.mpr (hin.reflection_higman_natModEq k))

/-- Reflection version of the bounded star-edge arithmetic: the geometric
formula and explicit bounds reduce the fixed count to `56`. -/
theorem reflection_starEdgeCountFormula_fixedVertexCount_eq_56_of_bounds
    (hin : D19LinearCharacterInput h) (k : ZMod 19)
    (hformula :
      (adjacentMovedCount Γ (h.smulEquiv (DihedralGroup.sr k)) : ℤ) =
        3250 -
          58 * (fixedVertexCount (h.smulEquiv (DihedralGroup.sr k)) : ℤ) +
            2 * ((fixedVertexCount (h.smulEquiv (DihedralGroup.sr k)) : ℤ) - 1))
    (hfixed_lower :
      52 ≤ (fixedVertexCount (h.smulEquiv (DihedralGroup.sr k)) : ℤ))
    (hfixed_upper :
      (fixedVertexCount (h.smulEquiv (DihedralGroup.sr k)) : ℤ) ≤ 56) :
    fixedVertexCount (h.smulEquiv (DihedralGroup.sr k)) = 56 :=
  h.isMoore.starEdgeCountFormula_fixedVertexCount_eq_56_of_bounds
    (h.smulEquiv (DihedralGroup.sr k))
    (h.reflection_smulEquiv_involutive k)
    (z := (hin.multiplicity.alpha : ℤ) - (hin.multiplicity.beta : ℤ))
    (by rw [hin.linear_character, d19LinearCharacter_reflection])
    hformula hfixed_lower hfixed_upper

end D19LinearCharacterInput

end D19ActsOnMoore57

end

end Moore57
