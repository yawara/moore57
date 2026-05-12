import Moore57.D19OnMoore57.Reflection.FixedSetStarTraceBoundsBridge
import Moore57.D19OnMoore57.Reflection.TraceIntegrality

/-!
# Reflection fixed-count bounds bridge

This file packages the remaining Macaj-Siran/Higman fixed-count range
`52 ≤ a₀ ≤ 56` for reflections, and exposes thin connectors from that range to
the existing fixed-star bridge.  It does not prove the range from a raw
reflection; it isolates exactly what the current scaffold still needs.
-/

namespace Moore57

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

namespace D19ActsOnMoore57

variable {h : D19ActsOnMoore57 V Γ}

/-- The remaining reflection fixed-count range, in the natural-number form
used by the fixed-induced graph regular-branch exclusion. -/
structure ReflectionFixedCountBounds (h : D19ActsOnMoore57 V Γ) : Prop where
  lower :
    ∀ k : ZMod 19,
      52 ≤ fixedVertexCount (h.smulEquiv (DihedralGroup.sr k))
  upper :
    ∀ k : ZMod 19,
      fixedVertexCount (h.smulEquiv (DihedralGroup.sr k)) ≤ 56

namespace ReflectionFixedCountBounds

/-- Integer lower-bound form expected by the Higman arithmetic bridge. -/
theorem lower_int (bounds : ReflectionFixedCountBounds h) (k : ZMod 19) :
    52 ≤ (fixedVertexCount (h.smulEquiv (DihedralGroup.sr k)) : ℤ) := by
  exact_mod_cast ReflectionFixedCountBounds.lower bounds k

/-- Integer upper-bound form expected by the Higman arithmetic bridge. -/
theorem upper_int (bounds : ReflectionFixedCountBounds h) (k : ZMod 19) :
    (fixedVertexCount (h.smulEquiv (DihedralGroup.sr k)) : ℤ) ≤ 56 := by
  exact_mod_cast ReflectionFixedCountBounds.upper bounds k

/-- The exact paper fixed-count statement is a stronger source of the bounds. -/
def of_exact
    (hfix :
      ∀ k : ZMod 19,
        fixedVertexCount (h.smulEquiv (DihedralGroup.sr k)) = 56) :
    ReflectionFixedCountBounds h where
  lower := by
    intro k
    simp [hfix k]
  upper := by
    intro k
    simp [hfix k]

/-- The fixed-count range alone rules out the regular fixed-induced branch. -/
theorem fixedInducedGraph_not_regular
    (bounds : ReflectionFixedCountBounds h) (k : ZMod 19) :
    ¬ ∃ d : ℕ,
      ∀ x : fixedVertexSet (h.smulEquiv (DihedralGroup.sr k)),
        (h.fixedInducedGraph (DihedralGroup.sr k)).degree x = d :=
  h.fixedInducedGraph_not_regular_of_fixedVertexCount_between_52_56
    (DihedralGroup.sr k)
    (ReflectionFixedCountBounds.lower bounds k)
    (ReflectionFixedCountBounds.upper bounds k)

/-- Via the strong `(0,1)` fixed-induced graph scaffold, the same range gives
a star center for the fixed-induced graph. -/
theorem exists_fixedInducedGraph_isStarWithCenter
    (bounds : ReflectionFixedCountBounds h) (k : ZMod 19) :
    ∃ c : fixedVertexSet (h.smulEquiv (DihedralGroup.sr k)),
      IsStarWithCenter (h.fixedInducedGraph (DihedralGroup.sr k)) c := by
  have hstrong := h.fixedInducedGraph_isStrongZeroOne (DihedralGroup.sr k)
  exact hstrong.exists_isStarWithCenter_of_not_regular
    (ReflectionFixedCountBounds.fixedInducedGraph_not_regular bounds k)

/-- Fixed-count bounds plus trace integrality give the paper-shaped fixed-star
conclusion through the existing Higman arithmetic bridge. -/
theorem involutionFixedSetStar56_of_trace
    (bounds : ReflectionFixedCountBounds h)
    (k : ZMod 19) {z : ℤ}
    (htrace :
      Matrix.trace (E7Matrix Γ * permMatrix (h.smulEquiv (DihedralGroup.sr k))) =
        (z : ℚ)) :
    InvolutionFixedSetStar56 Γ (h.smulEquiv (DihedralGroup.sr k)) :=
  h.involutionFixedSetStar56_of_reflection_trace_fixedVertexCount_bounds
    k htrace
    (ReflectionFixedCountBounds.lower_int bounds k)
    (ReflectionFixedCountBounds.upper_int bounds k)

/-- Prop-valued `K_{1,55}` output from the same fixed-count bounds package. -/
theorem nonempty_involutionK155_of_trace
    (bounds : ReflectionFixedCountBounds h)
    (k : ZMod 19) {z : ℤ}
    (htrace :
      Matrix.trace (E7Matrix Γ * permMatrix (h.smulEquiv (DihedralGroup.sr k))) =
        (z : ℚ)) :
    Nonempty (InvolutionK155 Γ (h.smulEquiv (DihedralGroup.sr k))) :=
  (ReflectionFixedCountBounds.involutionFixedSetStar56_of_trace
    bounds k htrace).nonempty_involutionK155

/-- Fixed-count bounds alone now give the paper-shaped fixed-star conclusion:
the E7 trace integrality is automatic for reflections. -/
theorem involutionFixedSetStar56
    (bounds : ReflectionFixedCountBounds h) (k : ZMod 19) :
    InvolutionFixedSetStar56 Γ (h.smulEquiv (DihedralGroup.sr k)) := by
  obtain ⟨z, htrace⟩ :=
    h.exists_int_E7Matrix_mul_permMatrix_reflection_trace k
  exact ReflectionFixedCountBounds.involutionFixedSetStar56_of_trace
    bounds k htrace

/-- Prop-valued `K_{1,55}` output from fixed-count bounds alone. -/
theorem nonempty_involutionK155
    (bounds : ReflectionFixedCountBounds h) (k : ZMod 19) :
    Nonempty (InvolutionK155 Γ (h.smulEquiv (DihedralGroup.sr k))) :=
  (ReflectionFixedCountBounds.involutionFixedSetStar56 bounds k).nonempty_involutionK155

end ReflectionFixedCountBounds

/-- Per-reflection Nat-bounds wrapper around the existing Int-bounds trace
bridge. -/
theorem involutionFixedSetStar56_of_reflection_trace_fixedVertexCount_nat_bounds
    (k : ZMod 19) {z : ℤ}
    (htrace :
      Matrix.trace (E7Matrix Γ * permMatrix (h.smulEquiv (DihedralGroup.sr k))) =
        (z : ℚ))
    (hfixed_lower :
      52 ≤ fixedVertexCount (h.smulEquiv (DihedralGroup.sr k)))
    (hfixed_upper :
      fixedVertexCount (h.smulEquiv (DihedralGroup.sr k)) ≤ 56) :
    InvolutionFixedSetStar56 Γ (h.smulEquiv (DihedralGroup.sr k)) := by
  exact h.involutionFixedSetStar56_of_reflection_trace_fixedVertexCount_bounds
    k htrace (by exact_mod_cast hfixed_lower) (by exact_mod_cast hfixed_upper)

/-- Prop-valued `K_{1,55}` version of the Nat-bounds trace bridge. -/
theorem nonempty_involutionK155_of_reflection_trace_fixedVertexCount_nat_bounds
    (k : ZMod 19) {z : ℤ}
    (htrace :
      Matrix.trace (E7Matrix Γ * permMatrix (h.smulEquiv (DihedralGroup.sr k))) =
        (z : ℚ))
    (hfixed_lower :
      52 ≤ fixedVertexCount (h.smulEquiv (DihedralGroup.sr k)))
    (hfixed_upper :
      fixedVertexCount (h.smulEquiv (DihedralGroup.sr k)) ≤ 56) :
    Nonempty (InvolutionK155 Γ (h.smulEquiv (DihedralGroup.sr k))) :=
  (h.involutionFixedSetStar56_of_reflection_trace_fixedVertexCount_nat_bounds
    k htrace hfixed_lower hfixed_upper).nonempty_involutionK155

/-- Per-reflection Nat-bounds bridge with automatic E7 trace integrality. -/
theorem involutionFixedSetStar56_of_reflection_fixedVertexCount_nat_bounds
    (k : ZMod 19)
    (hfixed_lower :
      52 ≤ fixedVertexCount (h.smulEquiv (DihedralGroup.sr k)))
    (hfixed_upper :
      fixedVertexCount (h.smulEquiv (DihedralGroup.sr k)) ≤ 56) :
    InvolutionFixedSetStar56 Γ (h.smulEquiv (DihedralGroup.sr k)) := by
  obtain ⟨z, htrace⟩ :=
    h.exists_int_E7Matrix_mul_permMatrix_reflection_trace k
  exact h.involutionFixedSetStar56_of_reflection_trace_fixedVertexCount_nat_bounds
    k htrace hfixed_lower hfixed_upper

/-- Prop-valued `K_{1,55}` version of the Nat-bounds bridge with automatic E7
trace integrality. -/
theorem nonempty_involutionK155_of_reflection_fixedVertexCount_nat_bounds
    (k : ZMod 19)
    (hfixed_lower :
      52 ≤ fixedVertexCount (h.smulEquiv (DihedralGroup.sr k)))
    (hfixed_upper :
      fixedVertexCount (h.smulEquiv (DihedralGroup.sr k)) ≤ 56) :
    Nonempty (InvolutionK155 Γ (h.smulEquiv (DihedralGroup.sr k))) :=
  (h.involutionFixedSetStar56_of_reflection_fixedVertexCount_nat_bounds
    k hfixed_lower hfixed_upper).nonempty_involutionK155

end D19ActsOnMoore57

end

end Moore57
