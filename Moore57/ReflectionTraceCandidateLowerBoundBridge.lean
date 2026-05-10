import Moore57.ReflectionTraceSmallCandidateReduction

/-!
# Lower-bound bridge after trace-refined reflection candidates

The raw reflection candidate list is now
`6, 10, 16, 26, 36, 46, 56`.  Consequently a lower bound of `47` already
forces the paper fixed count `56`, and hence the fixed-star theorem.
-/

namespace Moore57

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

namespace D19ActsOnMoore57

variable {h : D19ActsOnMoore57 V Γ}

/-- Trace-refined raw candidates plus the lower bound `47` force the exact
paper reflection fixed count. -/
theorem fixedVertexCount_reflection_eq_56_of_ge_fortySeven
    (k : ZMod 19)
    (hlower : 47 ≤ fixedVertexCount (h.smulEquiv (DihedralGroup.sr k))) :
    fixedVertexCount (h.smulEquiv (DihedralGroup.sr k)) = 56 := by
  rcases h.fixedVertexCount_reflection_trace_refined_raw_candidates k with
      h6 | h10 | h16 | h26 | h36 | h46 | h56 <;> omega

/-- A lower bound of `47` is now enough to obtain the paper-shaped reflection
fixed star. -/
theorem involutionFixedSetStar56_of_reflection_fixedVertexCount_ge_fortySeven
    (k : ZMod 19)
    (hlower : 47 ≤ fixedVertexCount (h.smulEquiv (DihedralGroup.sr k))) :
    InvolutionFixedSetStar56 Γ (h.smulEquiv (DihedralGroup.sr k)) :=
  h.involutionFixedSetStar56_of_reflection_fixedVertexCount_eq_56 k
    (h.fixedVertexCount_reflection_eq_56_of_ge_fortySeven k hlower)

/-- Uniform lower-bound package for all reflections. -/
structure ReflectionFixedCountLower47 (h : D19ActsOnMoore57 V Γ) : Prop where
  lower :
    ∀ k : ZMod 19,
      47 ≤ fixedVertexCount (h.smulEquiv (DihedralGroup.sr k))

namespace ReflectionFixedCountLower47

/-- The lower-bound package supplies exact fixed count `56` for every
reflection. -/
theorem fixedVertexCount_eq_56
    (bounds : ReflectionFixedCountLower47 h) (k : ZMod 19) :
    fixedVertexCount (h.smulEquiv (DihedralGroup.sr k)) = 56 :=
  h.fixedVertexCount_reflection_eq_56_of_ge_fortySeven k (bounds.lower k)

/-- The lower-bound package supplies the paper-shaped fixed star for every
reflection. -/
theorem involutionFixedSetStar56
    (bounds : ReflectionFixedCountLower47 h) (k : ZMod 19) :
    InvolutionFixedSetStar56 Γ (h.smulEquiv (DihedralGroup.sr k)) :=
  h.involutionFixedSetStar56_of_reflection_fixedVertexCount_ge_fortySeven
    k (bounds.lower k)

/-- The lower-bound package is a stronger source of the previous `52..56`
fixed-count-bounds record. -/
def toReflectionFixedCountBounds
    (bounds : ReflectionFixedCountLower47 h) :
    ReflectionFixedCountBounds h where
  lower := by
    intro k
    have h56 := bounds.fixedVertexCount_eq_56 k
    omega
  upper := by
    intro k
    rw [bounds.fixedVertexCount_eq_56 k]

end ReflectionFixedCountLower47

end D19ActsOnMoore57

end

end Moore57
