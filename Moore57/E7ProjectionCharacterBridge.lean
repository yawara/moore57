import Moore57.E7ProjectionRepresentationSkeleton
import Moore57.E7ProjectionTraceBridge
import Mathlib.RepresentationTheory.Character

/-!
# Character bridge for the E7 projection representation

The `E7` range representation constructed from the raw D19 action has character
equal to the concrete matrix trace used by the Higman pipeline.
-/

namespace Moore57

namespace D19ActsOnMoore57

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- The mathlib character of the concrete `E7` range representation is the
project's concrete Higman trace `trace(E7 * P_g)`. -/
theorem e7ProjectionRepresentation_character_eq_matrix_trace
    (h : D19ActsOnMoore57 V Γ) (g : DihedralGroup 19) :
    (h.e7ProjectionRepresentation).character g =
      Matrix.trace (E7Matrix Γ * permMatrix (h.smulEquiv g)) := by
  have hmap :
      h.e7ProjectionRepresentation g =
        (permMatrix (h.smulEquiv g)).toLin'.restrict (by
          intro x hx
          exact ((Module.End.mem_invtSubmodule_iff_mapsTo
            (f := (permMatrix (h.smulEquiv g)).toLin')).mp
              ((LinearMap.IsIdempotentElem.commute_iff
                (E7Matrix_toLin'_isIdempotentElem h.isMoore)
                (T := (permMatrix (h.smulEquiv g)).toLin')).mp
                (E7Matrix_toLin'_commute_permMatrix_toLin' Γ (h.smulEquiv g)
                  (by
                    intro v w
                    exact h.smul_adj g v w))).1) hx) := by
    ext x
    rfl
  rw [Representation.character, hmap]
  exact h.trace_restrict_E7Range_smulEquiv_toLin'_eq_matrix_trace g

end D19ActsOnMoore57

end Moore57
