import Moore57.D19OnMoore57.Rotation.RotationFixedCountOneFrontier
import Moore57.D19OnMoore57.Reflection.ReflectionRawActionFixedStar

/-!
# Phase 1 prebuilt aliases for the representation-side wiring

The natural-language Lemma 9.3 (reflection has `a_0 = 56`, `a_1 = 112`) and
the rotation upper bound (`a_0(r^d) ≤ 19` for `d ≠ 0`) are already proved in
the codebase as raw-action consequences.  This file exposes them under the
stable Phase 1 names referenced in the representation-side roadmap.

* `rotation_a0_le_nineteen_of_raw_action` — `a_0(r^d) ≤ 19` for nonzero `d`,
  exact value `1` from `RotationFixedCountOneFrontier`.
* `reflection_a0_eq_fiftySix_of_raw_action` — `a_0(t) = 56` from
  `fixedVertexCount_reflection_eq_56_of_raw_action`.
* `reflection_a1_eq_oneHundredTwelve_of_raw_action` — `a_1(t) = 112` from
  `adjacentMovedCount_reflection_eq_112_of_raw_action`.

All three are immediate from existing raw-action infrastructure.  This file
provides a stable surface for Phase 2 (SRG spectrum / Higman trace) and
Phase 4 (vertex orbit decomposition).
-/

namespace Moore57

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

namespace D19ActsOnMoore57

/-- Task 1.1: Every nontrivial rotation has at most `19` fixed vertices
(actually exactly `1`).  Raw-action wrapper for `RotationFixedUpperBoundInput`. -/
noncomputable def rotationFixedUpperBoundInput_of_raw_action
    (h : D19ActsOnMoore57 V Γ) :
    RotationFixedUpperBoundInput h :=
  RotationFixedUpperBoundInput.of_provedRotationFixedCountOne h

/-- Task 1.1 (point form): `fixedVertexCount (h.rotation d) ≤ 19` for nonzero `d`. -/
theorem rotation_fixedVertexCount_le_nineteen
    (h : D19ActsOnMoore57 V Γ) (d : ZMod 19) (hd : d ≠ 0) :
    fixedVertexCount (h.rotation d) ≤ 19 :=
  (h.rotationFixedUpperBoundInput_of_raw_action).fixed_le_nineteen d hd

/-- Task 1.2 (reflection a_0 part): every reflection has exactly `56` fixed
vertices.  Direct alias to the raw-action consequence. -/
theorem reflection_fixedVertexCount_eq_fiftySix
    (h : D19ActsOnMoore57 V Γ) (k : ZMod 19) :
    fixedVertexCount (h.smulEquiv (DihedralGroup.sr k)) = 56 :=
  h.fixedVertexCount_reflection_eq_56_of_raw_action k

/-- Task 1.2 (reflection a_1 part): every reflection has adjacent-moved count
`112`.  Direct alias to the raw-action consequence. -/
theorem reflection_adjacentMovedCount_eq_oneHundredTwelve
    (h : D19ActsOnMoore57 V Γ) (k : ZMod 19) :
    adjacentMovedCount Γ (h.smulEquiv (DihedralGroup.sr k)) = 112 :=
  h.adjacentMovedCount_reflection_eq_112_of_raw_action k

end D19ActsOnMoore57

end Moore57
