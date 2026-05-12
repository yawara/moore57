import Moore57.D19OnMoore57.Final.RepresentationCountConstantResidualBase
import Moore57.D19OnMoore57.AdjacentMoved.ReflectionCompactCriteria

/-!
# Final D19 inputs from compact adjacent-moved data

This file records the final representation-character boundary using the compact
adjacent-moved criterion over an `OrbitBaseSelectionInput`.
-/

namespace Moore57

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- Final D19 input package using representation-character data, exact
rotation-one fixed count, downstream base-selection input, and the compact
adjacent-moved complement-residual criterion. -/
structure D19FinalRepresentationCountCompactInputs
    (h : D19ActsOnMoore57 V Γ) where
  /-- Representation-theoretic multiplicities and nontrivial rotation
  character values. -/
  representation : D19ActsOnMoore57.D19RepresentationCharacterInput h
  /-- Rotation by `1` has exactly one fixed vertex. -/
  rotationOne_fixed_count : fixedVertexCount (h.rotation 1) = 1
  /-- Pairwise-disjoint selected moved rotation orbits. -/
  orbitBase : OrbitBaseSelectionInput h
  /-- Compact adjacent-moved complement-residual witness over the selected
  bases. -/
  adjacentMoved :
    AdjacentMovedReflectionComplementResidual38Witness h orbitBase

namespace D19FinalRepresentationCountCompactInputs

variable {h : D19ActsOnMoore57 V Γ}

/-- Convert the compact adjacent-moved criterion to the constant-residual final
representation boundary. -/
noncomputable def toD19FinalRepresentationCountConstantResidualBaseInputs
    (data : D19FinalRepresentationCountCompactInputs h) :
    D19FinalRepresentationCountConstantResidualBaseInputs h where
  representation := data.representation
  rotationOne_fixed_count := data.rotationOne_fixed_count
  orbitBase := data.orbitBase
  adjacentMoved := data.adjacentMoved.toConstantResidual38Witness

/-- Forget the compact presentation down to the final input record. -/
noncomputable def toD19FinalInputs
    (data : D19FinalRepresentationCountCompactInputs h) :
    D19FinalInputs h :=
  data.toD19FinalRepresentationCountConstantResidualBaseInputs.toD19FinalInputs

/-- Final representation-character, exact-count, compact adjacent-moved inputs
cannot exist. -/
theorem not_nonempty (h : D19ActsOnMoore57 V Γ) :
    ¬ Nonempty (D19FinalRepresentationCountCompactInputs h) := by
  rintro ⟨data⟩
  exact D19FinalRepresentationCountConstantResidualBaseInputs.not_nonempty h
    ⟨data.toD19FinalRepresentationCountConstantResidualBaseInputs⟩

end D19FinalRepresentationCountCompactInputs

end Moore57
