import Moore57.D19OnMoore57.D19Core.D19OrbitContributionData
import Moore57.D19OnMoore57.Trace.TraceCharacterInputReduction

/-!
# Top-level reduced hypotheses for D19 actions

This file packages the currently remaining reduced inputs for a fixed
`D19ActsOnMoore57` witness and forgets them down to the existing orbit
contribution data interface.
-/

namespace Moore57

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- The top-level reduced hypotheses still needed for the D19 contradiction
pipeline attached to a fixed `D19ActsOnMoore57` action.

The character input is kept in its coarse reduced form; the orbit contribution
input is kept as the split fixed/`A` contribution plus the generated-orbit
decomposition. -/
structure D19ReducedHypotheses (h : D19ActsOnMoore57 V Γ) where
  /-- Coarse trace-character input for the action. -/
  characterInput : D19ActsOnMoore57.D19CharacterInput h
  /-- One representative for each of the 56 rotation orbits. -/
  base : Fin 56 → V
  /-- The chosen representatives are moved by the first nontrivial rotation. -/
  base_moved : ∀ q : Fin 56, h.rotation 1 (base q) ≠ base q
  /-- The contribution from the fixed vertex and the `A`-side part. -/
  fixedOrAContribution : ZMod 19 → ℕ
  /-- The fixed/`A`-side contribution is `38` for every nontrivial rotation. -/
  fixed_or_A_contribution :
    ∀ d : ZMod 19, d ≠ 0 → fixedOrAContribution d = 38
  /-- Decomposition of `a1` into the fixed/`A`-side part and the 56 generated
  rotation-orbit contributions. -/
  a1_decomposition :
    ∀ d : ZMod 19, d ≠ 0 →
      h.a1 d =
        fixedOrAContribution d +
          2 * (∑ q : Fin 56,
            ((h.rotationOrbitFinset (base q)).filter fun y =>
              Γ.Adj y (h.rotation d y)).card)

namespace D19ReducedHypotheses

variable {h : D19ActsOnMoore57 V Γ}

/-- Forget the top-level reduced packaging down to the orbit contribution data
interface used by the existing contradiction pipeline. -/
noncomputable def toD19OrbitContributionData (data : D19ReducedHypotheses h) :
    D19OrbitContributionData h where
  base := data.base
  base_moved := data.base_moved
  traceInput := data.characterInput.toD19TraceInput
  fixedOrAContribution := data.fixedOrAContribution
  fixed_or_A_contribution := data.fixed_or_A_contribution
  a1_decomposition := data.a1_decomposition

/-- The reduced top-level D19 hypotheses cannot exist. -/
theorem not_nonempty (h : D19ActsOnMoore57 V Γ) :
    ¬ Nonempty (D19ReducedHypotheses h) := by
  rintro ⟨data⟩
  exact D19ActionOrbitConcreteData.not_nonempty h
    ⟨data.toD19OrbitContributionData.toActionOrbitConcreteData⟩

end D19ReducedHypotheses

end Moore57
