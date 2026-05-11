import Moore57.D19OnMoore57.D19Core.D19ActionOrbitConcreteData
import Moore57.D19OnMoore57.Orbit.OrbitContributionSum

/-!
# Orbit contribution data for D19 actions

This file packages the adjacent-moved contribution in two pieces before
forgetting down to `D19ActionOrbitConcreteData`: the fixed/`A`-side contribution
and the contribution coming from the 56 generated rotation orbits.
-/

namespace Moore57

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- Higher-level contribution data attached to a fixed `D19ActsOnMoore57`
action.

The raw field in `D19ActionOrbitConcreteData` is recovered from three smaller
inputs: a fixed/`A`-side contribution of `38`, an orbit-sum decomposition of
`h.a1`, and the generic orbit contribution sum over the 56 generated rotation
orbits. -/
structure D19OrbitContributionData (h : D19ActsOnMoore57 V Γ) where
  /-- One representative for each of the 56 rotation orbits. -/
  base : Fin 56 → V
  /-- The chosen representatives are moved by the first nontrivial rotation. -/
  base_moved : ∀ q : Fin 56, h.rotation 1 (base q) ≠ base q
  /-- Split trace input for the action. -/
  traceInput : D19TraceInput h
  /-- The contribution from the fixed vertex and the `A`-side part. -/
  fixedOrAContribution : ZMod 19 → ℕ
  /-- The fixed/`A`-side contribution is `38` for every nontrivial rotation. -/
  fixed_or_A_contribution :
    ∀ d : ZMod 19, d ≠ 0 → fixedOrAContribution d = 38
  /-- Decomposition of `a1` into the fixed/`A`-side part and the 56 orbit
  contributions.  The orbit side is written as twice the sum over the chosen
  19-cycles, matching the two paired sides of the geometric decomposition. -/
  a1_decomposition :
    ∀ d : ZMod 19, d ≠ 0 →
      h.a1 d =
        fixedOrAContribution d +
          2 * (∑ q : Fin 56,
            ((h.rotationOrbitFinset (base q)).filter fun y =>
              Γ.Adj y (h.rotation d y)).card)

namespace D19OrbitContributionData

variable {h : D19ActsOnMoore57 V Γ}

/-- The full orbit map generated from the base vertex of orbit `q`. -/
noncomputable def W (data : D19OrbitContributionData h) (q : Fin 56) :
    ZMod 19 → V :=
  fun i => h.rotation i (data.base q)

/-- Number of generated base orbits whose internal difference set contains
`d`. -/
noncomputable def filteredOrbitCount (data : D19OrbitContributionData h)
    (d : ZMod 19) : ℕ :=
  ((Finset.univ : Finset (Fin 56)).filter
    (fun q => d ∈ internalDiffSet Γ (data.W q))).card

/-- The orbit-side contribution before converting the family sum to a filtered
count. -/
noncomputable def orbitContributionSum (data : D19OrbitContributionData h)
    (d : ZMod 19) : ℕ :=
  2 * (∑ q : Fin 56,
    ((h.rotationOrbitFinset (data.base q)).filter fun y =>
      Γ.Adj y (h.rotation d y)).card)

/-- Each chosen base vertex generates a full rotation orbit. -/
theorem rotationOrbitFinset_card_base (data : D19OrbitContributionData h)
    (q : Fin 56) :
    (h.rotationOrbitFinset (data.base q)).card = 19 :=
  h.rotationOrbitFinset_card_eq_nineteen_of_nonzero_moved'
    (d := 1) (by decide) (data.base_moved q)

/-- The orbit-side contribution is `38` times the number of generated orbits
whose internal difference set contains `d`. -/
theorem orbitContributionSum_eq_thirtyEight_mul_filteredOrbitCount
    (data : D19OrbitContributionData h) (d : ZMod 19) :
    data.orbitContributionSum d = 38 * data.filteredOrbitCount d := by
  classical
  have hsum :=
    h.sum_rotationOrbitContribution_card_eq_nineteen_mul_card_filter
      data.base d data.rotationOrbitFinset_card_base
  calc
    data.orbitContributionSum d =
        2 * (19 *
          ((Finset.univ : Finset (Fin 56)).filter
            (fun q => d ∈ internalDiffSet Γ (fun i : ZMod 19 =>
              h.rotation i (data.base q)))).card) := by
          simp [orbitContributionSum, hsum]
    _ = 38 * data.filteredOrbitCount d := by
          change
            2 * (19 *
              ((Finset.univ : Finset (Fin 56)).filter
                (fun q => d ∈ internalDiffSet Γ (fun i : ZMod 19 =>
                  h.rotation i (data.base q)))).card) =
              38 * ((Finset.univ : Finset (Fin 56)).filter
                (fun q => d ∈ internalDiffSet Γ (fun i : ZMod 19 =>
                  h.rotation i (data.base q)))).card
          rw [← Nat.mul_assoc]

/-- The higher-level split implies the raw contribution equation expected by
`D19ActionOrbitConcreteData`. -/
theorem a1_contribution (data : D19OrbitContributionData h) :
    ∀ d : ZMod 19, d ≠ 0 →
      h.a1 d =
        38 + 38 *
          ((Finset.univ : Finset (Fin 56)).filter
            (fun q => d ∈ internalDiffSet Γ (data.W q))).card := by
  intro d hd
  calc
    h.a1 d = data.fixedOrAContribution d + data.orbitContributionSum d := by
      simpa [orbitContributionSum] using data.a1_decomposition d hd
    _ = 38 + data.orbitContributionSum d := by
      rw [data.fixed_or_A_contribution d hd]
    _ = 38 + 38 * data.filteredOrbitCount d := by
      rw [data.orbitContributionSum_eq_thirtyEight_mul_filteredOrbitCount d]
    _ = 38 + 38 *
          ((Finset.univ : Finset (Fin 56)).filter
            (fun q => d ∈ internalDiffSet Γ (data.W q))).card := by
      rfl

/-- Forget the contribution split and keep the concrete data needed by the
existing contradiction pipeline. -/
noncomputable def toActionOrbitConcreteData (data : D19OrbitContributionData h) :
    D19ActionOrbitConcreteData h where
  base := data.base
  base_moved := data.base_moved
  traceInput := data.traceInput
  a1_contribution := by
    intro d hd
    simpa [D19ActionOrbitConcreteData.W, W] using data.a1_contribution d hd

end D19OrbitContributionData

end Moore57
