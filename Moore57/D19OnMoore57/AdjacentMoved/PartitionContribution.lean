import Moore57.D19OnMoore57.AdjacentMoved.Partition
import Moore57.D19OnMoore57.Orbit.FamilyPartition
import Moore57.D19OnMoore57.D19Core.OrbitContributionData

/-!
# Adjacent-moved partitions as orbit contribution data

This file bridges a coarse vertex partition/counting statement to the
`a1_decomposition` field used by `D19OrbitContributionData`.
-/

namespace Moore57

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- A partition-level decomposition of the adjacent-moved count into a
fixed/`A` residual contribution plus two copies of the chosen `Fin 56` rotation
orbit family.

The structure is deliberately stated only as the resulting counting identity:
the two copies may come from actual paired pieces, or from any coarser
partition proof that gives the same filtered cardinalities. -/
structure D19AdjacentMovedDecomposition (h : D19ActsOnMoore57 V Γ)
    (base : Fin 56 → V) (fixedOrAContribution : ZMod 19 → ℕ) where
  adjacentMoved_decomposition :
    ∀ d : ZMod 19, d ≠ 0 →
      adjacentMovedCount Γ (h.rotation d) =
        fixedOrAContribution d +
          2 * (∑ q : Fin 56,
            ((h.rotationOrbitFinset (base q)).filter fun y =>
              Γ.Adj y (h.rotation d y)).card)

namespace D19AdjacentMovedDecomposition

variable {h : D19ActsOnMoore57 V Γ}
variable {base : Fin 56 → V}
variable {fixedOrAContribution : ZMod 19 → ℕ}

/-- The adjacent-moved decomposition is exactly the `a1_decomposition` equation
required by `D19OrbitContributionData`, since `h.a1 d` is definitionally the
adjacent-moved count of `h.rotation d`. -/
theorem a1_decomposition
    (decomp : D19AdjacentMovedDecomposition h base fixedOrAContribution) :
    ∀ d : ZMod 19, d ≠ 0 →
      h.a1 d =
        fixedOrAContribution d +
          2 * (∑ q : Fin 56,
            ((h.rotationOrbitFinset (base q)).filter fun y =>
              Γ.Adj y (h.rotation d y)).card) := by
  intro d hd
  rw [← h.rotation_a1_def d]
  exact decomp.adjacentMoved_decomposition d hd

private theorem sum_fin_two_orbit_contribution
    (f : Fin 56 → ℕ) :
    (∑ i : Fin 2 × Fin 56, f i.2) = 2 * ∑ q : Fin 56, f q := by
  classical
  calc
    (∑ i : Fin 2 × Fin 56, f i.2)
        = ∑ side : Fin 2, ∑ q : Fin 56, f q := by
          simpa using
            (Fintype.sum_prod_type
              (fun i : Fin 2 × Fin 56 => f i.2))
    _ = 2 * ∑ q : Fin 56, f q := by
          simp [Nat.two_mul]

/-- Build an adjacent-moved decomposition from actual partition data indexed by
`Fin 2 × Fin 56` plus a residual part.

The hypotheses say that the residual filtered cardinality is the fixed/`A`
contribution, and each of the two indexed copies has the same filtered
cardinality as the corresponding rotation-orbit finset. The partition cover and
disjointness themselves are supplied through `AdjacentMovedPartition`, whose
counting theorem is used in the proof. -/
noncomputable def of_twoCopyPartition
    (partition :
      ∀ d : ZMod 19, d ≠ 0 →
        D19ActsOnMoore57.AdjacentMovedPartition h d (Fin 2 × Fin 56))
    (residual_contribution :
      ∀ d : ZMod 19, ∀ hd : d ≠ 0,
        (((partition d hd).residual).filter fun y =>
          Γ.Adj y (h.rotation d y)).card = fixedOrAContribution d)
    (copy_contribution :
      ∀ d : ZMod 19, ∀ hd : d ≠ 0, ∀ side : Fin 2, ∀ q : Fin 56,
        (((partition d hd).pieces (side, q)).filter fun y =>
          Γ.Adj y (h.rotation d y)).card =
            ((h.rotationOrbitFinset (base q)).filter fun y =>
              Γ.Adj y (h.rotation d y)).card) :
    D19AdjacentMovedDecomposition h base fixedOrAContribution where
  adjacentMoved_decomposition := by
    intro d hd
    classical
    let P := partition d hd
    let orbitContribution : Fin 56 → ℕ := fun q =>
      ((h.rotationOrbitFinset (base q)).filter fun y =>
        Γ.Adj y (h.rotation d y)).card
    have hpartition :
        adjacentMovedCount Γ (h.rotation d) =
          (∑ i : Fin 2 × Fin 56,
            ((P.pieces i).filter fun y => Γ.Adj y (h.rotation d y)).card) +
            (P.residual.filter fun y => Γ.Adj y (h.rotation d y)).card := by
      exact D19ActsOnMoore57.AdjacentMovedPartition.adjacentMovedCount_eq_sum_filter_card
        h d P
    have hpieces :
        (∑ i : Fin 2 × Fin 56,
            ((P.pieces i).filter fun y => Γ.Adj y (h.rotation d y)).card) =
          ∑ i : Fin 2 × Fin 56, orbitContribution i.2 := by
      apply Finset.sum_congr rfl
      intro i _hi
      exact copy_contribution d hd i.1 i.2
    have hresidual :
        (P.residual.filter fun y => Γ.Adj y (h.rotation d y)).card =
          fixedOrAContribution d := by
      exact residual_contribution d hd
    calc
      adjacentMovedCount Γ (h.rotation d)
          = (∑ i : Fin 2 × Fin 56,
              ((P.pieces i).filter fun y => Γ.Adj y (h.rotation d y)).card) +
              (P.residual.filter fun y => Γ.Adj y (h.rotation d y)).card := hpartition
      _ = (∑ i : Fin 2 × Fin 56, orbitContribution i.2) +
              fixedOrAContribution d := by
            rw [hpieces, hresidual]
      _ = 2 * (∑ q : Fin 56, orbitContribution q) +
              fixedOrAContribution d := by
            rw [sum_fin_two_orbit_contribution]
      _ = fixedOrAContribution d +
            2 * (∑ q : Fin 56, orbitContribution q) := by
            rw [Nat.add_comm]

end D19AdjacentMovedDecomposition

end Moore57
