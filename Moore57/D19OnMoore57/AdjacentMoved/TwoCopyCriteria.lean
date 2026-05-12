import Moore57.D19OnMoore57.AdjacentMoved.PartitionContribution

/-!
# Two-copy criteria for adjacent-moved decompositions

This file packages the common `Fin 2 × Fin 56` partition criterion for the
adjacent-moved decomposition.  It is a higher-level witness layer over
`D19AdjacentMovedDecomposition.of_twoCopyPartition`: instead of passing a
partition and two contribution hypotheses separately, one record contains the
pieces, residual part, partition proof, and filtered-count contributions for
all nontrivial rotations.
-/

namespace Moore57

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- A raw two-copy partition witness for the adjacent-moved decomposition.

For every nontrivial rotation `d`, the finite vertex set is partitioned into
`Fin 2 × Fin 56` pieces plus one residual part.  Each of the two copies over a
fixed `q : Fin 56` contributes the same filtered cardinality as the chosen
rotation orbit of `base q`; the residual contributes `fixedOrAContribution d`.
-/
structure AdjacentMovedTwoCopyPartitionWitness
    (h : D19ActsOnMoore57 V Γ) (base : Fin 56 → V)
    (fixedOrAContribution : ZMod 19 → ℕ) where
  pieces :
    ∀ d : ZMod 19, d ≠ 0 → Fin 2 × Fin 56 → Finset V
  residual :
    ∀ d : ZMod 19, d ≠ 0 → Finset V
  pairwise_disjoint :
    ∀ d : ZMod 19, ∀ hd : d ≠ 0,
      ((Finset.univ : Finset (Fin 2 × Fin 56)) :
        Set (Fin 2 × Fin 56)).PairwiseDisjoint (pieces d hd)
  residual_disjoint :
    ∀ d : ZMod 19, ∀ hd : d ≠ 0, ∀ i : Fin 2 × Fin 56,
      Disjoint (pieces d hd i) (residual d hd)
  cover :
    ∀ d : ZMod 19, ∀ hd : d ≠ 0,
      (Finset.univ : Finset (Fin 2 × Fin 56)).biUnion (pieces d hd) ∪
          residual d hd =
        (Finset.univ : Finset V)
  residual_contribution :
    ∀ d : ZMod 19, ∀ hd : d ≠ 0,
      ((residual d hd).filter fun y => Γ.Adj y (h.rotation d y)).card =
        fixedOrAContribution d
  copy_contribution :
    ∀ d : ZMod 19, ∀ hd : d ≠ 0, ∀ side : Fin 2, ∀ q : Fin 56,
      ((pieces d hd (side, q)).filter fun y =>
          Γ.Adj y (h.rotation d y)).card =
        ((h.rotationOrbitFinset (base q)).filter fun y =>
          Γ.Adj y (h.rotation d y)).card

namespace AdjacentMovedTwoCopyPartitionWitness

variable {h : D19ActsOnMoore57 V Γ}
variable {base : Fin 56 → V}
variable {fixedOrAContribution : ZMod 19 → ℕ}

/-- Convert the raw witness for a fixed nontrivial rotation into the generic
`AdjacentMovedPartition` package. -/
def toPartition
    (w : AdjacentMovedTwoCopyPartitionWitness h base fixedOrAContribution)
    (d : ZMod 19) (hd : d ≠ 0) :
    D19ActsOnMoore57.AdjacentMovedPartition h d (Fin 2 × Fin 56) where
  pieces := w.pieces d hd
  residual := w.residual d hd
  pairwise_disjoint := w.pairwise_disjoint d hd
  residual_disjoint := w.residual_disjoint d hd
  cover := w.cover d hd

/-- The bundled two-copy witness supplies the downstream adjacent-moved
decomposition. -/
noncomputable def toDecomposition
    (w : AdjacentMovedTwoCopyPartitionWitness h base fixedOrAContribution) :
    D19AdjacentMovedDecomposition h base fixedOrAContribution :=
  D19AdjacentMovedDecomposition.of_twoCopyPartition
    (fun d hd => w.toPartition d hd)
    (fun d hd => w.residual_contribution d hd)
    (fun d hd side q => w.copy_contribution d hd side q)

/-- The same witness gives the `a1` decomposition used by the reduced D19
pipeline. -/
theorem a1_decomposition
    (w : AdjacentMovedTwoCopyPartitionWitness h base fixedOrAContribution) :
    ∀ d : ZMod 19, d ≠ 0 →
      h.a1 d =
        fixedOrAContribution d +
          2 * (∑ q : Fin 56,
            ((h.rotationOrbitFinset (base q)).filter fun y =>
              Γ.Adj y (h.rotation d y)).card) :=
  w.toDecomposition.a1_decomposition

end AdjacentMovedTwoCopyPartitionWitness

/-- The constant residual contribution `38`, used for the fixed/`A` side in
the D19 reduction. -/
def fixedOrAContribution38 : ZMod 19 → ℕ := fun _ => 38

/-- Specialized two-copy partition witness when the residual contribution is
known directly to be `38` for every nontrivial rotation. -/
structure AdjacentMovedTwoCopyPartition38Witness
    (h : D19ActsOnMoore57 V Γ) (base : Fin 56 → V) where
  pieces :
    ∀ d : ZMod 19, d ≠ 0 → Fin 2 × Fin 56 → Finset V
  residual :
    ∀ d : ZMod 19, d ≠ 0 → Finset V
  pairwise_disjoint :
    ∀ d : ZMod 19, ∀ hd : d ≠ 0,
      ((Finset.univ : Finset (Fin 2 × Fin 56)) :
        Set (Fin 2 × Fin 56)).PairwiseDisjoint (pieces d hd)
  residual_disjoint :
    ∀ d : ZMod 19, ∀ hd : d ≠ 0, ∀ i : Fin 2 × Fin 56,
      Disjoint (pieces d hd i) (residual d hd)
  cover :
    ∀ d : ZMod 19, ∀ hd : d ≠ 0,
      (Finset.univ : Finset (Fin 2 × Fin 56)).biUnion (pieces d hd) ∪
          residual d hd =
        (Finset.univ : Finset V)
  residual_contribution :
    ∀ d : ZMod 19, ∀ hd : d ≠ 0,
      ((residual d hd).filter fun y => Γ.Adj y (h.rotation d y)).card = 38
  copy_contribution :
    ∀ d : ZMod 19, ∀ hd : d ≠ 0, ∀ side : Fin 2, ∀ q : Fin 56,
      ((pieces d hd (side, q)).filter fun y =>
          Γ.Adj y (h.rotation d y)).card =
        ((h.rotationOrbitFinset (base q)).filter fun y =>
          Γ.Adj y (h.rotation d y)).card

namespace AdjacentMovedTwoCopyPartition38Witness

variable {h : D19ActsOnMoore57 V Γ}
variable {base : Fin 56 → V}

/-- Forget the specialized `38` witness to the general two-copy witness with
constant fixed/`A` contribution. -/
def toWitness (w : AdjacentMovedTwoCopyPartition38Witness h base) :
    AdjacentMovedTwoCopyPartitionWitness h base fixedOrAContribution38 where
  pieces := w.pieces
  residual := w.residual
  pairwise_disjoint := w.pairwise_disjoint
  residual_disjoint := w.residual_disjoint
  cover := w.cover
  residual_contribution := by
    intro d hd
    simpa [fixedOrAContribution38] using w.residual_contribution d hd
  copy_contribution := w.copy_contribution

/-- Dedicated constructor for the adjacent-moved decomposition with residual
contribution constantly `38`. -/
noncomputable def toDecomposition
    (w : AdjacentMovedTwoCopyPartition38Witness h base) :
    D19AdjacentMovedDecomposition h base fixedOrAContribution38 :=
  w.toWitness.toDecomposition

/-- The specialized witness gives the `a1` decomposition with the residual
term written as `38`. -/
theorem a1_decomposition
    (w : AdjacentMovedTwoCopyPartition38Witness h base) :
    ∀ d : ZMod 19, d ≠ 0 →
      h.a1 d =
        38 +
          2 * (∑ q : Fin 56,
            ((h.rotationOrbitFinset (base q)).filter fun y =>
              Γ.Adj y (h.rotation d y)).card) := by
  intro d hd
  simpa [fixedOrAContribution38] using w.toDecomposition.a1_decomposition d hd

end AdjacentMovedTwoCopyPartition38Witness

namespace D19AdjacentMovedDecomposition

variable {h : D19ActsOnMoore57 V Γ}
variable {base : Fin 56 → V}

/-- Constructor wrapper for the common two-copy criterion with residual
contribution constantly `38`. -/
noncomputable def of_twoCopyPartition38
    (w : AdjacentMovedTwoCopyPartition38Witness h base) :
    D19AdjacentMovedDecomposition h base fixedOrAContribution38 :=
  w.toDecomposition

end D19AdjacentMovedDecomposition

end Moore57
