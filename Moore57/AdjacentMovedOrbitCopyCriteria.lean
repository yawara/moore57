import Moore57.AdjacentMovedTwoCopyCriteria

/-!
# Orbit-copy criteria for adjacent-moved two-copy witnesses

This file adds a constructor layer for the two-copy adjacent-moved partition in
which every indexed piece is explicitly a rotation-orbit finset.
-/

namespace Moore57

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- A two-copy adjacent-moved partition witness whose pieces are rotation
orbits.

For every nontrivial rotation `d`, the pieces are
`h.rotationOrbitFinset (copyBase d hd i)`, indexed by `Fin 2 × Fin 56`, plus a
residual part.  The hypotheses are exactly those needed to forget this to the
existing `AdjacentMovedTwoCopyPartition38Witness`: disjointness, cover,
residual contribution `38`, and equality of each copy contribution with the
corresponding chosen base orbit contribution. -/
structure AdjacentMovedOrbitCopyPartition38Witness
    (h : D19ActsOnMoore57 V Γ) (base : Fin 56 → V) where
  copyBase :
    ∀ d : ZMod 19, d ≠ 0 → Fin 2 × Fin 56 → V
  residual :
    ∀ d : ZMod 19, d ≠ 0 → Finset V
  pairwise_disjoint :
    ∀ d : ZMod 19, ∀ hd : d ≠ 0,
      ((Finset.univ : Finset (Fin 2 × Fin 56)) :
        Set (Fin 2 × Fin 56)).PairwiseDisjoint
          (fun i => h.rotationOrbitFinset (copyBase d hd i))
  residual_disjoint :
    ∀ d : ZMod 19, ∀ hd : d ≠ 0, ∀ i : Fin 2 × Fin 56,
      Disjoint (h.rotationOrbitFinset (copyBase d hd i)) (residual d hd)
  cover :
    ∀ d : ZMod 19, ∀ hd : d ≠ 0,
      (Finset.univ : Finset (Fin 2 × Fin 56)).biUnion
            (fun i => h.rotationOrbitFinset (copyBase d hd i)) ∪
          residual d hd =
        (Finset.univ : Finset V)
  residual_contribution :
    ∀ d : ZMod 19, ∀ hd : d ≠ 0,
      ((residual d hd).filter fun y => Γ.Adj y (h.rotation d y)).card = 38
  copy_contribution :
    ∀ d : ZMod 19, ∀ hd : d ≠ 0, ∀ side : Fin 2, ∀ q : Fin 56,
      ((h.rotationOrbitFinset (copyBase d hd (side, q))).filter fun y =>
          Γ.Adj y (h.rotation d y)).card =
        ((h.rotationOrbitFinset (base q)).filter fun y =>
          Γ.Adj y (h.rotation d y)).card

namespace AdjacentMovedOrbitCopyPartition38Witness

variable {h : D19ActsOnMoore57 V Γ}
variable {base : Fin 56 → V}

/-- The actual piece finset used by an orbit-copy witness. -/
noncomputable def pieces
    (w : AdjacentMovedOrbitCopyPartition38Witness h base)
    (d : ZMod 19) (hd : d ≠ 0) (i : Fin 2 × Fin 56) : Finset V :=
  h.rotationOrbitFinset (w.copyBase d hd i)

/-- Forget the orbit-copy presentation to the existing two-copy partition
witness. -/
noncomputable def toTwoCopyPartition38Witness
    (w : AdjacentMovedOrbitCopyPartition38Witness h base) :
    AdjacentMovedTwoCopyPartition38Witness h base where
  pieces := w.pieces
  residual := w.residual
  pairwise_disjoint := by
    intro d hd
    simpa [pieces] using w.pairwise_disjoint d hd
  residual_disjoint := by
    intro d hd i
    simpa [pieces] using w.residual_disjoint d hd i
  cover := by
    intro d hd
    simpa [pieces] using w.cover d hd
  residual_contribution := w.residual_contribution
  copy_contribution := by
    intro d hd side q
    simpa [pieces] using w.copy_contribution d hd side q

/-- The orbit-copy witness gives the adjacent-moved decomposition with
residual contribution constantly `38`. -/
noncomputable def toDecomposition
    (w : AdjacentMovedOrbitCopyPartition38Witness h base) :
    D19AdjacentMovedDecomposition h base fixedOrAContribution38 :=
  w.toTwoCopyPartition38Witness.toDecomposition

/-- The orbit-copy witness gives the `a1` decomposition with the residual term
written as `38`. -/
theorem a1_decomposition
    (w : AdjacentMovedOrbitCopyPartition38Witness h base) :
    ∀ d : ZMod 19, d ≠ 0 →
      h.a1 d =
        38 +
          2 * (∑ q : Fin 56,
            ((h.rotationOrbitFinset (base q)).filter fun y =>
              Γ.Adj y (h.rotation d y)).card) :=
  w.toTwoCopyPartition38Witness.a1_decomposition

end AdjacentMovedOrbitCopyPartition38Witness

namespace AdjacentMovedTwoCopyPartition38Witness

variable {h : D19ActsOnMoore57 V Γ}
variable {base : Fin 56 → V}

/-- Constructor wrapper for the orbit-copy criterion. -/
noncomputable def of_orbitCopyPartition
    (w : AdjacentMovedOrbitCopyPartition38Witness h base) :
    AdjacentMovedTwoCopyPartition38Witness h base :=
  w.toTwoCopyPartition38Witness

end AdjacentMovedTwoCopyPartition38Witness

namespace D19AdjacentMovedDecomposition

variable {h : D19ActsOnMoore57 V Γ}
variable {base : Fin 56 → V}

/-- Constructor wrapper for an adjacent-moved decomposition whose two-copy
pieces are rotation-orbit finsets. -/
noncomputable def of_orbitCopyPartition38
    (w : AdjacentMovedOrbitCopyPartition38Witness h base) :
    D19AdjacentMovedDecomposition h base fixedOrAContribution38 :=
  w.toDecomposition

end D19AdjacentMovedDecomposition

end Moore57
