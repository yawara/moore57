import Moore57.D19OnMoore57.AdjacentMoved.Symmetry
import Moore57.D19OnMoore57.AdjacentMoved.OrbitCopyCriteria
import Moore57.D19OnMoore57.Reflection.OrbitTools

/-!
# Reflection-copy criteria for adjacent-moved two-copy witnesses

This file packages the common case where the second copy of each base rotation
orbit is obtained by applying one fixed reflection to the first copy.
-/

namespace Moore57

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- The base point for a two-copy orbit family where side `0` is the original
base and side `1` is its image under one fixed reflection. -/
def reflectionCopyBase
    (h : D19ActsOnMoore57 V Γ) (base : Fin 56 → V) (k : ZMod 19)
    (i : Fin 2 × Fin 56) : V :=
  if i.1 = 0 then base i.2 else h.smul (DihedralGroup.sr k) (base i.2)

/-- A two-copy partition criterion in which the second copy is a reflection of
the first one.

The reflection transports the `d`-adjacent-moved count on the reflected orbit
to the `-d` count on the original orbit; the base-orbit symmetry between `d`
and `-d` is supplied by `AdjacentMovedSymmetry`. -/
structure AdjacentMovedReflectionCopyPartition38Witness
    (h : D19ActsOnMoore57 V Γ) (base : Fin 56 → V) where
  k : ZMod 19
  residual :
    ∀ d : ZMod 19, d ≠ 0 → Finset V
  pairwise_disjoint :
    ∀ d : ZMod 19, ∀ _hd : d ≠ 0,
      ((Finset.univ : Finset (Fin 2 × Fin 56)) :
        Set (Fin 2 × Fin 56)).PairwiseDisjoint
          (fun i => h.rotationOrbitFinset (reflectionCopyBase h base k i))
  residual_disjoint :
    ∀ d : ZMod 19, ∀ hd : d ≠ 0, ∀ i : Fin 2 × Fin 56,
      Disjoint
        (h.rotationOrbitFinset (reflectionCopyBase h base k i))
        (residual d hd)
  cover :
    ∀ d : ZMod 19, ∀ hd : d ≠ 0,
      (Finset.univ : Finset (Fin 2 × Fin 56)).biUnion
            (fun i => h.rotationOrbitFinset (reflectionCopyBase h base k i)) ∪
          residual d hd =
        (Finset.univ : Finset V)
  residual_contribution :
    ∀ d : ZMod 19, ∀ hd : d ≠ 0,
      ((residual d hd).filter fun y => Γ.Adj y (h.rotation d y)).card = 38

namespace AdjacentMovedReflectionCopyPartition38Witness

variable {h : D19ActsOnMoore57 V Γ}
variable {base : Fin 56 → V}

/-- Forget the reflection-copy presentation to the orbit-copy criterion. -/
noncomputable def toOrbitCopyPartition38Witness
    (w : AdjacentMovedReflectionCopyPartition38Witness h base) :
    AdjacentMovedOrbitCopyPartition38Witness h base where
  copyBase := fun _ _ i => reflectionCopyBase h base w.k i
  residual := w.residual
  pairwise_disjoint := by
    intro d hd
    simpa using w.pairwise_disjoint d hd
  residual_disjoint := by
    intro d hd i
    simpa using w.residual_disjoint d hd i
  cover := by
    intro d hd
    simpa using w.cover d hd
  residual_contribution := w.residual_contribution
  copy_contribution := by
    intro d hd side q
    fin_cases side
    · simp [reflectionCopyBase]
    · have hreflection :=
        h.reflection_filter_adjacent_rotation_moved_card_eq w.k (-d) (base q)
      calc
        ((h.rotationOrbitFinset
              (reflectionCopyBase h base w.k (1, q))).filter fun y =>
            Γ.Adj y (h.rotation d y)).card =
            ((h.rotationOrbitFinset
                (h.smul (DihedralGroup.sr w.k) (base q))).filter fun y =>
              Γ.Adj y (h.rotation d y)).card := by
              simp [reflectionCopyBase]
        _ =
            ((h.rotationOrbitFinset (base q)).filter fun y =>
              Γ.Adj y (h.rotation (-d) y)).card := by
              simpa using hreflection
        _ =
            ((h.rotationOrbitFinset (base q)).filter fun y =>
              Γ.Adj y (h.rotation d y)).card :=
              h.rotationOrbitFinset_filter_adjacent_rotation_moved_card_neg_eq
                (base q) d

/-- Forget the reflection-copy presentation directly to the two-copy witness. -/
noncomputable def toTwoCopyPartition38Witness
    (w : AdjacentMovedReflectionCopyPartition38Witness h base) :
    AdjacentMovedTwoCopyPartition38Witness h base :=
  w.toOrbitCopyPartition38Witness.toTwoCopyPartition38Witness

/-- The reflection-copy witness gives the adjacent-moved decomposition with
residual contribution constantly `38`. -/
noncomputable def toDecomposition
    (w : AdjacentMovedReflectionCopyPartition38Witness h base) :
    D19AdjacentMovedDecomposition h base fixedOrAContribution38 :=
  w.toOrbitCopyPartition38Witness.toDecomposition

end AdjacentMovedReflectionCopyPartition38Witness

namespace AdjacentMovedOrbitCopyPartition38Witness

variable {h : D19ActsOnMoore57 V Γ}
variable {base : Fin 56 → V}

/-- Constructor wrapper for the reflection-copy criterion. -/
noncomputable def of_reflectionCopyPartition
    (w : AdjacentMovedReflectionCopyPartition38Witness h base) :
    AdjacentMovedOrbitCopyPartition38Witness h base :=
  w.toOrbitCopyPartition38Witness

end AdjacentMovedOrbitCopyPartition38Witness

namespace AdjacentMovedTwoCopyPartition38Witness

variable {h : D19ActsOnMoore57 V Γ}
variable {base : Fin 56 → V}

/-- Constructor wrapper for the reflection-copy criterion. -/
noncomputable def of_reflectionCopyPartition
    (w : AdjacentMovedReflectionCopyPartition38Witness h base) :
    AdjacentMovedTwoCopyPartition38Witness h base :=
  w.toTwoCopyPartition38Witness

end AdjacentMovedTwoCopyPartition38Witness

namespace D19AdjacentMovedDecomposition

variable {h : D19ActsOnMoore57 V Γ}
variable {base : Fin 56 → V}

/-- Constructor wrapper for a reflection-copy adjacent-moved decomposition. -/
noncomputable def of_reflectionCopyPartition38
    (w : AdjacentMovedReflectionCopyPartition38Witness h base) :
    D19AdjacentMovedDecomposition h base fixedOrAContribution38 :=
  w.toDecomposition

end D19AdjacentMovedDecomposition

end Moore57
