import Moore57.D19OnMoore57.AdjacentMoved.ReflectionConstantResidual

/-!
# Reflection-copy criteria with complement residual

This file packages the canonical residual for a reflection-copy orbit family:
the complement of the union of the copied rotation-orbit pieces.
-/

namespace Moore57

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- The union of all reflection-copy rotation-orbit pieces. -/
noncomputable def reflectionCopyUnion
    (h : D19ActsOnMoore57 V Γ) (base : Fin 56 → V) (k : ZMod 19) :
    Finset V :=
  (Finset.univ : Finset (Fin 2 × Fin 56)).biUnion
    (fun i => h.rotationOrbitFinset (reflectionCopyBase h base k i))

/-- The canonical residual: the complement of the reflection-copy orbit union. -/
noncomputable def reflectionCopyResidual
    (h : D19ActsOnMoore57 V Γ) (base : Fin 56 → V) (k : ZMod 19) :
    Finset V :=
  (reflectionCopyUnion h base k)ᶜ

/-- Each reflection-copy orbit piece is disjoint from the canonical residual. -/
theorem reflectionCopyResidual_disjoint
    (h : D19ActsOnMoore57 V Γ) (base : Fin 56 → V) (k : ZMod 19)
    (i : Fin 2 × Fin 56) :
    Disjoint
      (h.rotationOrbitFinset (reflectionCopyBase h base k i))
      (reflectionCopyResidual h base k) := by
  classical
  have hsubset :
      h.rotationOrbitFinset (reflectionCopyBase h base k i) ≤
        reflectionCopyUnion h base k := by
    change
      h.rotationOrbitFinset (reflectionCopyBase h base k i) ≤
        (Finset.univ : Finset (Fin 2 × Fin 56)).biUnion
        (fun i => h.rotationOrbitFinset (reflectionCopyBase h base k i))
    exact Finset.subset_biUnion_of_mem
      (fun i => h.rotationOrbitFinset (reflectionCopyBase h base k i))
      (Finset.mem_univ i)
  simpa [reflectionCopyResidual] using LE.le.disjoint_compl_right hsubset

/-- The reflection-copy orbit union together with its canonical residual covers
all vertices. -/
theorem reflectionCopyResidual_cover
    (h : D19ActsOnMoore57 V Γ) (base : Fin 56 → V) (k : ZMod 19) :
    reflectionCopyUnion h base k ∪ reflectionCopyResidual h base k =
      (Finset.univ : Finset V) := by
  classical
  simp [reflectionCopyResidual]

namespace AdjacentMovedReflectionConstantResidual38Witness

variable {h : D19ActsOnMoore57 V Γ}
variable {base : Fin 56 → V}

/-- Build a constant-residual reflection-copy witness using the canonical
complement of the reflection-copy orbit union as residual. -/
noncomputable def of_complementResidual
    (k : ZMod 19)
    (pairwise_disjoint :
      ((Finset.univ : Finset (Fin 2 × Fin 56)) :
        Set (Fin 2 × Fin 56)).PairwiseDisjoint
          (fun i => h.rotationOrbitFinset (reflectionCopyBase h base k i)))
    (residual_contribution :
      ∀ d : ZMod 19, ∀ _hd : d ≠ 0,
        ((reflectionCopyResidual h base k).filter fun y =>
          Γ.Adj y (h.rotation d y)).card = 38) :
    AdjacentMovedReflectionConstantResidual38Witness h base where
  k := k
  residual := reflectionCopyResidual h base k
  pairwise_disjoint := pairwise_disjoint
  residual_disjoint := by
    intro i
    exact reflectionCopyResidual_disjoint h base k i
  cover := by
    simpa [reflectionCopyUnion] using reflectionCopyResidual_cover h base k
  residual_contribution := residual_contribution

end AdjacentMovedReflectionConstantResidual38Witness

end Moore57
