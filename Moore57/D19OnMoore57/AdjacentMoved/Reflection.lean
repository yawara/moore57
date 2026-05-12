import Moore57.D19OnMoore57.AdjacentMoved.OrbitCopyCriteria
import Moore57.D19OnMoore57.AdjacentMoved.Symmetry
import Moore57.D19OnMoore57.Orbit.BaseSelectionInputBridge
import Moore57.D19OnMoore57.Orbit.BaseSelectionInputs
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

/-!
# Reflection-copy pairwise disjointness from base and cross disjointness

This file packages the disjointness bookkeeping for reflection-copy orbit
families.  Base/base disjointness comes from `OrbitBaseSelectionInput`, the
mixed base/reflection cases are supplied as a cross-disjointness hypothesis,
and reflection/reflection disjointness is transported across the reflection.
-/

namespace Moore57

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

namespace D19ActsOnMoore57

variable (h : D19ActsOnMoore57 V Γ)

/-- A reflection transports disjointness of rotation orbits to disjointness of
the reflected rotation orbits. -/
theorem disjoint_reflection_rotationOrbitFinset_of_disjoint
    (k : ZMod 19) {x y : V}
    (hdisj : Disjoint (h.rotationOrbitFinset x) (h.rotationOrbitFinset y)) :
    Disjoint
      (h.rotationOrbitFinset (h.smul (DihedralGroup.sr k) x))
      (h.rotationOrbitFinset (h.smul (DihedralGroup.sr k) y)) := by
  classical
  rw [← h.reflection_image_rotationOrbitFinset k x,
    ← h.reflection_image_rotationOrbitFinset k y]
  rw [Finset.disjoint_left]
  intro z hzx hzy
  rcases Finset.mem_image.mp hzx with ⟨x', hx', hx'z⟩
  rcases Finset.mem_image.mp hzy with ⟨y', hy', hy'z⟩
  have hxy : x' = y' :=
    (h.smulEquiv (DihedralGroup.sr k)).injective (hx'z.trans hy'z.symm)
  exact Finset.disjoint_left.mp hdisj hx' (hxy ▸ hy')

/-- Reflection-copy orbit families are pairwise disjoint when the selected
base orbits are pairwise disjoint and every original orbit is disjoint from
every reflected orbit. -/
theorem pairwiseDisjoint_reflectionCopyBase_of_base_cross
    (input : OrbitBaseSelectionInput h) (k : ZMod 19)
    (hcross : ∀ q r : Fin 56,
      Disjoint
        (h.rotationOrbitFinset (input.base q))
        (h.rotationOrbitFinset (h.smul (DihedralGroup.sr k) (input.base r)))) :
    ((Finset.univ : Finset (Fin 2 × Fin 56)) : Set (Fin 2 × Fin 56)).PairwiseDisjoint
      (fun i => h.rotationOrbitFinset (reflectionCopyBase h input.base k i)) := by
  classical
  intro i _hi j _hj hij
  rcases i with ⟨side, q⟩
  rcases j with ⟨side', r⟩
  fin_cases side <;> fin_cases side'
  · have hqr : q ≠ r := by
      intro hqr
      exact hij (by simp [hqr])
    simpa [reflectionCopyBase] using input.pairwise_disjoint q r hqr
  · simpa [reflectionCopyBase] using hcross q r
  · simpa [reflectionCopyBase] using (hcross r q).symm
  · have hqr : q ≠ r := by
      intro hqr
      exact hij (by simp [hqr])
    simpa [reflectionCopyBase] using
      h.disjoint_reflection_rotationOrbitFinset_of_disjoint k
        (input.pairwise_disjoint q r hqr)

end D19ActsOnMoore57

end Moore57

/-!
# Reflection-copy criteria with constant residual

This file packages the special case of
`AdjacentMovedReflectionCopyPartition38Witness` where the residual finset is
independent of the nontrivial rotation `d`.
-/

namespace Moore57

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- A reflection-copy partition criterion whose residual finset is fixed for
all nontrivial rotations.

The orbit pieces are already independent of `d` in the underlying
reflection-copy criterion.  This witness additionally makes the residual
independent of `d`; only the filtered residual contribution still ranges over
the nontrivial rotations. -/
structure AdjacentMovedReflectionConstantResidual38Witness
    (h : D19ActsOnMoore57 V Γ) (base : Fin 56 → V) where
  k : ZMod 19
  residual : Finset V
  pairwise_disjoint :
    ((Finset.univ : Finset (Fin 2 × Fin 56)) :
      Set (Fin 2 × Fin 56)).PairwiseDisjoint
        (fun i => h.rotationOrbitFinset (reflectionCopyBase h base k i))
  residual_disjoint :
    ∀ i : Fin 2 × Fin 56,
      Disjoint
        (h.rotationOrbitFinset (reflectionCopyBase h base k i))
        residual
  cover :
    (Finset.univ : Finset (Fin 2 × Fin 56)).biUnion
          (fun i => h.rotationOrbitFinset (reflectionCopyBase h base k i)) ∪
        residual =
      (Finset.univ : Finset V)
  residual_contribution :
    ∀ d : ZMod 19, ∀ _hd : d ≠ 0,
      (residual.filter fun y => Γ.Adj y (h.rotation d y)).card = 38

namespace AdjacentMovedReflectionConstantResidual38Witness

variable {h : D19ActsOnMoore57 V Γ}
variable {base : Fin 56 → V}

/-- Forget the constant-residual presentation to the existing reflection-copy
criterion. -/
noncomputable def toReflectionCopyPartition38Witness
    (w : AdjacentMovedReflectionConstantResidual38Witness h base) :
    AdjacentMovedReflectionCopyPartition38Witness h base where
  k := w.k
  residual := fun _ _ => w.residual
  pairwise_disjoint := by
    intro d hd
    simpa using w.pairwise_disjoint
  residual_disjoint := by
    intro d hd i
    simpa using w.residual_disjoint i
  cover := by
    intro d hd
    simpa using w.cover
  residual_contribution := by
    intro d hd
    simpa using w.residual_contribution d hd

/-- Forget the constant-residual presentation to the orbit-copy criterion. -/
noncomputable def toOrbitCopyPartition38Witness
    (w : AdjacentMovedReflectionConstantResidual38Witness h base) :
    AdjacentMovedOrbitCopyPartition38Witness h base :=
  w.toReflectionCopyPartition38Witness.toOrbitCopyPartition38Witness

/-- Forget the constant-residual presentation directly to the two-copy
witness. -/
noncomputable def toTwoCopyPartition38Witness
    (w : AdjacentMovedReflectionConstantResidual38Witness h base) :
    AdjacentMovedTwoCopyPartition38Witness h base :=
  w.toReflectionCopyPartition38Witness.toTwoCopyPartition38Witness

/-- The constant-residual reflection-copy witness gives the adjacent-moved
decomposition with residual contribution constantly `38`. -/
noncomputable def toDecomposition
    (w : AdjacentMovedReflectionConstantResidual38Witness h base) :
    D19AdjacentMovedDecomposition h base fixedOrAContribution38 :=
  w.toReflectionCopyPartition38Witness.toDecomposition

end AdjacentMovedReflectionConstantResidual38Witness

namespace AdjacentMovedReflectionCopyPartition38Witness

variable {h : D19ActsOnMoore57 V Γ}
variable {base : Fin 56 → V}

/-- Constructor wrapper for the constant-residual reflection-copy criterion. -/
noncomputable def of_constantResidual
    (w : AdjacentMovedReflectionConstantResidual38Witness h base) :
    AdjacentMovedReflectionCopyPartition38Witness h base :=
  w.toReflectionCopyPartition38Witness

end AdjacentMovedReflectionCopyPartition38Witness

namespace AdjacentMovedTwoCopyPartition38Witness

variable {h : D19ActsOnMoore57 V Γ}
variable {base : Fin 56 → V}

/-- Constructor wrapper for the constant-residual reflection-copy criterion. -/
noncomputable def of_reflectionConstantResidual
    (w : AdjacentMovedReflectionConstantResidual38Witness h base) :
    AdjacentMovedTwoCopyPartition38Witness h base :=
  w.toTwoCopyPartition38Witness

end AdjacentMovedTwoCopyPartition38Witness

namespace D19AdjacentMovedDecomposition

variable {h : D19ActsOnMoore57 V Γ}
variable {base : Fin 56 → V}

/-- Constructor wrapper for a constant-residual reflection-copy adjacent-moved
decomposition. -/
noncomputable def of_reflectionConstantResidual38
    (w : AdjacentMovedReflectionConstantResidual38Witness h base) :
    D19AdjacentMovedDecomposition h base fixedOrAContribution38 :=
  w.toDecomposition

end D19AdjacentMovedDecomposition

end Moore57

-- The orbit-family membership proof below elaborates through several nested
-- finset and orbit-membership equivalences.
set_option maxRecDepth 10000

/-!
# Reflection-copy cross disjointness from avoidance

This file reduces the mixed original/reflection orbit disjointness condition to
the smaller condition that no reflected selected base lies in the selected
rotation-orbit union.
-/

namespace Moore57

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

namespace D19ActsOnMoore57

variable (h : D19ActsOnMoore57 V Γ)

/-- Rotation orbit membership is symmetric: if `y` is a rotation translate of
`x`, then `x` is a rotation translate of `y`. -/
theorem rotationOrbitFinset_mem_symm {x y : V}
    (hy : y ∈ h.rotationOrbitFinset x) :
    x ∈ h.rotationOrbitFinset y := by
  rcases (h.mem_rotationOrbitFinset x y).mp hy with ⟨i, rfl⟩
  exact (h.mem_rotationOrbitFinset (h.rotation i x) x).mpr
    ⟨-i, by
      calc
        h.rotation (-i) (h.rotation i x)
            = (h.rotation (-i) * h.rotation i) x := by
                simp [Equiv.Perm.mul_apply]
        _ = h.rotation ((-i) + i) x := by
                rw [← h.rotation_add]
        _ = x := by
                simp⟩

/-- If no reflected selected base point lies in the selected orbit-family
union, then every selected orbit is disjoint from every reflected selected
orbit. -/
theorem cross_disjoint_of_reflection_not_mem_orbitFamilyUnion
    (input : OrbitBaseSelectionInput h) (k : ZMod 19)
    (havoid : ∀ r : Fin 56,
      h.smul (DihedralGroup.sr k) (input.base r) ∉ input.orbitFamilyUnion) :
    ∀ q r : Fin 56,
      Disjoint
        (h.rotationOrbitFinset (input.base q))
        (h.rotationOrbitFinset (h.smul (DihedralGroup.sr k) (input.base r))) := by
  classical
  intro q r
  rw [Finset.disjoint_left]
  intro y hyq hyr
  have href_in_orbit_y :
      h.smul (DihedralGroup.sr k) (input.base r) ∈ h.rotationOrbitFinset y :=
    h.rotationOrbitFinset_mem_symm hyr
  rcases (h.mem_rotationOrbitFinset y
      (h.smul (DihedralGroup.sr k) (input.base r))).mp href_in_orbit_y with
    ⟨j, hj⟩
  rcases (h.mem_rotationOrbitFinset (input.base q) y).mp hyq with ⟨i, rfl⟩
  have href_eq :
      h.rotation (j + i) (input.base q) =
        h.smul (DihedralGroup.sr k) (input.base r) := by
    calc
      h.rotation (j + i) (input.base q)
          = (h.rotation j * h.rotation i) (input.base q) := by
              rw [h.rotation_add]
      _ = h.rotation j (h.rotation i (input.base q)) := by
              simp [Equiv.Perm.mul_apply]
      _ = h.smul (DihedralGroup.sr k) (input.base r) := hj
  have hrefUnion :
      h.smul (DihedralGroup.sr k) (input.base r) ∈ input.orbitFamilyUnion := by
    have hrefUnion' :
        h.smul (DihedralGroup.sr k) (input.base r) ∈
          h.orbitFamilyUnion input.base :=
      (h.mem_orbitFamilyUnion input.base
        (h.smul (DihedralGroup.sr k) (input.base r))).mpr
          ⟨q, j + i, href_eq⟩
    simpa [OrbitBaseSelectionInput.orbitFamilyUnion] using hrefUnion'
  exact (havoid r) hrefUnion

/-- Constructor wrapper: the reflected-base avoidance condition gives the
pairwise disjointness of the two reflection-copy orbit families. -/
theorem pairwiseDisjoint_reflectionCopyBase_of_reflection_not_mem_orbitFamilyUnion
    (input : OrbitBaseSelectionInput h) (k : ZMod 19)
    (havoid : ∀ r : Fin 56,
      h.smul (DihedralGroup.sr k) (input.base r) ∉ input.orbitFamilyUnion) :
    ((Finset.univ : Finset (Fin 2 × Fin 56)) : Set (Fin 2 × Fin 56)).PairwiseDisjoint
      (fun i => h.rotationOrbitFinset (reflectionCopyBase h input.base k i)) :=
  h.pairwiseDisjoint_reflectionCopyBase_of_base_cross input k
    (h.cross_disjoint_of_reflection_not_mem_orbitFamilyUnion input k havoid)

end D19ActsOnMoore57

end Moore57

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

/-!
# Compact reflection-copy criteria

This file packages the smallest current reflection-copy adjacent-moved
criterion over an `OrbitBaseSelectionInput`: original/reflected cross
disjointness plus the filtered count of the canonical complement residual.
-/

namespace Moore57

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- Compact witness for the canonical complement-residual reflection-copy
criterion based on an orbit-base selection input.

The base/base and reflected/reflected disjointness are derived from
`OrbitBaseSelectionInput`; the mixed cases are exactly the `cross_disjoint`
field.  The residual is the complement of the copied orbit union. -/
structure AdjacentMovedReflectionComplementResidual38Witness
    (h : D19ActsOnMoore57 V Γ) (input : OrbitBaseSelectionInput h) where
  k : ZMod 19
  cross_disjoint :
    ∀ q r : Fin 56,
      Disjoint
        (h.rotationOrbitFinset (input.base q))
        (h.rotationOrbitFinset
          (h.smul (DihedralGroup.sr k) (input.base r)))
  residual_contribution :
    ∀ d : ZMod 19, ∀ _hd : d ≠ 0,
      ((reflectionCopyResidual h input.base k).filter fun y =>
        Γ.Adj y (h.rotation d y)).card = 38

namespace AdjacentMovedReflectionComplementResidual38Witness

variable {h : D19ActsOnMoore57 V Γ}
variable {input : OrbitBaseSelectionInput h}

/-- Convert the compact complement-residual witness to the existing
constant-residual reflection-copy witness. -/
noncomputable def toConstantResidual38Witness
    (w : AdjacentMovedReflectionComplementResidual38Witness h input) :
    AdjacentMovedReflectionConstantResidual38Witness h input.base :=
  AdjacentMovedReflectionConstantResidual38Witness.of_complementResidual
    (h := h) (base := input.base) w.k
    (h.pairwiseDisjoint_reflectionCopyBase_of_base_cross
      input w.k w.cross_disjoint)
    w.residual_contribution

/-- Convert the compact complement-residual witness to the reflection-copy
partition witness. -/
noncomputable def toReflectionCopyPartition38Witness
    (w : AdjacentMovedReflectionComplementResidual38Witness h input) :
    AdjacentMovedReflectionCopyPartition38Witness h input.base :=
  w.toConstantResidual38Witness.toReflectionCopyPartition38Witness

/-- Convert the compact complement-residual witness to the two-copy witness. -/
noncomputable def toTwoCopyPartition38Witness
    (w : AdjacentMovedReflectionComplementResidual38Witness h input) :
    AdjacentMovedTwoCopyPartition38Witness h input.base :=
  w.toConstantResidual38Witness.toTwoCopyPartition38Witness

/-- The compact complement-residual witness gives the adjacent-moved
decomposition with residual contribution constantly `38`. -/
noncomputable def toDecomposition
    (w : AdjacentMovedReflectionComplementResidual38Witness h input) :
    D19AdjacentMovedDecomposition h input.base fixedOrAContribution38 :=
  w.toConstantResidual38Witness.toDecomposition

end AdjacentMovedReflectionComplementResidual38Witness

namespace AdjacentMovedReflectionConstantResidual38Witness

variable {h : D19ActsOnMoore57 V Γ}
variable {input : OrbitBaseSelectionInput h}

/-- Constructor wrapper for the compact complement-residual criterion. -/
noncomputable def of_compactComplementResidual
    (w : AdjacentMovedReflectionComplementResidual38Witness h input) :
    AdjacentMovedReflectionConstantResidual38Witness h input.base :=
  w.toConstantResidual38Witness

end AdjacentMovedReflectionConstantResidual38Witness

end Moore57

/-!
# Compact reflection-copy criteria with split complement residual

This file refines the compact complement-residual witness by allowing the
canonical residual to be supplied as a disjoint union of two pieces, such as the
fixed-vertex side and an `A`-side contribution.
-/

namespace Moore57

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- A compact complement-residual reflection-copy criterion whose canonical
residual is split into two disjoint finsets.

The final compact residual contribution is proved from the two filtered
contributions using `Finset.card_union_of_disjoint`. -/
structure AdjacentMovedReflectionComplementResidualSplit38Witness
    (h : D19ActsOnMoore57 V Γ) (input : OrbitBaseSelectionInput h) where
  k : ZMod 19
  cross_disjoint :
    ∀ q r : Fin 56,
      Disjoint
        (h.rotationOrbitFinset (input.base q))
        (h.rotationOrbitFinset
          (h.smul (DihedralGroup.sr k) (input.base r)))
  fixedPart : Finset V
  aPart : Finset V
  parts_disjoint : Disjoint fixedPart aPart
  residual_eq :
    reflectionCopyResidual h input.base k = fixedPart ∪ aPart
  residual_contribution :
    ∀ d : ZMod 19, ∀ _hd : d ≠ 0,
      (fixedPart.filter fun y => Γ.Adj y (h.rotation d y)).card +
          (aPart.filter fun y => Γ.Adj y (h.rotation d y)).card =
        38

namespace AdjacentMovedReflectionComplementResidualSplit38Witness

variable {h : D19ActsOnMoore57 V Γ}
variable {input : OrbitBaseSelectionInput h}

/-- The two split residual pieces are disjoint after filtering by any
predicate. -/
theorem filter_parts_disjoint
    (w : AdjacentMovedReflectionComplementResidualSplit38Witness h input)
    (p : V → Prop) [DecidablePred p] :
    Disjoint (w.fixedPart.filter p) (w.aPart.filter p) :=
  Disjoint.mono (Finset.filter_subset p w.fixedPart)
    (Finset.filter_subset p w.aPart) w.parts_disjoint

/-- The filtered cardinality of the canonical complement residual is the sum of
the filtered cardinalities of its two supplied pieces. -/
theorem residual_filter_card
    (w : AdjacentMovedReflectionComplementResidualSplit38Witness h input)
    (p : V → Prop) [DecidablePred p] :
    ((reflectionCopyResidual h input.base w.k).filter p).card =
      (w.fixedPart.filter p).card + (w.aPart.filter p).card := by
  classical
  rw [w.residual_eq, Finset.filter_union]
  exact Finset.card_union_of_disjoint (w.filter_parts_disjoint p)

/-- Forget the split presentation to the compact complement-residual
criterion. -/
noncomputable def toComplementResidual38Witness
    (w : AdjacentMovedReflectionComplementResidualSplit38Witness h input) :
    AdjacentMovedReflectionComplementResidual38Witness h input where
  k := w.k
  cross_disjoint := w.cross_disjoint
  residual_contribution := by
    intro d hd
    rw [w.residual_filter_card (fun y => Γ.Adj y (h.rotation d y))]
    exact w.residual_contribution d hd

/-- Convert the split compact complement-residual witness to the existing
constant-residual reflection-copy witness. -/
noncomputable def toConstantResidual38Witness
    (w : AdjacentMovedReflectionComplementResidualSplit38Witness h input) :
    AdjacentMovedReflectionConstantResidual38Witness h input.base :=
  w.toComplementResidual38Witness.toConstantResidual38Witness

/-- Convert the split compact complement-residual witness to the reflection-copy
partition witness. -/
noncomputable def toReflectionCopyPartition38Witness
    (w : AdjacentMovedReflectionComplementResidualSplit38Witness h input) :
    AdjacentMovedReflectionCopyPartition38Witness h input.base :=
  w.toComplementResidual38Witness.toReflectionCopyPartition38Witness

/-- Convert the split compact complement-residual witness to the two-copy
witness. -/
noncomputable def toTwoCopyPartition38Witness
    (w : AdjacentMovedReflectionComplementResidualSplit38Witness h input) :
    AdjacentMovedTwoCopyPartition38Witness h input.base :=
  w.toComplementResidual38Witness.toTwoCopyPartition38Witness

/-- The split compact complement-residual witness gives the adjacent-moved
decomposition with residual contribution constantly `38`. -/
noncomputable def toDecomposition
    (w : AdjacentMovedReflectionComplementResidualSplit38Witness h input) :
    D19AdjacentMovedDecomposition h input.base fixedOrAContribution38 :=
  w.toComplementResidual38Witness.toDecomposition

end AdjacentMovedReflectionComplementResidualSplit38Witness

namespace AdjacentMovedReflectionComplementResidual38Witness

variable {h : D19ActsOnMoore57 V Γ}
variable {input : OrbitBaseSelectionInput h}

/-- Constructor wrapper for the split compact complement-residual criterion. -/
noncomputable def of_splitComplementResidual
    (w : AdjacentMovedReflectionComplementResidualSplit38Witness h input) :
    AdjacentMovedReflectionComplementResidual38Witness h input :=
  w.toComplementResidual38Witness

end AdjacentMovedReflectionComplementResidual38Witness

namespace AdjacentMovedReflectionConstantResidual38Witness

variable {h : D19ActsOnMoore57 V Γ}
variable {input : OrbitBaseSelectionInput h}

/-- Constructor wrapper from the split compact complement-residual criterion to
the constant-residual reflection-copy criterion. -/
noncomputable def of_compactSplitComplementResidual
    (w : AdjacentMovedReflectionComplementResidualSplit38Witness h input) :
    AdjacentMovedReflectionConstantResidual38Witness h input.base :=
  w.toConstantResidual38Witness

end AdjacentMovedReflectionConstantResidual38Witness

end Moore57

/-!
# Constructor wrappers for compact reflection-copy criteria

This file exposes namespace-local constructors from the compact
complement-residual witness to the existing adjacent-moved witness layers.
-/

namespace Moore57

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

namespace AdjacentMovedReflectionCopyPartition38Witness

variable {h : D19ActsOnMoore57 V Γ}
variable {input : OrbitBaseSelectionInput h}

/-- Constructor wrapper for the compact complement-residual criterion. -/
noncomputable def of_compactComplementResidual
    (w : AdjacentMovedReflectionComplementResidual38Witness h input) :
    AdjacentMovedReflectionCopyPartition38Witness h input.base :=
  w.toReflectionCopyPartition38Witness

end AdjacentMovedReflectionCopyPartition38Witness

namespace AdjacentMovedTwoCopyPartition38Witness

variable {h : D19ActsOnMoore57 V Γ}
variable {input : OrbitBaseSelectionInput h}

/-- Constructor wrapper for the compact complement-residual criterion. -/
noncomputable def of_compactComplementResidual
    (w : AdjacentMovedReflectionComplementResidual38Witness h input) :
    AdjacentMovedTwoCopyPartition38Witness h input.base :=
  w.toTwoCopyPartition38Witness

end AdjacentMovedTwoCopyPartition38Witness

namespace D19AdjacentMovedDecomposition

variable {h : D19ActsOnMoore57 V Γ}
variable {input : OrbitBaseSelectionInput h}

/-- Constructor wrapper for a compact complement-residual adjacent-moved
decomposition. -/
noncomputable def of_compactComplementResidual38
    (w : AdjacentMovedReflectionComplementResidual38Witness h input) :
    D19AdjacentMovedDecomposition h input.base fixedOrAContribution38 :=
  w.toDecomposition

end D19AdjacentMovedDecomposition

end Moore57

/-!
# Avoidance criterion for compact reflection-copy witnesses

This file replaces the all-pairs cross-disjointness field in the compact
reflection-copy criterion by the smaller condition that every reflected base
avoids the selected rotation-orbit union.
-/

namespace Moore57

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- Avoidance-based compact complement-residual reflection-copy criterion.

The avoidance condition says that no reflected selected base belongs to the
selected orbit family.  This implies the mixed original/reflected orbit
disjointness required by `AdjacentMovedReflectionComplementResidual38Witness`.
-/
structure AdjacentMovedReflectionAvoidanceComplementResidual38Witness
    (h : D19ActsOnMoore57 V Γ) (input : OrbitBaseSelectionInput h) where
  k : ZMod 19
  reflection_not_mem_orbitFamilyUnion :
    ∀ r : Fin 56,
      h.smul (DihedralGroup.sr k) (input.base r) ∉ input.orbitFamilyUnion
  residual_contribution :
    ∀ d : ZMod 19, ∀ _hd : d ≠ 0,
      ((reflectionCopyResidual h input.base k).filter fun y =>
        Γ.Adj y (h.rotation d y)).card = 38

namespace AdjacentMovedReflectionAvoidanceComplementResidual38Witness

variable {h : D19ActsOnMoore57 V Γ}
variable {input : OrbitBaseSelectionInput h}

/-- Convert the avoidance-based criterion to the compact complement-residual
witness. -/
noncomputable def toComplementResidual38Witness
    (w : AdjacentMovedReflectionAvoidanceComplementResidual38Witness h input) :
    AdjacentMovedReflectionComplementResidual38Witness h input where
  k := w.k
  cross_disjoint :=
    h.cross_disjoint_of_reflection_not_mem_orbitFamilyUnion
      input w.k w.reflection_not_mem_orbitFamilyUnion
  residual_contribution := w.residual_contribution

/-- Convert the avoidance-based criterion to the constant-residual
reflection-copy witness. -/
noncomputable def toConstantResidual38Witness
    (w : AdjacentMovedReflectionAvoidanceComplementResidual38Witness h input) :
    AdjacentMovedReflectionConstantResidual38Witness h input.base :=
  w.toComplementResidual38Witness.toConstantResidual38Witness

/-- Convert the avoidance-based criterion to the reflection-copy partition
witness. -/
noncomputable def toReflectionCopyPartition38Witness
    (w : AdjacentMovedReflectionAvoidanceComplementResidual38Witness h input) :
    AdjacentMovedReflectionCopyPartition38Witness h input.base :=
  w.toComplementResidual38Witness.toReflectionCopyPartition38Witness

/-- Convert the avoidance-based criterion to the two-copy witness. -/
noncomputable def toTwoCopyPartition38Witness
    (w : AdjacentMovedReflectionAvoidanceComplementResidual38Witness h input) :
    AdjacentMovedTwoCopyPartition38Witness h input.base :=
  w.toComplementResidual38Witness.toTwoCopyPartition38Witness

/-- The avoidance-based criterion gives the adjacent-moved decomposition with
residual contribution constantly `38`. -/
noncomputable def toDecomposition
    (w : AdjacentMovedReflectionAvoidanceComplementResidual38Witness h input) :
    D19AdjacentMovedDecomposition h input.base fixedOrAContribution38 :=
  w.toComplementResidual38Witness.toDecomposition

end AdjacentMovedReflectionAvoidanceComplementResidual38Witness

namespace AdjacentMovedReflectionComplementResidual38Witness

variable {h : D19ActsOnMoore57 V Γ}
variable {input : OrbitBaseSelectionInput h}

/-- Constructor wrapper for the avoidance-based compact criterion. -/
noncomputable def of_reflectionAvoidance
    (w : AdjacentMovedReflectionAvoidanceComplementResidual38Witness h input) :
    AdjacentMovedReflectionComplementResidual38Witness h input :=
  w.toComplementResidual38Witness

end AdjacentMovedReflectionComplementResidual38Witness

end Moore57

/-!
# Avoidance criterion with split complement residual

This file combines the avoidance-based cross-disjointness criterion with the
split presentation of the canonical complement residual.
-/

namespace Moore57

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- Avoidance-based complement-residual criterion with the canonical residual
split into two disjoint pieces. -/
structure AdjacentMovedReflectionAvoidanceSplit38Witness
    (h : D19ActsOnMoore57 V Γ) (input : OrbitBaseSelectionInput h) where
  k : ZMod 19
  reflection_not_mem_orbitFamilyUnion :
    ∀ r : Fin 56,
      h.smul (DihedralGroup.sr k) (input.base r) ∉ input.orbitFamilyUnion
  fixedPart : Finset V
  aPart : Finset V
  parts_disjoint : Disjoint fixedPart aPart
  residual_eq :
    reflectionCopyResidual h input.base k = fixedPart ∪ aPart
  residual_contribution :
    ∀ d : ZMod 19, ∀ _hd : d ≠ 0,
      (fixedPart.filter fun y => Γ.Adj y (h.rotation d y)).card +
          (aPart.filter fun y => Γ.Adj y (h.rotation d y)).card =
        38

namespace AdjacentMovedReflectionAvoidanceSplit38Witness

variable {h : D19ActsOnMoore57 V Γ}
variable {input : OrbitBaseSelectionInput h}

/-- Convert the avoidance split criterion to the compact split witness. -/
noncomputable def toComplementResidualSplit38Witness
    (w : AdjacentMovedReflectionAvoidanceSplit38Witness h input) :
    AdjacentMovedReflectionComplementResidualSplit38Witness h input where
  k := w.k
  cross_disjoint :=
    h.cross_disjoint_of_reflection_not_mem_orbitFamilyUnion
      input w.k w.reflection_not_mem_orbitFamilyUnion
  fixedPart := w.fixedPart
  aPart := w.aPart
  parts_disjoint := w.parts_disjoint
  residual_eq := w.residual_eq
  residual_contribution := w.residual_contribution

/-- Convert the avoidance split criterion to the avoidance compact witness. -/
noncomputable def toAvoidanceComplementResidual38Witness
    (w : AdjacentMovedReflectionAvoidanceSplit38Witness h input) :
    AdjacentMovedReflectionAvoidanceComplementResidual38Witness h input where
  k := w.k
  reflection_not_mem_orbitFamilyUnion := w.reflection_not_mem_orbitFamilyUnion
  residual_contribution := by
    intro d hd
    exact w.toComplementResidualSplit38Witness
      |>.toComplementResidual38Witness
      |>.residual_contribution d hd

/-- Convert the avoidance split criterion to the compact complement-residual
witness. -/
noncomputable def toComplementResidual38Witness
    (w : AdjacentMovedReflectionAvoidanceSplit38Witness h input) :
    AdjacentMovedReflectionComplementResidual38Witness h input :=
  w.toComplementResidualSplit38Witness.toComplementResidual38Witness

/-- Convert the avoidance split criterion to the constant-residual
reflection-copy witness. -/
noncomputable def toConstantResidual38Witness
    (w : AdjacentMovedReflectionAvoidanceSplit38Witness h input) :
    AdjacentMovedReflectionConstantResidual38Witness h input.base :=
  w.toComplementResidual38Witness.toConstantResidual38Witness

/-- The avoidance split criterion gives the adjacent-moved decomposition with
residual contribution constantly `38`. -/
noncomputable def toDecomposition
    (w : AdjacentMovedReflectionAvoidanceSplit38Witness h input) :
    D19AdjacentMovedDecomposition h input.base fixedOrAContribution38 :=
  w.toComplementResidual38Witness.toDecomposition

end AdjacentMovedReflectionAvoidanceSplit38Witness

namespace AdjacentMovedReflectionAvoidanceComplementResidual38Witness

variable {h : D19ActsOnMoore57 V Γ}
variable {input : OrbitBaseSelectionInput h}

/-- Constructor wrapper for the split avoidance criterion. -/
noncomputable def of_splitAvoidance
    (w : AdjacentMovedReflectionAvoidanceSplit38Witness h input) :
    AdjacentMovedReflectionAvoidanceComplementResidual38Witness h input :=
  w.toAvoidanceComplementResidual38Witness

end AdjacentMovedReflectionAvoidanceComplementResidual38Witness

end Moore57

-- The theorem statements below expand through nested indexed finset unions
-- over `Fin 2 × Fin 56` and rotation orbit membership.
set_option maxRecDepth 10000

/-!
# Membership criteria for reflection-copy residuals

This file exposes the canonical complement residual as the vertices that lie in
neither the original selected rotation-orbit family nor its reflected copy.
-/

namespace Moore57

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

namespace D19ActsOnMoore57

variable (h : D19ActsOnMoore57 V Γ)

/-- Membership in the reflection-copy union in indexed form. -/
theorem mem_reflectionCopyUnion_iff
    (base : Fin 56 → V) (k : ZMod 19) (y : V) :
    y ∈ reflectionCopyUnion h base k ↔
      ∃ side : Fin 2, ∃ q : Fin 56, ∃ i : ZMod 19,
        h.rotation i (reflectionCopyBase h base k (side, q)) = y := by
  classical
  constructor
  · intro hy
    change y ∈
      (Finset.univ : Finset (Fin 2 × Fin 56)).biUnion
        (fun sideq =>
          h.rotationOrbitFinset (reflectionCopyBase h base k sideq)) at hy
    rcases Finset.mem_biUnion.mp hy with ⟨sideq, _hsideq, hyOrbit⟩
    rcases sideq with ⟨side, q⟩
    rcases (h.mem_rotationOrbitFinset
        (reflectionCopyBase h base k (side, q)) y).mp hyOrbit with ⟨i, hi⟩
    exact ⟨side, q, i, hi⟩
  · rintro ⟨side, q, i, hi⟩
    change y ∈
      (Finset.univ : Finset (Fin 2 × Fin 56)).biUnion
        (fun sideq =>
          h.rotationOrbitFinset (reflectionCopyBase h base k sideq))
    exact Finset.mem_biUnion.mpr
      ⟨(side, q), Finset.mem_univ _,
        (h.mem_rotationOrbitFinset
          (reflectionCopyBase h base k (side, q)) y).mpr ⟨i, hi⟩⟩

/-- Membership in the reflection-copy union, split into original and reflected
orbit families. -/
theorem mem_reflectionCopyUnion_iff_or
    (base : Fin 56 → V) (k : ZMod 19) (y : V) :
    y ∈ reflectionCopyUnion h base k ↔
      (∃ q : Fin 56, ∃ i : ZMod 19, h.rotation i (base q) = y) ∨
        ∃ q : Fin 56, ∃ i : ZMod 19,
          h.rotation i (h.smul (DihedralGroup.sr k) (base q)) = y := by
  classical
  constructor
  · intro hy
    rcases (h.mem_reflectionCopyUnion_iff base k y).mp hy with
      ⟨side, q, i, hi⟩
    fin_cases side
    · left
      exact ⟨q, i, by simpa [reflectionCopyBase] using hi⟩
    · right
      exact ⟨q, i, by simpa [reflectionCopyBase] using hi⟩
  · rintro (horig | href)
    · rcases horig with ⟨q, i, hi⟩
      exact (h.mem_reflectionCopyUnion_iff base k y).mpr
        ⟨0, q, i, by simpa [reflectionCopyBase] using hi⟩
    · rcases href with ⟨q, i, hi⟩
      exact (h.mem_reflectionCopyUnion_iff base k y).mpr
        ⟨1, q, i, by simpa [reflectionCopyBase] using hi⟩

/-- Membership in the canonical reflection-copy residual is exactly avoiding
both the original selected orbit family and its reflected copy. -/
theorem mem_reflectionCopyResidual_iff
    (base : Fin 56 → V) (k : ZMod 19) (y : V) :
    y ∈ reflectionCopyResidual h base k ↔
      ¬ ((∃ q : Fin 56, ∃ i : ZMod 19, h.rotation i (base q) = y) ∨
        ∃ q : Fin 56, ∃ i : ZMod 19,
          h.rotation i (h.smul (DihedralGroup.sr k) (base q)) = y) := by
  classical
  rw [reflectionCopyResidual, Finset.mem_compl,
    h.mem_reflectionCopyUnion_iff_or base k y]

/-- A residual vertex is not in the original selected orbit family. -/
theorem not_mem_original_orbitFamily_of_mem_reflectionCopyResidual
    (base : Fin 56 → V) (k : ZMod 19) {y : V}
    (hy : y ∈ reflectionCopyResidual h base k) :
    ¬ ∃ q : Fin 56, ∃ i : ZMod 19, h.rotation i (base q) = y := by
  intro horig
  exact (h.mem_reflectionCopyResidual_iff base k y).mp hy (Or.inl horig)

/-- A residual vertex is not in the reflected selected orbit family. -/
theorem not_mem_reflected_orbitFamily_of_mem_reflectionCopyResidual
    (base : Fin 56 → V) (k : ZMod 19) {y : V}
    (hy : y ∈ reflectionCopyResidual h base k) :
    ¬ ∃ q : Fin 56, ∃ i : ZMod 19,
      h.rotation i (h.smul (DihedralGroup.sr k) (base q)) = y := by
  intro href
  exact (h.mem_reflectionCopyResidual_iff base k y).mp hy (Or.inr href)

end D19ActsOnMoore57

end Moore57

/-!
# Reflection-copy residual as original/reflected orbit-family avoidance

This file repackages the membership criterion for `reflectionCopyResidual`
using the existing `orbitFamilyUnion` abstraction for both the original selected
orbit family and its reflected copy.
-/

namespace Moore57

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

namespace D19ActsOnMoore57

variable (h : D19ActsOnMoore57 V Γ)

/-- The reflected copy of a selected rotation-orbit family. -/
noncomputable def reflectionOrbitFamilyUnion
    (base : Fin 56 → V) (k : ZMod 19) : Finset V :=
  h.orbitFamilyUnion fun q : Fin 56 =>
    h.smul (DihedralGroup.sr k) (base q)

/-- Membership in the reflected orbit-family union. -/
theorem mem_reflectionOrbitFamilyUnion_iff
    (base : Fin 56 → V) (k : ZMod 19) (y : V) :
    y ∈ h.reflectionOrbitFamilyUnion base k ↔
      ∃ q : Fin 56, ∃ i : ZMod 19,
        h.rotation i (h.smul (DihedralGroup.sr k) (base q)) = y := by
  simpa [reflectionOrbitFamilyUnion] using
    h.mem_orbitFamilyUnion
      (fun q : Fin 56 => h.smul (DihedralGroup.sr k) (base q)) y

/-- The reflection-copy union is the union of the original selected orbit
family and its reflected orbit family. -/
theorem mem_reflectionCopyUnion_iff_orbitFamilyUnion_or_reflectionOrbitFamilyUnion
    (base : Fin 56 → V) (k : ZMod 19) (y : V) :
    y ∈ reflectionCopyUnion h base k ↔
      y ∈ h.orbitFamilyUnion base ∨
        y ∈ h.reflectionOrbitFamilyUnion base k := by
  rw [h.mem_reflectionCopyUnion_iff_or base k y,
    h.mem_orbitFamilyUnion base y,
    h.mem_reflectionOrbitFamilyUnion_iff base k y]

/-- The reflection-copy residual is exactly the complement of both the original
selected orbit family and its reflected orbit family. -/
theorem mem_reflectionCopyResidual_iff_not_orbitFamilyUnion_and_not_reflectionOrbitFamilyUnion
    (base : Fin 56 → V) (k : ZMod 19) (y : V) :
    y ∈ reflectionCopyResidual h base k ↔
      y ∉ h.orbitFamilyUnion base ∧
        y ∉ h.reflectionOrbitFamilyUnion base k := by
  rw [reflectionCopyResidual, Finset.mem_compl,
    h.mem_reflectionCopyUnion_iff_orbitFamilyUnion_or_reflectionOrbitFamilyUnion
      base k y]
  exact not_or

end D19ActsOnMoore57

namespace OrbitBaseSelectionInput

variable {h : D19ActsOnMoore57 V Γ}

/-- The reflected copy of the selected orbit-family union attached to an input. -/
noncomputable def reflectionOrbitFamilyUnion
    (input : OrbitBaseSelectionInput h) (k : ZMod 19) : Finset V :=
  h.reflectionOrbitFamilyUnion input.base k

/-- Membership in the reflected orbit-family union attached to an input. -/
theorem mem_reflectionOrbitFamilyUnion_iff
    (input : OrbitBaseSelectionInput h) (k : ZMod 19) (y : V) :
    y ∈ input.reflectionOrbitFamilyUnion k ↔
      ∃ q : Fin 56, ∃ i : ZMod 19,
        h.rotation i (h.smul (DihedralGroup.sr k) (input.base q)) = y := by
  simpa [reflectionOrbitFamilyUnion] using
    h.mem_reflectionOrbitFamilyUnion_iff input.base k y

/-- Input-specialized form: the reflection-copy union is the union of the
selected orbit-family union and its reflected orbit-family union. -/
theorem mem_reflectionCopyUnion_iff_orbitFamilyUnion_or_reflectionOrbitFamilyUnion
    (input : OrbitBaseSelectionInput h) (k : ZMod 19) (y : V) :
    y ∈ reflectionCopyUnion h input.base k ↔
      y ∈ input.orbitFamilyUnion ∨
        y ∈ input.reflectionOrbitFamilyUnion k := by
  simpa [OrbitBaseSelectionInput.orbitFamilyUnion,
    OrbitBaseSelectionInput.reflectionOrbitFamilyUnion] using
    h.mem_reflectionCopyUnion_iff_orbitFamilyUnion_or_reflectionOrbitFamilyUnion
      input.base k y

/-- Input-specialized form: the reflection-copy residual is exactly the
complement of both the selected orbit-family union and its reflected copy. -/
theorem mem_reflectionCopyResidual_iff_not_orbitFamilyUnion_and_not_reflectionOrbitFamilyUnion
    (input : OrbitBaseSelectionInput h) (k : ZMod 19) (y : V) :
    y ∈ reflectionCopyResidual h input.base k ↔
      y ∉ input.orbitFamilyUnion ∧
        y ∉ input.reflectionOrbitFamilyUnion k := by
  simpa [OrbitBaseSelectionInput.orbitFamilyUnion,
    OrbitBaseSelectionInput.reflectionOrbitFamilyUnion] using
    h.mem_reflectionCopyResidual_iff_not_orbitFamilyUnion_and_not_reflectionOrbitFamilyUnion
      input.base k y

end OrbitBaseSelectionInput

end Moore57

/-!
# Reflection-copy criteria with split constant residual

This file refines the constant-residual reflection-copy witness by allowing the
residual finset to be supplied as a disjoint union of two pieces, such as the
fixed-vertex side and an `A`-side contribution.
-/

namespace Moore57

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- A constant-residual reflection-copy criterion whose residual is split into
two disjoint finsets.

The final residual contribution is proved from the two filtered contributions
using `Finset.card_union_of_disjoint`. -/
structure AdjacentMovedReflectionResidualSplit38Witness
    (h : D19ActsOnMoore57 V Γ) (base : Fin 56 → V) where
  k : ZMod 19
  fixedPart : Finset V
  aPart : Finset V
  parts_disjoint : Disjoint fixedPart aPart
  pairwise_disjoint :
    ((Finset.univ : Finset (Fin 2 × Fin 56)) :
      Set (Fin 2 × Fin 56)).PairwiseDisjoint
        (fun i => h.rotationOrbitFinset (reflectionCopyBase h base k i))
  fixedPart_disjoint :
    ∀ i : Fin 2 × Fin 56,
      Disjoint
        (h.rotationOrbitFinset (reflectionCopyBase h base k i))
        fixedPart
  aPart_disjoint :
    ∀ i : Fin 2 × Fin 56,
      Disjoint
        (h.rotationOrbitFinset (reflectionCopyBase h base k i))
        aPart
  cover :
    (Finset.univ : Finset (Fin 2 × Fin 56)).biUnion
          (fun i => h.rotationOrbitFinset (reflectionCopyBase h base k i)) ∪
        (fixedPart ∪ aPart) =
      (Finset.univ : Finset V)
  residual_contribution :
    ∀ d : ZMod 19, ∀ _hd : d ≠ 0,
      (fixedPart.filter fun y => Γ.Adj y (h.rotation d y)).card +
          (aPart.filter fun y => Γ.Adj y (h.rotation d y)).card =
        38

namespace AdjacentMovedReflectionResidualSplit38Witness

variable {h : D19ActsOnMoore57 V Γ}
variable {base : Fin 56 → V}

/-- The residual finset obtained by joining the two residual pieces. -/
def residual (w : AdjacentMovedReflectionResidualSplit38Witness h base) :
    Finset V :=
  w.fixedPart ∪ w.aPart

/-- The two split residual pieces are disjoint after filtering by any
predicate. -/
theorem filter_parts_disjoint
    (w : AdjacentMovedReflectionResidualSplit38Witness h base)
    (p : V → Prop) [DecidablePred p] :
    Disjoint (w.fixedPart.filter p) (w.aPart.filter p) :=
  Disjoint.mono (Finset.filter_subset p w.fixedPart)
    (Finset.filter_subset p w.aPart) w.parts_disjoint

/-- The filtered cardinality of the joined residual is the sum of the filtered
cardinalities of the two residual pieces. -/
theorem residual_filter_card
    (w : AdjacentMovedReflectionResidualSplit38Witness h base)
    (p : V → Prop) [DecidablePred p] :
    ((w.residual).filter p).card =
      (w.fixedPart.filter p).card + (w.aPart.filter p).card := by
  classical
  rw [residual, Finset.filter_union]
  exact Finset.card_union_of_disjoint (w.filter_parts_disjoint p)

/-- Forget the split-residual presentation to the constant-residual
reflection-copy criterion. -/
noncomputable def toConstantResidual38Witness
    (w : AdjacentMovedReflectionResidualSplit38Witness h base) :
    AdjacentMovedReflectionConstantResidual38Witness h base where
  k := w.k
  residual := w.residual
  pairwise_disjoint := w.pairwise_disjoint
  residual_disjoint := by
    intro i
    rw [residual, Finset.disjoint_left]
    intro x hx hxresidual
    rcases Finset.mem_union.mp hxresidual with hxfixed | hxa
    · exact (Finset.disjoint_left.mp (w.fixedPart_disjoint i)) hx hxfixed
    · exact (Finset.disjoint_left.mp (w.aPart_disjoint i)) hx hxa
  cover := by
    simpa [residual] using w.cover
  residual_contribution := by
    intro d hd
    rw [w.residual_filter_card (fun y => Γ.Adj y (h.rotation d y))]
    exact w.residual_contribution d hd

/-- Forget the split-residual presentation to the reflection-copy criterion. -/
noncomputable def toReflectionCopyPartition38Witness
    (w : AdjacentMovedReflectionResidualSplit38Witness h base) :
    AdjacentMovedReflectionCopyPartition38Witness h base :=
  w.toConstantResidual38Witness.toReflectionCopyPartition38Witness

/-- Forget the split-residual presentation to the two-copy witness. -/
noncomputable def toTwoCopyPartition38Witness
    (w : AdjacentMovedReflectionResidualSplit38Witness h base) :
    AdjacentMovedTwoCopyPartition38Witness h base :=
  w.toConstantResidual38Witness.toTwoCopyPartition38Witness

/-- The split-residual witness gives the adjacent-moved decomposition with
residual contribution constantly `38`. -/
noncomputable def toDecomposition
    (w : AdjacentMovedReflectionResidualSplit38Witness h base) :
    D19AdjacentMovedDecomposition h base fixedOrAContribution38 :=
  w.toConstantResidual38Witness.toDecomposition

end AdjacentMovedReflectionResidualSplit38Witness

namespace AdjacentMovedReflectionConstantResidual38Witness

variable {h : D19ActsOnMoore57 V Γ}
variable {base : Fin 56 → V}

/-- Constructor wrapper for the split-residual reflection-copy criterion. -/
noncomputable def of_residualSplit
    (w : AdjacentMovedReflectionResidualSplit38Witness h base) :
    AdjacentMovedReflectionConstantResidual38Witness h base :=
  w.toConstantResidual38Witness

end AdjacentMovedReflectionConstantResidual38Witness

end Moore57

