import Moore57.AFiberUnionFilterCardinality
import Moore57.Moore57Graph.AFiber.MatchingPermSymmetry
import Moore57.AFiberCoordinateRotation
import Moore57.AFiberCardinalityBoundary

/-!
# A-fiber rotation filters as coordinate fixed-point counts

This file bridges the per-fiber adjacent-rotation filter on an A-fiber to a
fixed-point count for the coordinate permutation obtained by first matching
across the two fibers and then transporting back along the rotation.
-/

namespace Moore57

open Finset

universe u uP

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

theorem fixedVertexCount_eq_fintype_card_fixedSubtype
    {P : Type*} [DecidableEq P] [Fintype P] (σ : Equiv.Perm P) :
    fixedVertexCount σ = Fintype.card {p : P // σ p = p} := by
  classical
  rw [fixedVertexCount]
  symm
  calc
    Fintype.card {p : P // σ p = p} =
        Fintype.card
          {p : P // p ∈ ((Finset.univ : Finset P).filter fun p => σ p = p)} := by
      exact Fintype.card_congr
        (Equiv.subtypeEquivRight fun p => by simp)
    _ = ((Finset.univ : Finset P).filter fun p => σ p = p).card := by
      rw [Fintype.card_coe]

namespace AFiberCoordinates

theorem coord_adjacent_rotation_iff_matching_rotation_fixed_to
    (h : D19ActsOnMoore57 V Γ) (coords : AFiberCoordinates.{u, uP} Γ)
    (d i j : ZMod 19) (hij : i ≠ j)
    (hu : h.rotation d coords.u = coords.u)
    (haij : h.rotation d (coords.a i) = coords.a j)
    (p : coords.P) :
    Γ.Adj
        (((coords.coord i p :
          {x : V // x ∈ branchFiber Γ coords.u (coords.a i)}) : V))
        (h.rotation d
          (((coords.coord i p :
            {x : V // x ∈ branchFiber Γ coords.u (coords.a i)}) : V))) ↔
      (((matchingEquiv h.isMoore coords i j hij).trans
          (rotationCoordEquivTo h coords d i j hu haij).symm) p = p) := by
  let ρ : Equiv.Perm coords.P := rotationCoordEquivTo h coords d i j hu haij
  have hrot :
      ((coords.coord j (ρ p) :
        {x : V // x ∈ branchFiber Γ coords.u (coords.a j)}) : V) =
        h.rotation d
          (((coords.coord i p :
            {x : V // x ∈ branchFiber Γ coords.u (coords.a i)}) : V)) := by
    dsimp [ρ]
    simp
  calc
    Γ.Adj
        (((coords.coord i p :
          {x : V // x ∈ branchFiber Γ coords.u (coords.a i)}) : V))
        (h.rotation d
          (((coords.coord i p :
            {x : V // x ∈ branchFiber Γ coords.u (coords.a i)}) : V))) ↔
      Γ.Adj
        (((coords.coord i p :
          {x : V // x ∈ branchFiber Γ coords.u (coords.a i)}) : V))
        (((coords.coord j (ρ p) :
          {x : V // x ∈ branchFiber Γ coords.u (coords.a j)}) : V)) := by
        rw [hrot]
    _ ↔ matchingEquiv h.isMoore coords i j hij p = ρ p := by
        exact adj_iff_matchingEquiv_eq h.isMoore coords hij p (ρ p)
    _ ↔ (((matchingEquiv h.isMoore coords i j hij).trans
          (rotationCoordEquivTo h coords d i j hu haij).symm) p = p) := by
        simpa [ρ] using
          (matchingEquiv_eq_perm_apply_iff_trans_symm_fixed
            h.isMoore coords hij ρ p)

end AFiberCoordinates

theorem fiber_filter_adjacent_rotation_card_eq_fixedVertexCount_to
    (h : D19ActsOnMoore57 V Γ) (coords : AFiberCoordinates.{u, uP} Γ)
    (d i j : ZMod 19) (hij : i ≠ j)
    (hu : h.rotation d coords.u = coords.u)
    (haij : h.rotation d (coords.a i) = coords.a j) :
    ((coords.fiber i).filter fun y => Γ.Adj y (h.rotation d y)).card =
      @fixedVertexCount coords.P (Classical.decEq coords.P) coords.P_fintype
        ((AFiberCoordinates.matchingEquiv h.isMoore coords i j hij).trans
          (AFiberCoordinates.rotationCoordEquivTo h coords d i j hu haij).symm) := by
  classical
  letI := coords.P_fintype
  let σ : Equiv.Perm coords.P :=
    (AFiberCoordinates.matchingEquiv h.isMoore coords i j hij).trans
      (AFiberCoordinates.rotationCoordEquivTo h coords d i j hu haij).symm
  let e :
      {y : V // y ∈ coords.fiber i ∧ Γ.Adj y (h.rotation d y)} ≃
        {p : coords.P // σ p = p} := {
    toFun y := by
      let p : coords.P :=
        (coords.coord i).symm ⟨y.1, y.2.1⟩
      refine ⟨p, ?_⟩
      have hcoord :
          (((coords.coord i p :
            {x : V // x ∈ branchFiber Γ coords.u (coords.a i)}) : V)) = y.1 := by
        dsimp [p]
        simp
      have hadj :
          Γ.Adj
            (((coords.coord i p :
              {x : V // x ∈ branchFiber Γ coords.u (coords.a i)}) : V))
            (h.rotation d
              (((coords.coord i p :
                {x : V // x ∈ branchFiber Γ coords.u (coords.a i)}) : V))) := by
        simpa [hcoord] using y.2.2
      have hfixed :=
        (AFiberCoordinates.coord_adjacent_rotation_iff_matching_rotation_fixed_to
          h coords d i j hij hu haij p).1 hadj
      simpa [σ] using hfixed
    invFun p := by
      refine
        ⟨((coords.coord i p.1 :
            {x : V // x ∈ branchFiber Γ coords.u (coords.a i)}) : V), ?_⟩
      refine ⟨coords.coord_mem i p.1, ?_⟩
      have hfixed :
          (((AFiberCoordinates.matchingEquiv h.isMoore coords i j hij).trans
              (AFiberCoordinates.rotationCoordEquivTo h coords d i j hu haij).symm)
              p.1 = p.1) := by
        simpa [σ] using p.2
      exact
        (AFiberCoordinates.coord_adjacent_rotation_iff_matching_rotation_fixed_to
          h coords d i j hij hu haij p.1).2 hfixed
    left_inv y := by
      ext
      simp
    right_inv p := by
      ext
      simp
  }
  calc
    ((coords.fiber i).filter fun y => Γ.Adj y (h.rotation d y)).card =
        Fintype.card {y : V // y ∈ coords.fiber i ∧ Γ.Adj y (h.rotation d y)} := by
      rw [Fintype.card_subtype]
      apply congrArg Finset.card
      ext y
      simp
    _ = Fintype.card {p : coords.P // σ p = p} :=
      Fintype.card_congr e
    _ =
        @fixedVertexCount coords.P (Classical.decEq coords.P) coords.P_fintype σ := by
      simpa [σ] using
        (fixedVertexCount_eq_fintype_card_fixedSubtype (σ := σ)).symm

theorem fiber_filter_adjacent_rotation_card_eq_fixedVertexCount_add
    (h : D19ActsOnMoore57 V Γ) (coords : AFiberCoordinates.{u, uP} Γ)
    (d i : ZMod 19) (hd : d ≠ 0)
    (hu : h.rotation d coords.u = coords.u)
    (hai : h.rotation d (coords.a i) = coords.a (i + d)) :
    ((coords.fiber i).filter fun y => Γ.Adj y (h.rotation d y)).card =
      @fixedVertexCount coords.P (Classical.decEq coords.P) coords.P_fintype
        ((AFiberCoordinates.matchingEquiv h.isMoore coords i (i + d)
            (index_ne_add_of_ne_zero hd)).trans
          (AFiberCoordinates.rotationCoordEquivTo h coords d i (i + d) hu hai).symm) :=
  fiber_filter_adjacent_rotation_card_eq_fixedVertexCount_to
    h coords d i (i + d) (index_ne_add_of_ne_zero hd) hu hai

theorem fiber_filter_adjacent_rotation_card_eq_fixedVertexCount_of_equivariance
    {h : D19ActsOnMoore57 V Γ} {coords : AFiberCoordinates.{u, uP} Γ}
    (rot : AFiberRotationEquivariance h coords)
    (d i : ZMod 19) (hd : d ≠ 0) :
    ((coords.fiber i).filter fun y => Γ.Adj y (h.rotation d y)).card =
      @fixedVertexCount coords.P (Classical.decEq coords.P) coords.P_fintype
        ((AFiberCoordinates.matchingEquiv h.isMoore coords i (i + d)
            (index_ne_add_of_ne_zero hd)).trans
          (rot.coordPerm d i).symm) := by
  simpa [AFiberRotationEquivariance.coordPerm] using
    fiber_filter_adjacent_rotation_card_eq_fixedVertexCount_add
      h coords d i hd (rot.rotation_u d) (rot.rotation_a d i)

theorem fixedAFiberAFiberCard_fiberUnion_eq_sum_fixedVertexCount
    {h : D19ActsOnMoore57 V Γ} {coords : AFiberCoordinates.{u, uP} Γ}
    (rot : AFiberRotationEquivariance h coords)
    (indices : Finset (ZMod 19)) (d : ZMod 19) (hd : d ≠ 0) :
    fixedAFiberAFiberCard h (coords.fiberUnion indices) d =
      ∑ i ∈ indices,
        @fixedVertexCount coords.P (Classical.decEq coords.P) coords.P_fintype
          ((AFiberCoordinates.matchingEquiv h.isMoore coords i (i + d)
              (index_ne_add_of_ne_zero hd)).trans
            (rot.coordPerm d i).symm) := by
  rw [fixedAFiberAFiberCard_fiberUnion_eq_sum]
  refine Finset.sum_congr rfl ?_
  intro i _hi
  exact fiber_filter_adjacent_rotation_card_eq_fixedVertexCount_of_equivariance
    rot d i hd

namespace AFiberCardinality38Boundary

variable {h : D19ActsOnMoore57 V Γ}
variable {coords : AFiberCoordinates.{u, uP} Γ}
variable {indices : Finset (ZMod 19)}

noncomputable def of_matchingFixedCountSum_add
    (hu : ∀ d : ZMod 19, d ≠ 0 → h.rotation d coords.u = coords.u)
    (ha :
      ∀ d : ZMod 19, d ≠ 0 → ∀ i : ZMod 19,
        h.rotation d (coords.a i) = coords.a (i + d))
    (hsum :
      ∀ d : ZMod 19, ∀ hd : d ≠ 0,
        ∑ i ∈ indices,
          @fixedVertexCount coords.P (Classical.decEq coords.P) coords.P_fintype
            ((AFiberCoordinates.matchingEquiv h.isMoore coords i (i + d)
                (index_ne_add_of_ne_zero hd)).trans
              (AFiberCoordinates.rotationCoordEquivTo h coords d i (i + d)
                (hu d hd) (ha d hd i)).symm) = 38) :
    AFiberCardinality38Boundary h coords indices :=
  of_card_eq_thirtyEight (by
    intro d hd
    rw [fixedAFiberAFiberCard_fiberUnion_eq_sum]
    trans
      ∑ i ∈ indices,
        @fixedVertexCount coords.P (Classical.decEq coords.P) coords.P_fintype
          ((AFiberCoordinates.matchingEquiv h.isMoore coords i (i + d)
              (index_ne_add_of_ne_zero hd)).trans
            (AFiberCoordinates.rotationCoordEquivTo h coords d i (i + d)
              (hu d hd) (ha d hd i)).symm)
    · refine Finset.sum_congr rfl ?_
      intro i hi
      exact fiber_filter_adjacent_rotation_card_eq_fixedVertexCount_add
        h coords d i hd (hu d hd) (ha d hd i)
    · exact hsum d hd)

noncomputable def of_matchingFixedCountSum
    (rot : AFiberRotationEquivariance h coords)
    (hsum :
      ∀ d : ZMod 19, ∀ hd : d ≠ 0,
        ∑ i ∈ indices,
          @fixedVertexCount coords.P (Classical.decEq coords.P) coords.P_fintype
            ((AFiberCoordinates.matchingEquiv h.isMoore coords i (i + d)
                (index_ne_add_of_ne_zero hd)).trans
              (rot.coordPerm d i).symm) = 38) :
    AFiberCardinality38Boundary h coords indices :=
  of_card_eq_thirtyEight (by
    intro d hd
    rw [fixedAFiberAFiberCard_fiberUnion_eq_sum_fixedVertexCount rot indices d hd]
    exact hsum d hd)

end AFiberCardinality38Boundary

end Moore57
