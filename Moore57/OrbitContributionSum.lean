import Moore57.OrbitAdjacentMovedCount
import Moore57.FinsetIndicatorSums

namespace Moore57

namespace D19ActsOnMoore57

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- A single adjacent `d`-rotation edge on a rotation orbit is enough to put
`d` in the orbit's internal difference set. -/
theorem mem_internalDiffSet_rotationOrbit_of_adjacent_mem_rotationOrbitFinset
    (h : D19ActsOnMoore57 V Γ) {d : ZMod 19} {x y : V}
    (hy : y ∈ h.rotationOrbitFinset x) (hadj : Γ.Adj y (h.rotation d y)) :
    d ∈ internalDiffSet Γ (fun i : ZMod 19 => h.rotation i x) := by
  classical
  rcases (h.mem_rotationOrbitFinset x y).mp hy with ⟨i, rfl⟩
  have hd0 : d ≠ 0 := by
    intro hd
    have hloop : Γ.Adj (h.rotation i x) (h.rotation i x) := by
      rw [hd] at hadj
      rw [h.rotation_zero] at hadj
      exact hadj
    exact SimpleGraph.irrefl Γ hloop
  have hAdj' :
      Γ.Adj (h.smul (DihedralGroup.r (-i)) (h.rotation i x))
        (h.smul (DihedralGroup.r (-i)) (h.rotation d (h.rotation i x))) :=
    (h.smul_adj (DihedralGroup.r (-i)) (h.rotation i x)
      (h.rotation d (h.rotation i x))).mp hadj
  change
      Γ.Adj (h.rotation (-i) (h.rotation i x))
        (h.rotation (-i) (h.rotation d (h.rotation i x))) at hAdj'
  have hleft : h.rotation (-i) (h.rotation i x) = x := by
    calc
      h.rotation (-i) (h.rotation i x)
          = (h.rotation (-i) * h.rotation i) x := by
              simp [Equiv.Perm.mul_apply]
      _ = h.rotation ((-i) + i) x := by
              rw [← h.rotation_add]
      _ = x := by
              simp
  have hdi : h.rotation d (h.rotation i x) = h.rotation (d + i) x := by
    calc
      h.rotation d (h.rotation i x)
          = (h.rotation d * h.rotation i) x := by
              simp [Equiv.Perm.mul_apply]
      _ = h.rotation (d + i) x := by
              rw [← h.rotation_add]
  have hright :
      h.rotation (-i) (h.rotation d (h.rotation i x)) = h.rotation d x := by
    calc
      h.rotation (-i) (h.rotation d (h.rotation i x))
          = h.rotation (-i) (h.rotation (d + i) x) := by
              rw [hdi]
      _ = (h.rotation (-i) * h.rotation (d + i)) x := by
              simp [Equiv.Perm.mul_apply]
      _ = h.rotation ((-i) + (d + i)) x := by
              rw [← h.rotation_add]
      _ = h.rotation d x := by
              congr 1
              simp [add_assoc, add_comm]
  have hbase : Γ.Adj x (h.rotation d x) := by
    simpa [hleft, hright] using hAdj'
  exact h.mem_internalDiffSet_rotationOrbit_of_adj hd0 hbase

/-- The contribution of one full size-19 rotation orbit to the adjacent-moved
count is either all `19` vertices or none, according as `d` is an internal
difference of that orbit. -/
theorem rotationOrbitContribution_card_eq_ite
    (h : D19ActsOnMoore57 V Γ) (d : ZMod 19) (x : V)
    (hcard : (h.rotationOrbitFinset x).card = 19) :
    ((h.rotationOrbitFinset x).filter fun y => Γ.Adj y (h.rotation d y)).card =
      if d ∈ internalDiffSet Γ (fun i : ZMod 19 => h.rotation i x) then 19 else 0 := by
  classical
  by_cases hd : d ∈ internalDiffSet Γ (fun i : ZMod 19 => h.rotation i x)
  · have hfilter :
        (h.rotationOrbitFinset x).filter (fun y => Γ.Adj y (h.rotation d y)) =
          h.rotationOrbitFinset x := by
      ext y
      constructor
      · intro hy
        exact (Finset.mem_filter.mp hy).1
      · intro hy
        exact Finset.mem_filter.mpr
          ⟨hy, h.adjacent_rotation_moved_of_mem_rotationOrbitFinset hd hy⟩
    simp [hd, hfilter, hcard]
  · have hfilter :
        (h.rotationOrbitFinset x).filter (fun y => Γ.Adj y (h.rotation d y)) =
          ∅ := by
      ext y
      constructor
      · intro hy
        rcases Finset.mem_filter.mp hy with ⟨hyOrbit, hyAdj⟩
        exact False.elim
          (hd (h.mem_internalDiffSet_rotationOrbit_of_adjacent_mem_rotationOrbitFinset
            hyOrbit hyAdj))
      · intro hy
        cases hy
    simp [hd, hfilter]

/-- Family-level orbit contribution sum for base vertices whose rotation
orbits all have cardinality `19`. -/
theorem sum_rotationOrbitContribution_card_eq_nineteen_mul_card_filter
    (h : D19ActsOnMoore57 V Γ) {ι : Type*} [Fintype ι]
    (base : ι → V) (d : ZMod 19)
    (hcard : ∀ q : ι, (h.rotationOrbitFinset (base q)).card = 19) :
    (∑ q : ι,
      ((h.rotationOrbitFinset (base q)).filter fun y =>
        Γ.Adj y (h.rotation d y)).card) =
      19 *
        ((Finset.univ : Finset ι).filter
          (fun q => d ∈ internalDiffSet Γ
            (fun i : ZMod 19 => h.rotation i (base q)))).card := by
  classical
  calc
    (∑ q : ι,
      ((h.rotationOrbitFinset (base q)).filter fun y =>
        Γ.Adj y (h.rotation d y)).card)
        = ∑ q : ι,
            if d ∈ internalDiffSet Γ
                (fun i : ZMod 19 => h.rotation i (base q)) then
              19
            else
              0 := by
            apply Finset.sum_congr rfl
            intro q _hq
            exact h.rotationOrbitContribution_card_eq_ite d (base q) (hcard q)
    _ = 19 *
        ((Finset.univ : Finset ι).filter
          (fun q => d ∈ internalDiffSet Γ
            (fun i : ZMod 19 => h.rotation i (base q)))).card := by
            simpa using
              (Fintype.sum_ite_const_nat_eq_mul_card_filter
                (ι := ι)
                (p := fun q => d ∈ internalDiffSet Γ
                  (fun i : ZMod 19 => h.rotation i (base q)))
                19)

/-- A fallback family-level indicator version: if each summand is already known
to be `if p q then 19 else 0`, the total is the corresponding filtered count
times `19`. -/
theorem sum_eq_nineteen_mul_card_filter_of_eq_ite
    {ι : Type*} [Fintype ι] (a : ι → ℕ) (p : ι → Prop) [DecidablePred p]
    (ha : ∀ q : ι, a q = if p q then 19 else 0) :
    (∑ q : ι, a q) = 19 * ((Finset.univ : Finset ι).filter p).card := by
  classical
  calc
    (∑ q : ι, a q) = ∑ q : ι, if p q then 19 else 0 := by
      apply Finset.sum_congr rfl
      intro q _hq
      exact ha q
    _ = 19 * ((Finset.univ : Finset ι).filter p).card := by
      simpa using Fintype.sum_ite_const_nat_eq_mul_card_filter (ι := ι) p 19

end D19ActsOnMoore57

end Moore57
