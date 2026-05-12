import Moore57.D19OnMoore57.Reflection.RegularTenTraceArithmetic

/-!
# Strong-graph boundary for the regular-10 reflection branch

This file packages the graph-theoretic consequences of the
`ReflectionRegularTenAllCenterNeighborOrbitsPreserved` boundary.  The proofs
only specialize the fixed-induced graph API and the already-proved regular-ten
degree theorem.
-/

namespace Moore57

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

namespace ReflectionRegularTenAllCenterNeighborOrbitsPreserved

variable {h : D19ActsOnMoore57 V Γ} {k : ZMod 19}

/-- The fixed-induced graph in the regular-`10` branch is strongly regular
with parameters `(10, 3, 0, 1)`. -/
theorem fixedInducedGraph_isSRGWith_10_3_0_1
    (hreg : ReflectionRegularTenAllCenterNeighborOrbitsPreserved h k) :
    (h.fixedInducedGraph (DihedralGroup.sr k)).IsSRGWith 10 3 0 1 := by
  have hsrg :=
    h.fixedInducedGraph_isSRGWith_of_regular
      (DihedralGroup.sr k) 3 hreg.fixedInducedGraph_regular_degree_three
  simpa [hreg.fixedVertexCount_eq_ten] using hsrg

/-- The fixed-induced graph inherits the strong `(λ, μ) = (0, 1)` condition. -/
theorem fixedInducedGraph_isStrongZeroOne
    (_hreg : ReflectionRegularTenAllCenterNeighborOrbitsPreserved h k) :
    IsStrongZeroOne (h.fixedInducedGraph (DihedralGroup.sr k)) :=
  h.fixedInducedGraph_isStrongZeroOne (DihedralGroup.sr k)

/-- Adjacent vertices in the fixed-induced graph have no common neighbor. -/
theorem fixedInducedGraph_not_commonNeighbor_of_adj
    (hreg : ReflectionRegularTenAllCenterNeighborOrbitsPreserved h k)
    {x y z : fixedVertexSet (h.smulEquiv (DihedralGroup.sr k))}
    (hxy : (h.fixedInducedGraph (DihedralGroup.sr k)).Adj x y) :
    ¬ ((h.fixedInducedGraph (DihedralGroup.sr k)).Adj x z ∧
        (h.fixedInducedGraph (DihedralGroup.sr k)).Adj y z) :=
  hreg.fixedInducedGraph_isStrongZeroOne.not_commonNeighbor_of_adj hxy

/-- Triangle-free form for the fixed-induced graph. -/
theorem fixedInducedGraph_triangleFree
    (hreg : ReflectionRegularTenAllCenterNeighborOrbitsPreserved h k)
    {a b c : fixedVertexSet (h.smulEquiv (DihedralGroup.sr k))}
    (hab : (h.fixedInducedGraph (DihedralGroup.sr k)).Adj a b)
    (hac : (h.fixedInducedGraph (DihedralGroup.sr k)).Adj a c) :
    ¬ (h.fixedInducedGraph (DihedralGroup.sr k)).Adj b c :=
  hreg.fixedInducedGraph_isStrongZeroOne.not_adj_of_adj_of_adj hab hac

/-- Distinct non-adjacent vertices in the fixed-induced graph have a unique
common neighbor. -/
theorem fixedInducedGraph_existsUnique_commonNeighbor_of_not_adj
    (hreg : ReflectionRegularTenAllCenterNeighborOrbitsPreserved h k)
    {x y : fixedVertexSet (h.smulEquiv (DihedralGroup.sr k))}
    (hxy_ne : x ≠ y)
    (hxy_not : ¬ (h.fixedInducedGraph (DihedralGroup.sr k)).Adj x y) :
    ∃! z : fixedVertexSet (h.smulEquiv (DihedralGroup.sr k)),
      (h.fixedInducedGraph (DihedralGroup.sr k)).Adj x z ∧
        (h.fixedInducedGraph (DihedralGroup.sr k)).Adj y z :=
  hreg.fixedInducedGraph_isStrongZeroOne.existsUnique_commonNeighbor_of_not_adj
    hxy_ne hxy_not

end ReflectionRegularTenAllCenterNeighborOrbitsPreserved

namespace D19ActsOnMoore57

variable {h : D19ActsOnMoore57 V Γ}

/-- D19 namespace wrapper for the regular-`10` strongly-regular fixed graph. -/
theorem reflectionRegularTen_fixedInducedGraph_isSRGWith_10_3_0_1
    (k : ZMod 19)
    (hreg : ReflectionRegularTenAllCenterNeighborOrbitsPreserved h k) :
    (h.fixedInducedGraph (DihedralGroup.sr k)).IsSRGWith 10 3 0 1 :=
  hreg.fixedInducedGraph_isSRGWith_10_3_0_1

/-- D19 namespace wrapper for the strong `(λ, μ) = (0, 1)` fixed graph. -/
theorem reflectionRegularTen_fixedInducedGraph_isStrongZeroOne
    (k : ZMod 19)
    (hreg : ReflectionRegularTenAllCenterNeighborOrbitsPreserved h k) :
    IsStrongZeroOne (h.fixedInducedGraph (DihedralGroup.sr k)) :=
  hreg.fixedInducedGraph_isStrongZeroOne

/-- D19 namespace wrapper: adjacent fixed vertices have no common neighbor. -/
theorem reflectionRegularTen_fixedInducedGraph_not_commonNeighbor_of_adj
    (k : ZMod 19)
    (hreg : ReflectionRegularTenAllCenterNeighborOrbitsPreserved h k)
    {x y z : fixedVertexSet (h.smulEquiv (DihedralGroup.sr k))}
    (hxy : (h.fixedInducedGraph (DihedralGroup.sr k)).Adj x y) :
    ¬ ((h.fixedInducedGraph (DihedralGroup.sr k)).Adj x z ∧
        (h.fixedInducedGraph (DihedralGroup.sr k)).Adj y z) :=
  hreg.fixedInducedGraph_not_commonNeighbor_of_adj hxy

/-- D19 namespace wrapper: triangle-free form for the fixed-induced graph. -/
theorem reflectionRegularTen_fixedInducedGraph_triangleFree
    (k : ZMod 19)
    (hreg : ReflectionRegularTenAllCenterNeighborOrbitsPreserved h k)
    {a b c : fixedVertexSet (h.smulEquiv (DihedralGroup.sr k))}
    (hab : (h.fixedInducedGraph (DihedralGroup.sr k)).Adj a b)
    (hac : (h.fixedInducedGraph (DihedralGroup.sr k)).Adj a c) :
    ¬ (h.fixedInducedGraph (DihedralGroup.sr k)).Adj b c :=
  hreg.fixedInducedGraph_triangleFree hab hac

/-- D19 namespace wrapper: distinct non-adjacent fixed vertices have a unique
common neighbor. -/
theorem reflectionRegularTen_fixedInducedGraph_existsUnique_commonNeighbor_of_not_adj
    (k : ZMod 19)
    (hreg : ReflectionRegularTenAllCenterNeighborOrbitsPreserved h k)
    {x y : fixedVertexSet (h.smulEquiv (DihedralGroup.sr k))}
    (hxy_ne : x ≠ y)
    (hxy_not : ¬ (h.fixedInducedGraph (DihedralGroup.sr k)).Adj x y) :
    ∃! z : fixedVertexSet (h.smulEquiv (DihedralGroup.sr k)),
      (h.fixedInducedGraph (DihedralGroup.sr k)).Adj x z ∧
        (h.fixedInducedGraph (DihedralGroup.sr k)).Adj y z :=
  hreg.fixedInducedGraph_existsUnique_commonNeighbor_of_not_adj hxy_ne hxy_not

end D19ActsOnMoore57

end

end Moore57
