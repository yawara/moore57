import Moore57.D19OnMoore57.AFiber.ReflectionTransport

/-!
# A-fiber coordinate reflection equivariance

This file packages the minimal hypotheses saying that the chosen A-fiber
coordinates are equivariant with respect to one reflection: the center is fixed
and the branch indexed by `i` is sent to the branch indexed by `sigma i`.

The package deliberately stores only these geometric facts.  Coordinate
permutations are derived from `AFiberCoordinates.reflectionCoordEquivTo`.
-/

namespace Moore57

universe u uP

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- The minimal reflection equivariance hypotheses for an A-fiber coordinate
system, for a fixed reflection parameter `k` and branch-index map `sigma`.  No
coordinate permutations are stored: they are derived on demand from the
reflection transport API. -/
structure AFiberReflectionEquivariance
    (h : D19ActsOnMoore57 V Γ) (coords : AFiberCoordinates.{u, uP} Γ)
    (k : ZMod 19) (sigma : ZMod 19 → ZMod 19) : Prop where
  /-- The chosen reflection fixes the A-fiber center. -/
  reflection_u : h.smul (DihedralGroup.sr k) coords.u = coords.u
  /-- The chosen reflection sends the branch at `i` to the branch at
  `sigma i`. -/
  reflection_a :
    ∀ i : ZMod 19, h.smul (DihedralGroup.sr k) (coords.a i) = coords.a (sigma i)

namespace AFiberReflectionEquivariance

variable {h : D19ActsOnMoore57 V Γ}
variable {coords : AFiberCoordinates.{u, uP} Γ}
variable {k : ZMod 19} {sigma : ZMod 19 → ZMod 19}

/-- The coordinate permutation induced by the chosen reflection, using the
chart at `i` as source and the chart at `sigma i` as target. -/
noncomputable def coordPerm
    (ref : AFiberReflectionEquivariance h coords k sigma)
    (i : ZMod 19) : Equiv.Perm coords.P :=
  AFiberCoordinates.reflectionCoordEquivTo h coords k i (sigma i)
    ref.reflection_u (ref.reflection_a i)

@[simp] theorem coordPerm_apply
    (ref : AFiberReflectionEquivariance h coords k sigma)
    (i : ZMod 19) (p : coords.P) :
    ref.coordPerm i p =
      (coords.coord (sigma i)).symm
        (AFiberCoordinates.reflectionFiberEquivTo h coords k i (sigma i)
          ref.reflection_u (ref.reflection_a i) (coords.coord i p)) :=
  rfl

/-- Applying the derived coordinate permutation and then reading the target
chart gives the underlying reflected vertex. -/
@[simp] theorem coord_coordPerm_apply_val
    (ref : AFiberReflectionEquivariance h coords k sigma)
    (i : ZMod 19) (p : coords.P) :
    ((coords.coord (sigma i) (ref.coordPerm i p) :
      {x : V // x ∈ branchFiber Γ coords.u (coords.a (sigma i))}) : V) =
        h.smul (DihedralGroup.sr k)
          (((coords.coord i p :
            {x : V // x ∈ branchFiber Γ coords.u (coords.a i)}) : V)) := by
  simp [coordPerm]

/-- Coordinate equality after the derived reflection permutation is equivalent
to equality of the underlying reflected source representative with the target
representative. -/
theorem coordPerm_eq_iff
    (ref : AFiberReflectionEquivariance h coords k sigma)
    (i : ZMod 19) (p q : coords.P) :
    ref.coordPerm i p = q ↔
      h.smul (DihedralGroup.sr k)
          (((coords.coord i p :
            {x : V // x ∈ branchFiber Γ coords.u (coords.a i)}) : V)) =
        (((coords.coord (sigma i) q :
          {x : V // x ∈ branchFiber Γ coords.u (coords.a (sigma i))}) : V)) := by
  simpa [coordPerm] using
    AFiberCoordinates.reflectionCoordEquivTo_eq_iff h coords k i (sigma i)
      ref.reflection_u (ref.reflection_a i) p q

/-- Reflection transports membership from the `i`-th A-fiber to the
`sigma i`-th A-fiber, and reflects it back. -/
theorem reflection_mem_fiber_iff
    (ref : AFiberReflectionEquivariance h coords k sigma)
    (i : ZMod 19) (x : V) :
    h.smul (DihedralGroup.sr k) x ∈ coords.fiber (sigma i) ↔
      x ∈ coords.fiber i :=
  AFiberCoordinates.reflection_mem_fiber_iff h coords k i (sigma i)
    ref.reflection_u (ref.reflection_a i) x

/-- Forward membership transport for the reflection-induced A-fiber shift. -/
theorem reflection_mem_fiber_of_mem
    (ref : AFiberReflectionEquivariance h coords k sigma)
    (i : ZMod 19) {x : V} (hx : x ∈ coords.fiber i) :
    h.smul (DihedralGroup.sr k) x ∈ coords.fiber (sigma i) :=
  (ref.reflection_mem_fiber_iff i x).2 hx

/-- Backward membership transport for the reflection-induced A-fiber shift. -/
theorem mem_fiber_of_reflection_mem_fiber
    (ref : AFiberReflectionEquivariance h coords k sigma)
    (i : ZMod 19) {x : V}
    (hx : h.smul (DihedralGroup.sr k) x ∈ coords.fiber (sigma i)) :
    x ∈ coords.fiber i :=
  (ref.reflection_mem_fiber_iff i x).1 hx

/-- A coordinate representative, after reflection, lies in the target
A-fiber. -/
theorem reflection_coord_mem_fiber
    (ref : AFiberReflectionEquivariance h coords k sigma)
    (i : ZMod 19) (p : coords.P) :
    h.smul (DihedralGroup.sr k)
        (((coords.coord i p :
          {x : V // x ∈ branchFiber Γ coords.u (coords.a i)}) : V)) ∈
      coords.fiber (sigma i) :=
  ref.reflection_mem_fiber_of_mem i (coords.coord_mem i p)

/-- The support of the coordinate permutation induced at branch `i`. -/
noncomputable def supportAt
    [DecidableEq coords.P] [Fintype coords.P]
    (ref : AFiberReflectionEquivariance h coords k sigma)
    (i : ZMod 19) : Finset coords.P :=
  (ref.coordPerm i).support

end AFiberReflectionEquivariance

end Moore57
