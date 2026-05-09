import Moore57.AFiberCoordinateOrbit
import Moore57.AFiberMatchingFixedCountSupport

/-!
# A-fiber cardinality boundaries from rotation-orbit coordinates

This file composes the rotation-orbit coordinate constructor with the
support-complement fixed-count constructor for `AFiberCardinality38Boundary`.
-/

namespace Moore57

open Finset

noncomputable section

universe u uP

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

local instance instAFiberOrbitCardinalityBoundaryPFintype
    (coords : AFiberCoordinates.{u, uP} Γ) : Fintype coords.P :=
  coords.P_fintype

local instance instAFiberOrbitCardinalityBoundaryDecidableEq
    (α : Type*) : DecidableEq α :=
  Classical.decEq α

namespace AFiberCardinality38Boundary

/-- Build the A-fiber cardinality boundary for rotation-orbit coordinates from
support-complement sums of the matching-rotation coordinate permutations. -/
noncomputable def of_rotationOrbit_matchingSupportComplSum
    (h : D19ActsOnMoore57 V Γ) (u a0 : V)
    (hu : ∀ d : ZMod 19, h.rotation d u = u)
    (hub0 : Γ.Adj u a0)
    (hinj : Function.Injective fun i : ZMod 19 => h.rotation i a0)
    (indices : Finset (ZMod 19))
    (hsum :
      ∀ d : ZMod 19, ∀ hd : d ≠ 0,
        ∑ i ∈ indices,
          ((AFiberCoordinates.ofRotationOrbit_rotationEquivariance
              h u a0 hu hub0 hinj).matchingRotationPerm d i hd).supportᶜ.card =
            38) :
    AFiberCardinality38Boundary h
      (AFiberCoordinates.ofRotationOrbit h u a0 hu hub0 hinj) indices :=
  of_matchingSupportComplSum
    (AFiberCoordinates.ofRotationOrbit_rotationEquivariance h u a0 hu hub0 hinj)
    hsum

/-- Build the A-fiber cardinality boundary for moved-branch rotation-orbit
coordinates from support-complement sums, deriving orbit injectivity from the
nonzero moved hypothesis. -/
noncomputable def of_rotationOrbitOfMoved_matchingSupportComplSum
    (h : D19ActsOnMoore57 V Γ) (u a0 : V)
    (hu : ∀ d : ZMod 19, h.rotation d u = u)
    (hub0 : Γ.Adj u a0)
    {d₀ : ZMod 19} (hd₀ : d₀ ≠ 0) (hmove : h.rotation d₀ a0 ≠ a0)
    (indices : Finset (ZMod 19))
    (hsum :
      ∀ d : ZMod 19, ∀ hd : d ≠ 0,
        ∑ i ∈ indices,
          ((AFiberCoordinates.ofRotationOrbitOfMoved_rotationEquivariance
              h u a0 hu hub0 hd₀ hmove).matchingRotationPerm d i hd).supportᶜ.card =
            38) :
    AFiberCardinality38Boundary h
      (AFiberCoordinates.ofRotationOrbitOfMoved h u a0 hu hub0 hd₀ hmove)
      indices :=
  of_matchingSupportComplSum
    (AFiberCoordinates.ofRotationOrbitOfMoved_rotationEquivariance
      h u a0 hu hub0 hd₀ hmove)
    hsum

end AFiberCardinality38Boundary

end

end Moore57
