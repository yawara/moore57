import Moore57.D19OnMoore57.AFiber.AFiberOrbitBaseSelection
import Moore57.D19OnMoore57.BranchOrbit.BranchOrbitABCDataFromCenter
import Moore57.D19OnMoore57.Rotation.RotationFixedCenterNeighborOrbits

/-!
# Orbit base selection from raw action

Option B of the post-Lemma-6.3 wiring: construct the orbit-base selection
inputs (`OrbitBaseSelectionInput`, `OrbitBaseSelectionWitness`,
`OrbitBaseSelectionEnumeration`) directly from `h : D19ActsOnMoore57 V Γ`
with no additional axiomatic inputs.

The construction uses the existing
`AFiberCoordinates.toOrbitBaseSelectionInputOfMoore` machinery, which picks
the 56 orbit-base vertices from the base A-fiber coordinates by the Moore57
cardinality `|P| = 56`.  Combined with raw-action consequences supplying the
required `BranchOrbitABCFromCenter` data, this closes Option B.
-/

namespace Moore57

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

namespace BranchOrbitABCFromCenter

variable {h : D19ActsOnMoore57 V Γ}

/-- The orbit-base selection input from any `BranchOrbitABCFromCenter` data,
using the canonical `Fin 56 ≃ P` chosen by the Moore57 cardinality. -/
noncomputable def toOrbitBaseSelectionInput
    (data : BranchOrbitABCFromCenter h) :
    OrbitBaseSelectionInput h :=
  data.toAFiberCoordinates.toOrbitBaseSelectionInputOfMoore
    data.toAFiberRotationEquivariance

/-- The orbit-base selection witness (with global orbit-coordinate
injectivity) from any `BranchOrbitABCFromCenter` data, obtained via the
enumeration's `toWitness` converter. -/
noncomputable def toOrbitBaseSelectionWitness
    (data : BranchOrbitABCFromCenter h) :
    OrbitBaseSelectionWitness h :=
  (data.toAFiberCoordinates.toOrbitBaseSelectionEnumerationOfMoore
    data.toAFiberRotationEquivariance).toWitness

/-- The orbit-base selection enumeration (with explicit coordinate map) from
any `BranchOrbitABCFromCenter` data. -/
noncomputable def toOrbitBaseSelectionEnumeration
    (data : BranchOrbitABCFromCenter h) :
    OrbitBaseSelectionEnumeration h :=
  data.toAFiberCoordinates.toOrbitBaseSelectionEnumerationOfMoore
    data.toAFiberRotationEquivariance

end BranchOrbitABCFromCenter

namespace D19ActsOnMoore57

/-- The orbit-base selection input from `h : D19ActsOnMoore57 V Γ` alone,
using the canonical `BranchOrbitABCFromCenter` constructed from the rotation
fixed-center neighbor orbits. -/
noncomputable def orbitBaseSelectionInput_of_raw_action
    (h : D19ActsOnMoore57 V Γ) :
    OrbitBaseSelectionInput h :=
  (BranchOrbitABCFromCenter.ofExistsThreeRotationOrbitFinsetNeighbors h)
    |>.toOrbitBaseSelectionInput

/-- The orbit-base selection witness from `h : D19ActsOnMoore57 V Γ` alone. -/
noncomputable def orbitBaseSelectionWitness_of_raw_action
    (h : D19ActsOnMoore57 V Γ) :
    OrbitBaseSelectionWitness h :=
  (BranchOrbitABCFromCenter.ofExistsThreeRotationOrbitFinsetNeighbors h)
    |>.toOrbitBaseSelectionWitness

/-- The orbit-base selection enumeration from `h : D19ActsOnMoore57 V Γ` alone. -/
noncomputable def orbitBaseSelectionEnumeration_of_raw_action
    (h : D19ActsOnMoore57 V Γ) :
    OrbitBaseSelectionEnumeration h :=
  (BranchOrbitABCFromCenter.ofExistsThreeRotationOrbitFinsetNeighbors h)
    |>.toOrbitBaseSelectionEnumeration

end D19ActsOnMoore57

end

end Moore57
