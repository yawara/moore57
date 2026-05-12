import Moore57.D19OnMoore57.D19Core.D19ConstructiveFinalInputs
import Moore57.D19OnMoore57.D19Core.D19RepresentationCharacterDataBridge

/-!
# Component-boundary connectors for final character packages

The branch-orbit no-go frontiers consume
`D19ActsOnMoore57.RepresentationCharacterComponentsBoundary`.  This file
records the direct forgetful maps from the split final character packages to
that boundary, avoiding repeated unpacking through nonempty equivalences at
call sites.
-/

namespace Moore57

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

namespace D19FinalCharacterInputs

variable {h : D19ActsOnMoore57 V Γ}

/-- Forget the fixed-count upper-bound side, retaining the representation
component boundary consumed by branch-orbit no-go frontiers. -/
theorem representationCharacterComponentsBoundary
    (data : D19FinalCharacterInputs h) :
    D19ActsOnMoore57.RepresentationCharacterComponentsBoundary h :=
  data.representation.representationCharacterComponentsBoundary

end D19FinalCharacterInputs

namespace D19FinalInputs

variable {h : D19ActsOnMoore57 V Γ}

/-- Final inputs supply the representation component boundary through their
split final-character field. -/
theorem representationCharacterComponentsBoundary
    (data : D19FinalInputs h) :
    D19ActsOnMoore57.RepresentationCharacterComponentsBoundary h :=
  data.character.representationCharacterComponentsBoundary

end D19FinalInputs

namespace D19ConstructiveFinalInputs

variable {h : D19ActsOnMoore57 V Γ}

/-- Constructive final inputs supply the representation component boundary
through their split final-character field. -/
theorem representationCharacterComponentsBoundary
    (data : D19ConstructiveFinalInputs h) :
    D19ActsOnMoore57.RepresentationCharacterComponentsBoundary h :=
  data.character.representationCharacterComponentsBoundary

end D19ConstructiveFinalInputs

end Moore57
