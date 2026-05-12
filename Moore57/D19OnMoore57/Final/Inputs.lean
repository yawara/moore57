import Moore57.D19OnMoore57.D19Core.GeometricInputs
import Moore57.D19OnMoore57.Misc.CharacterInputPackaging
import Moore57.D19OnMoore57.Orbit.BaseSelection

/-!
# Final D19 input packaging

This file exposes a coarser final input boundary for the D19 contradiction:
the trace-character input is split into representation data and a fixed-count
upper bound, while the orbit-base input is strengthened to a single global
coordinate-injectivity witness.
-/

namespace Moore57

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- The final split form of the character input used by the D19 pipeline.

The representation-theoretic character identities are separated from the
geometric fixed-count upper bound. -/
structure D19FinalCharacterInputs (h : D19ActsOnMoore57 V Γ) where
  /-- Representation-theoretic multiplicities and rotation character values. -/
  representation : D19ActsOnMoore57.D19RepresentationCharacterInput h
  /-- Coarse upper bound for nontrivial rotation fixed vertices. -/
  fixedUpperBound : D19ActsOnMoore57.RotationFixedUpperBoundInput h

namespace D19FinalCharacterInputs

variable {h : D19ActsOnMoore57 V Γ}

/-- Recombine the split final character inputs into the existing coarse
`D19CharacterInput`. -/
def toD19CharacterInput
    (data : D19FinalCharacterInputs h) :
    D19ActsOnMoore57.D19CharacterInput h :=
  data.representation.toD19CharacterInput data.fixedUpperBound

/-- Old bundled `TraceCharacterData` produces the final split character inputs.

This keeps old call sites usable while making the representation/fixed-bound
split explicit. -/
noncomputable def ofTraceCharacterData
    (h : D19ActsOnMoore57 V Γ)
    (hold : TraceCharacterData Γ h.rotation h.a1) :
    D19FinalCharacterInputs h where
  representation :=
    D19ActsOnMoore57.D19RepresentationCharacterInput.ofTraceCharacterData h hold
  fixedUpperBound :=
    D19ActsOnMoore57.RotationFixedUpperBoundInput.ofTraceCharacterData h hold

@[simp] theorem ofTraceCharacterData_toD19CharacterInput
    (h : D19ActsOnMoore57 V Γ)
    (hold : TraceCharacterData Γ h.rotation h.a1) :
    (ofTraceCharacterData h hold).toD19CharacterInput =
      D19ActsOnMoore57.D19CharacterInput.ofTraceCharacterData_split h hold :=
  rfl

end D19FinalCharacterInputs

/-- Final high-level input record for the D19 contradiction.

Compared with `D19GeometricInputs`, this record splits the character input into
representation and fixed-bound pieces, and asks for the stronger orbit-base
witness whose global coordinate map is injective. -/
structure D19FinalInputs (h : D19ActsOnMoore57 V Γ) where
  /-- Split character input: representation data plus fixed-count bound. -/
  character : D19FinalCharacterInputs h
  /-- Strong orbit-base witness for the 56 moved rotation orbits. -/
  orbitBase : OrbitBaseSelectionWitness h
  /-- Contribution from the fixed vertices and the `A`-side part. -/
  fixedOrAContribution : ZMod 19 → ℕ
  /-- The fixed/`A`-side contribution is `38` for nontrivial rotations. -/
  fixed_or_A_contribution :
    ∀ d : ZMod 19, d ≠ 0 → fixedOrAContribution d = 38
  /-- Adjacent-moved decomposition using the selected orbit bases. -/
  adjacentMovedDecomposition :
    D19AdjacentMovedDecomposition h orbitBase.base fixedOrAContribution

namespace D19FinalInputs

variable {h : D19ActsOnMoore57 V Γ}

/-- Forget final packaging down to the existing geometric input boundary. -/
noncomputable def toD19GeometricInputs
    (data : D19FinalInputs h) :
    D19GeometricInputs h where
  characterInput := data.character.toD19CharacterInput
  orbitBase := data.orbitBase.toInput
  fixedOrAContribution := data.fixedOrAContribution
  fixed_or_A_contribution := data.fixed_or_A_contribution
  adjacentMovedDecomposition := data.adjacentMovedDecomposition

/-- Convenience constructor from old bundled `TraceCharacterData` plus the
remaining geometric final inputs. -/
noncomputable def ofTraceCharacterData
    (h : D19ActsOnMoore57 V Γ)
    (hold : TraceCharacterData Γ h.rotation h.a1)
    (orbitBase : OrbitBaseSelectionWitness h)
    (fixedOrAContribution : ZMod 19 → ℕ)
    (fixed_or_A_contribution :
      ∀ d : ZMod 19, d ≠ 0 → fixedOrAContribution d = 38)
    (adjacentMovedDecomposition :
      D19AdjacentMovedDecomposition h orbitBase.base fixedOrAContribution) :
    D19FinalInputs h where
  character := D19FinalCharacterInputs.ofTraceCharacterData h hold
  orbitBase := orbitBase
  fixedOrAContribution := fixedOrAContribution
  fixed_or_A_contribution := fixed_or_A_contribution
  adjacentMovedDecomposition := adjacentMovedDecomposition

/-- Final D19 inputs cannot exist. -/
theorem not_nonempty (h : D19ActsOnMoore57 V Γ) :
    ¬ Nonempty (D19FinalInputs h) := by
  rintro ⟨data⟩
  exact D19GeometricInputs.not_nonempty h
    ⟨data.toD19GeometricInputs⟩

end D19FinalInputs

end Moore57
