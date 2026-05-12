import Moore57.D19OnMoore57.Midpoint.MiddleSupportRotationBridge
import Moore57.D19OnMoore57.BranchOrbit.ABCExceptionDoublingGeometry
import Moore57.D19OnMoore57.BranchOrbit.ABCExceptionIntersectionInvariantDecomp

/-!
# `MidpointExceptionDoublingGeometryBoundary` from the rotation bridge

This file combines:

* the rotation-bridge `mem_midpointMiddleSupport_iff_rotationCoordPerm_symm_mem_aFiberReflectionSupport`,
* the midpoint reflection criterion `MidpointReflectionCriterionBoundary`,
* the existing identity `midpointReflectionCoordPerm_eq_rotationCoordPerm_aFiberReflectionCoordPerm`,
* `aFiberReflectionCoordPerm` permutes its own support,

to derive the natural-language chain step `S_m ∩ E ⊆ S_{2m} ∩ E` of Lemma 6.3,
packaged as `MidpointExceptionDoublingGeometryBoundary`.

The natural-language argument (`moore57_d19_lean_aware_proof.md`, §6.3):
`p ∈ S_m ∩ E` ⟹ `A_m(p) ∈ E` and `p ∈ E`.  By Lemma 6.1's forward direction
applied at index `m`, `A_{2m}(p) = θ p`.  Since `θ` permutes `E` and `p ∈ E`,
`θ p ∈ E`, hence `A_{2m}(p) ∈ E`, which is `p ∈ S_{2m}`.
-/

namespace Moore57

open Finset

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

namespace BranchOrbitABCReflectionLabeling

variable {h : D19ActsOnMoore57 V Γ}

/-- Helper: rewrite `midpointMiddleSupport` along an equality of indices. -/
private theorem midpointMiddleSupport_index_subst
    (labeling : BranchOrbitABCReflectionLabeling h)
    {m m' : ZMod 19} (hmm' : m = m') :
    labeling.midpointMiddleSupport m = labeling.midpointMiddleSupport m' := by
  subst hmm'
  rfl

/-- Helper: `AFiberCoordinates.matchingEquiv` is invariant under substituting
the target index by an equal one (proof irrelevance for `i ≠ j`). -/
private theorem matchingEquiv_target_subst
    {coords : AFiberCoordinates Γ} {hΓ : IsMoore57 Γ}
    {i j j' : ZMod 19} (hjj' : j = j')
    (hij : i ≠ j) (hij' : i ≠ j')
    (p : coords.P) :
    AFiberCoordinates.matchingEquiv hΓ coords i j hij p =
      AFiberCoordinates.matchingEquiv hΓ coords i j' hij' p := by
  subst hjj'
  rfl

/-- The midpoint criterion plus the rotation bridge yield the doubling
geometry boundary `S_m ∩ E ⊆ S_{2m} ∩ E`.

This is the natural-language chain step of Lemma 6.3, derived without any
extra structural input: it uses only the existing midpoint criterion
(provable from K155) and the rotation-conjugation bridge proved in
`MidpointMiddleSupportRotationBridge`. -/
def midpointExceptionDoublingGeometryBoundary_of_criterion
    (labeling : BranchOrbitABCReflectionLabeling h)
    (criterion : MidpointReflectionCriterionBoundary labeling) :
    MidpointExceptionDoublingGeometryBoundary labeling where
  midpoint_middle_support_double m hm p hpSupport hpMid := by
    classical
    let coords := labeling.data.toAFiberCoordinates
    let rot := labeling.data.toAFiberRotationEquivariance
    -- Step 1: hpMid gives `p ∈ midpointExceptionSet m hm`.
    have hpException : p ∈ labeling.midpointExceptionSet m hm :=
      (labeling.mem_midpointExceptionSet m hm p).2 hpMid
    -- Step 2: via criterion (Lemma 6.1 ⟸), `p ∈ midpointEquationSet m hm`.
    have hpEq : p ∈ labeling.midpointEquationSet m hm :=
      (criterion.midpoint_equation_iff_exception m hm p).2 hpException
    have hmatch :
        AFiberCoordinates.matchingEquiv h.isMoore
            coords 0 (0 + (m + m))
            (index_ne_add_of_ne_zero (add_self_ne_zero_zmod19 hm)) p =
          labeling.midpointReflectionCoordPerm m p :=
      (labeling.mem_midpointEquationSet m hm p).1 hpEq
    -- Step 3: identity expressing `midpointReflectionCoordPerm` via rotation
    -- and A-fixing reflection.
    have hid :
        labeling.midpointReflectionCoordPerm m p =
          rot.coordPerm (m + m) 0
            (labeling.aFiberReflectionCoordPerm p) :=
      labeling.midpointReflectionCoordPerm_eq_rotationCoordPerm_aFiberReflectionCoordPerm
        m p
    -- Step 4: `θ p ∈ aFiberReflectionSupport` since `θ` permutes its support
    -- and `p ∈ aFiberReflectionSupport`.
    have hθpSupport :
        labeling.aFiberReflectionCoordPerm p ∈ labeling.aFiberReflectionSupport :=
      labeling.aFiberReflectionCoordPerm_mem_support_of_mem hpSupport
    -- Step 5: combine to get `matchingEquiv 0 (m+m) p` value via the bridge.
    -- Let `y = matchingEquiv 0 (m+m) p`.  Then `(rot.coordPerm (m+m) 0).symm y =
    -- aFiberReflectionCoordPerm p`, which is in `aFiberReflectionSupport`.
    have hsymm_mem :
        (rot.coordPerm (m + m) 0).symm
            (AFiberCoordinates.matchingEquiv h.isMoore
              coords 0 (0 + (m + m))
              (index_ne_add_of_ne_zero (add_self_ne_zero_zmod19 hm)) p) ∈
          labeling.aFiberReflectionSupport := by
      rw [hmatch, hid, Equiv.symm_apply_apply]
      exact hθpSupport
    -- Step 6: apply Bridge at index `(m + m)` to get
    -- `matchingEquiv 0 (m+m) p ∈ midpointMiddleSupport (m + m)`.
    have hMid_mm :
        AFiberCoordinates.matchingEquiv h.isMoore
            coords 0 (0 + (m + m))
            (index_ne_add_of_ne_zero (add_self_ne_zero_zmod19 hm)) p ∈
          labeling.midpointMiddleSupport (m + m) :=
      (labeling.mem_midpointMiddleSupport_iff_rotationCoordPerm_symm_mem_aFiberReflectionSupport
        (m + m) _).mpr hsymm_mem
    -- Step 7: convert index `(m + m)` to `(2 * m)` and chart index
    -- `0 + (m + m)` to `0 + (2 * m)`.
    have h2m : (2 : ZMod 19) * m = m + m := by ring
    have hmiddle_eq :
        labeling.midpointMiddleSupport ((2 : ZMod 19) * m) =
          labeling.midpointMiddleSupport (m + m) :=
      labeling.midpointMiddleSupport_index_subst h2m
    rw [hmiddle_eq]
    -- Goal: matchingEquiv 0 (0 + (2*m)) ... p ∈ midpointMiddleSupport (m + m).
    -- Convert the matching index `0 + (2*m)` to `0 + (m+m)`.
    have hidx : (0 : ZMod 19) + ((2 : ZMod 19) * m) = 0 + (m + m) := by
      rw [h2m]
    have hmatchEq :
        AFiberCoordinates.matchingEquiv h.isMoore
            coords 0 (0 + ((2 : ZMod 19) * m))
            (index_ne_add_of_ne_zero (two_mul_ne_zero_zmod19 hm)) p =
          AFiberCoordinates.matchingEquiv h.isMoore
            coords 0 (0 + (m + m))
            (index_ne_add_of_ne_zero (add_self_ne_zero_zmod19 hm)) p :=
      matchingEquiv_target_subst hidx _ _ p
    rw [hmatchEq]
    exact hMid_mm

/-- Final assembly: bridge + criterion give `MidpointExceptionDoublingBoundary`
(the abstract chain `S_m ∩ E ⊆ S_{2m} ∩ E`). -/
def midpointExceptionDoublingBoundary_of_criterion
    (labeling : BranchOrbitABCReflectionLabeling h)
    (criterion : MidpointReflectionCriterionBoundary labeling) :
    MidpointExceptionDoublingBoundary labeling :=
  (midpointExceptionDoublingGeometryBoundary_of_criterion labeling criterion)
    |>.toMidpointExceptionDoublingBoundary

end BranchOrbitABCReflectionLabeling

end

end Moore57
