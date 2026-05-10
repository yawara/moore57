import Moore57.ProjectionTrace
import Mathlib.Tactic

/-!
# Trace of an involutive linear map

This module records a small linear-algebra fact used by the reflection trace
pipeline: over `ℚ`, an involutive endomorphism has integer trace.  The proof
uses the idempotent projection `(1 + f) / 2` and the existing projection trace
lemma, so it avoids any representation-theory reimplementation.
-/

namespace Moore57

namespace LinearMap

noncomputable section

variable {W : Type*} [AddCommGroup W] [Module ℚ W] [FiniteDimensional ℚ W]

/-- An idempotent endomorphism has trace equal to the dimension of its range. -/
theorem trace_eq_finrank_range_of_isIdempotentElem
    (p : W →ₗ[ℚ] W) (hp : IsIdempotentElem p) :
    _root_.LinearMap.trace ℚ W p =
      (Module.finrank ℚ (_root_.LinearMap.range p) : ℚ) := by
  have h :=
    trace_restrict_range_eq_trace_comp_of_isIdempotentElem
      (K := ℚ) (V := W) p 1 hp (by simp)
  have hid :
      (1 : W →ₗ[ℚ] W).restrict (by
        intro x hx
        exact hx) =
        (1 : _root_.LinearMap.range p →ₗ[ℚ] _root_.LinearMap.range p) := by
    ext x
    rfl
  simpa [hid, _root_.LinearMap.trace_id] using h.symm

/-- The projection `(1 + f) / 2` attached to an involution. -/
def involutionProjection (f : W →ₗ[ℚ] W) : W →ₗ[ℚ] W :=
  (1 / 2 : ℚ) • (1 + f)

omit [FiniteDimensional ℚ W] in
theorem involutionProjection_isIdempotentElem
    (f : W →ₗ[ℚ] W) (hf : f * f = 1) :
    IsIdempotentElem (involutionProjection f) := by
  rw [IsIdempotentElem]
  ext x
  change involutionProjection f (involutionProjection f x) = involutionProjection f x
  have hffx : f (f x) = x := by
    have h := congrArg (fun g : Module.End ℚ W => g x) hf
    simpa [Module.End.mul_apply] using h
  simp [involutionProjection, hffx]
  module

/-- Trace formula for an involutive endomorphism over `ℚ`. -/
theorem trace_eq_two_finrank_involutionProjection_sub_finrank
    (f : W →ₗ[ℚ] W) (hf : f * f = 1) :
    _root_.LinearMap.trace ℚ W f =
      (2 * (Module.finrank ℚ (_root_.LinearMap.range (involutionProjection f)) : ℤ) -
          (Module.finrank ℚ W : ℤ) : ℤ) := by
  let p := involutionProjection f
  have hp : IsIdempotentElem p := involutionProjection_isIdempotentElem f hf
  have hptrace :
      _root_.LinearMap.trace ℚ W p =
        (Module.finrank ℚ (_root_.LinearMap.range p) : ℚ) :=
    trace_eq_finrank_range_of_isIdempotentElem p hp
  have hplinear :
      _root_.LinearMap.trace ℚ W p =
        (1 / 2 : ℚ) *
          ((Module.finrank ℚ W : ℚ) + _root_.LinearMap.trace ℚ W f) := by
    simp [p, involutionProjection, one_div]
    ring
  have htraceℚ :
      _root_.LinearMap.trace ℚ W f =
        2 * (Module.finrank ℚ (_root_.LinearMap.range p) : ℚ) -
          (Module.finrank ℚ W : ℚ) := by
    rw [hplinear] at hptrace
    linarith
  norm_num
  exact htraceℚ

/-- An involutive endomorphism over `ℚ` has integer trace. -/
theorem exists_int_trace_of_involutive
    (f : W →ₗ[ℚ] W) (hf : f * f = 1) :
    ∃ z : ℤ, _root_.LinearMap.trace ℚ W f = (z : ℚ) :=
  ⟨2 * (Module.finrank ℚ (_root_.LinearMap.range (involutionProjection f)) : ℤ) -
      (Module.finrank ℚ W : ℤ),
    trace_eq_two_finrank_involutionProjection_sub_finrank f hf⟩

end

end LinearMap

end Moore57
