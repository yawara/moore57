import Mathlib.Algebra.DirectSum.LinearMap
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Projection

/-!
# Trace of a commuting idempotent projection

This file isolates the linear-algebra step needed to treat an idempotent
matrix commuting with a representation as the character of the induced action
on its range.
-/

namespace Moore57

namespace LinearMap

open DirectSum

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
variable [FiniteDimensional K V]

set_option linter.flexible false in
/-- If an idempotent projection `p` commutes with `f`, then the trace of `f`
on the range of `p` is the trace of `p ∘ f` on the ambient space. -/
theorem trace_restrict_range_eq_trace_comp_of_isIdempotentElem
    (p f : V →ₗ[K] V) (hp : IsIdempotentElem p) (hcomm : Commute p f) :
    _root_.LinearMap.trace K (_root_.LinearMap.range p)
      (f.restrict (by
        intro x hx
        exact ((Module.End.mem_invtSubmodule_iff_mapsTo (f := f)).mp
          ((_root_.LinearMap.IsIdempotentElem.commute_iff hp (T := f)).mp hcomm).1) hx)) =
      _root_.LinearMap.trace K V (p ∘ₗ f) := by
  classical
  let N : Bool → Submodule K V :=
    fun b => if b then _root_.LinearMap.ker p else _root_.LinearMap.range p
  have hInternal : DirectSum.IsInternal N := by
    refine (DirectSum.isInternal_submodule_iff_isCompl N (i := false) (j := true) (by decide)
      (by
        ext b
        cases b <;> simp)).mpr ?_
    change IsCompl (_root_.LinearMap.range p) (_root_.LinearMap.ker p)
    exact _root_.LinearMap.IsIdempotentElem.isCompl hp
  have hcomm_parts := (_root_.LinearMap.IsIdempotentElem.commute_iff hp (T := f)).mp hcomm
  have hmaps_f : ∀ b, Set.MapsTo f (N b) (N b) := by
    intro b
    cases b
    · change Set.MapsTo f (_root_.LinearMap.range p) (_root_.LinearMap.range p)
      exact (Module.End.mem_invtSubmodule_iff_mapsTo (f := f)).mp hcomm_parts.1
    · change Set.MapsTo f (_root_.LinearMap.ker p) (_root_.LinearMap.ker p)
      exact (Module.End.mem_invtSubmodule_iff_mapsTo (f := f)).mp hcomm_parts.2
  have hmaps_pf : ∀ b, Set.MapsTo (p ∘ₗ f) (N b) (N b) := by
    intro b x hx
    cases b
    · change p (f x) ∈ _root_.LinearMap.range p
      exact _root_.LinearMap.mem_range_self p (f x)
    · change p (f x) ∈ _root_.LinearMap.ker p
      have hfx : f x ∈ _root_.LinearMap.ker p := hmaps_f true hx
      change p (p (f x)) = 0
      rw [← Module.End.mul_apply, hp.eq, _root_.LinearMap.mem_ker.mp hfx]
  have htrace_pf :=
    _root_.LinearMap.trace_eq_sum_trace_restrict hInternal hmaps_pf
  have hrange :
      (p ∘ₗ f).restrict (hmaps_pf false) =
        f.restrict (hmaps_f false) := by
    ext x
    change p (f x) = f x
    exact (_root_.LinearMap.IsIdempotentElem.mem_range_iff hp).mp
      (hmaps_f false x.property)
  have hker :
      (p ∘ₗ f).restrict (hmaps_pf true) = 0 := by
    ext x
    change p (f x) = 0
    exact _root_.LinearMap.mem_ker.mp (hmaps_f true x.property)
  have hrange' :
      (p ∘ₗ f).restrict (by
        change Set.MapsTo (p ∘ₗ f) (_root_.LinearMap.range p) (_root_.LinearMap.range p)
        exact hmaps_pf false) =
        f.restrict (by
          change Set.MapsTo f (_root_.LinearMap.range p) (_root_.LinearMap.range p)
          exact hmaps_f false) := by
    simpa [N] using hrange
  have hker' :
      (p ∘ₗ f).restrict (by
        change Set.MapsTo (p ∘ₗ f) (_root_.LinearMap.ker p) (_root_.LinearMap.ker p)
        exact hmaps_pf true) =
        (0 : _root_.LinearMap.ker p →ₗ[K] _root_.LinearMap.ker p) := by
    simpa [N] using hker
  change _root_.LinearMap.trace K (_root_.LinearMap.range p)
      (f.restrict (hmaps_f false)) =
    _root_.LinearMap.trace K V (p ∘ₗ f)
  rw [htrace_pf]
  rw [Fintype.sum_bool]
  simp [N]
  rw [hker', hrange']
  have htrace_zero :
      _root_.LinearMap.trace K (_root_.LinearMap.ker p)
        (0 : _root_.LinearMap.ker p →ₗ[K] _root_.LinearMap.ker p) = 0 :=
    (_root_.LinearMap.trace K (_root_.LinearMap.ker p)).map_zero
  change _root_.LinearMap.trace K (_root_.LinearMap.range p)
      (f.restrict (hmaps_f false)) =
    _root_.LinearMap.trace K (_root_.LinearMap.ker p)
        (0 : _root_.LinearMap.ker p →ₗ[K] _root_.LinearMap.ker p) +
      _root_.LinearMap.trace K (_root_.LinearMap.range p)
        (f.restrict (hmaps_f false))
  rw [htrace_zero, zero_add]

end LinearMap

end Moore57
