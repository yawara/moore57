import Moore57.InternalDiffSetTranslate
import Moore57.ZMod19Lemmas

namespace Moore57

/-- Affine reindexing of a `ZMod 19`-indexed orbit. -/
def affineW {V : Type*} (W : ZMod 19 → V) (c t : ZMod 19) : ZMod 19 → V :=
  fun i => W (c * i + t)

/-- Membership in the internal difference set is sent by affine reindexing to
left multiplication by the linear coefficient. -/
theorem internalDiffSet_affine_mem
    {V : Type*} {Γ : SimpleGraph V} [DecidableRel Γ.Adj]
    (W : ZMod 19 → V) {c t d : ZMod 19} (hc : c ≠ 0)
    (hd : d ∈ internalDiffSet Γ (affineW W c t)) :
    c * d ∈ internalDiffSet Γ W := by
  classical
  rw [internalDiffSet] at hd ⊢
  rcases (by simpa using hd) with ⟨hd0, hAdj⟩
  simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, and_true] at hd0 ⊢
  refine ⟨?_, ?_⟩
  · exact mul_ne_zero hc hd0
  · intro j
    have h := hAdj (c⁻¹ * (j - t))
    have hleft : c * (c⁻¹ * (j - t)) + t = j := by
      calc
        c * (c⁻¹ * (j - t)) + t = (c * c⁻¹) * (j - t) + t := by
          rw [mul_assoc]
        _ = j := by
          rw [mul_inv_cancel₀ hc, one_mul]
          simp [sub_eq_add_neg, add_assoc]
    have hright : c * (c⁻¹ * (j - t) + d) + t = j + c * d := by
      calc
        c * (c⁻¹ * (j - t) + d) + t =
            (c * (c⁻¹ * (j - t)) + t) + c * d := by
          ring
        _ = j + c * d := by
          rw [hleft]
    simpa [affineW, hleft, hright] using h

/-- Membership in the affine internal difference set follows from membership
after multiplying the difference by the nonzero linear coefficient. -/
theorem internalDiffSet_affine_mem_of_mul_mem
    {V : Type*} {Γ : SimpleGraph V} [DecidableRel Γ.Adj]
    (W : ZMod 19 → V) {c t d : ZMod 19} (_hc : c ≠ 0)
    (hd : c * d ∈ internalDiffSet Γ W) :
    d ∈ internalDiffSet Γ (affineW W c t) := by
  classical
  rw [internalDiffSet] at hd ⊢
  rcases (by simpa using hd) with ⟨hcd0, hAdj⟩
  simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, and_true] at hcd0 ⊢
  refine ⟨?_, ?_⟩
  · exact hcd0.2
  · intro i
    have h := hAdj (c * i + t)
    have hright : c * (i + d) + t = c * i + t + c * d := by
      ring
    simpa [affineW, hright] using h

/-- Affine reindexing sends internal differences by left multiplication with
the nonzero linear coefficient. -/
theorem internalDiffSet_affine_mem_iff
    {V : Type*} {Γ : SimpleGraph V} [DecidableRel Γ.Adj]
    (W : ZMod 19 → V) {c t d : ZMod 19} (hc : c ≠ 0) :
    d ∈ internalDiffSet Γ (affineW W c t) ↔ c * d ∈ internalDiffSet Γ W :=
  ⟨internalDiffSet_affine_mem W hc, internalDiffSet_affine_mem_of_mul_mem W hc⟩

/-- Equality form of affine reindexing for `internalDiffSet`. -/
theorem internalDiffSet_affine_image
    {V : Type*} {Γ : SimpleGraph V} [DecidableRel Γ.Adj]
    (W : ZMod 19 → V) {c t : ZMod 19} (hc : c ≠ 0) :
    (internalDiffSet Γ (affineW W c t)).image (fun d => c * d) =
      internalDiffSet Γ W := by
  classical
  ext e
  constructor
  · intro he
    rcases Finset.mem_image.mp he with ⟨d, hd, rfl⟩
    exact (internalDiffSet_affine_mem_iff (Γ := Γ) W (c := c) (t := t) (d := d) hc).mp hd
  · intro he
    have hcanc : c * (c⁻¹ * e) = e := by
      calc
        c * (c⁻¹ * e) = (c * c⁻¹) * e := by
          rw [mul_assoc]
        _ = e := by
          rw [mul_inv_cancel₀ hc, one_mul]
    refine Finset.mem_image.mpr ⟨c⁻¹ * e, ?_, ?_⟩
    · exact (internalDiffSet_affine_mem_iff (Γ := Γ) W
        (c := c) (t := t) (d := c⁻¹ * e) hc).mpr (by
          simpa [hcanc] using he)
    · exact hcanc

end Moore57
