import Moore57.RotationOrbitFinset

namespace Moore57

namespace D19ActsOnMoore57

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- A reflection sends the `i`-th rotation translate of `x` to the `-i`-th
rotation translate of the reflected base point. -/
theorem reflection_smul_rotation
    (h : D19ActsOnMoore57 V Γ) (k i : ZMod 19) (x : V) :
    h.smul (DihedralGroup.sr k) (h.rotation i x) =
      h.rotation (-i) (h.smul (DihedralGroup.sr k) x) := by
  change h.smul (DihedralGroup.sr k) (h.smul (DihedralGroup.r i) x) =
    h.smul (DihedralGroup.r (-i)) (h.smul (DihedralGroup.sr k) x)
  rw [← h.mul_smul, ← h.mul_smul]
  rw [DihedralGroup.sr_mul_r, DihedralGroup.r_mul_sr]
  simp [sub_eq_add_neg]

/-- A rotation by `-d` after reflecting agrees with reflecting after a rotation
by `d`. -/
theorem rotation_neg_reflection_smul
    (h : D19ActsOnMoore57 V Γ) (k d : ZMod 19) (x : V) :
    h.rotation (-d) (h.smul (DihedralGroup.sr k) x) =
      h.smul (DihedralGroup.sr k) (h.rotation d x) := by
  change h.smul (DihedralGroup.r (-d)) (h.smul (DihedralGroup.sr k) x) =
    h.smul (DihedralGroup.sr k) (h.smul (DihedralGroup.r d) x)
  rw [← h.mul_smul, ← h.mul_smul]
  rw [DihedralGroup.r_mul_sr, DihedralGroup.sr_mul_r]
  simp [sub_eq_add_neg]

/-- Reflection changes the adjacent-moved rotation offset from `d` to `-d`. -/
theorem reflection_adjacent_rotation_iff
    (h : D19ActsOnMoore57 V Γ) (k d : ZMod 19) (x : V) :
    Γ.Adj (h.smul (DihedralGroup.sr k) x)
        (h.rotation (-d) (h.smul (DihedralGroup.sr k) x)) ↔
      Γ.Adj x (h.rotation d x) := by
  have hAdj :=
    h.smul_adj (DihedralGroup.sr k) x (h.rotation d x)
  simpa [h.rotation_neg_reflection_smul k d x] using hAdj.symm

/-- The image of a rotation orbit under a reflection is the rotation orbit of
the reflected base point. -/
theorem reflection_image_rotationOrbitFinset
    (h : D19ActsOnMoore57 V Γ) (k : ZMod 19) (x : V) :
    (h.rotationOrbitFinset x).image (h.smulEquiv (DihedralGroup.sr k)) =
      h.rotationOrbitFinset (h.smul (DihedralGroup.sr k) x) := by
  classical
  ext y
  constructor
  · intro hy
    rcases Finset.mem_image.mp hy with ⟨z, hz, rfl⟩
    rcases (h.mem_rotationOrbitFinset x z).mp hz with ⟨i, rfl⟩
    exact (h.mem_rotationOrbitFinset (h.smul (DihedralGroup.sr k) x)
      ((h.smulEquiv (DihedralGroup.sr k)) (h.rotation i x))).mpr
        ⟨-i, by
          change h.rotation (-i) (h.smul (DihedralGroup.sr k) x) =
            h.smul (DihedralGroup.sr k) (h.rotation i x)
          exact (h.reflection_smul_rotation k i x).symm⟩
  · intro hy
    rcases (h.mem_rotationOrbitFinset (h.smul (DihedralGroup.sr k) x) y).mp hy
      with ⟨i, rfl⟩
    refine Finset.mem_image.mpr
      ⟨h.rotation (-i) x,
        (h.mem_rotationOrbitFinset x (h.rotation (-i) x)).mpr ⟨-i, rfl⟩, ?_⟩
    change h.smul (DihedralGroup.sr k) (h.rotation (-i) x) =
      h.rotation i (h.smul (DihedralGroup.sr k) x)
    simpa using h.reflection_smul_rotation k (-i) x

/-- Preimage form of `reflection_image_rotationOrbitFinset`. -/
theorem reflection_preimage_rotationOrbitFinset
    (h : D19ActsOnMoore57 V Γ) (k : ZMod 19) (x : V) :
    (h.rotationOrbitFinset (h.smul (DihedralGroup.sr k) x)).preimage
        (h.smulEquiv (DihedralGroup.sr k))
        (h.smulEquiv (DihedralGroup.sr k)).injective.injOn =
      h.rotationOrbitFinset x := by
  classical
  ext y
  constructor
  · intro hy
    have hyImage :
        (h.smulEquiv (DihedralGroup.sr k)) y ∈
          (h.rotationOrbitFinset x).image (h.smulEquiv (DihedralGroup.sr k)) := by
      simpa [h.reflection_image_rotationOrbitFinset k x] using
        (Finset.mem_preimage.mp hy)
    rcases Finset.mem_image.mp hyImage with ⟨z, hz, hzy⟩
    exact (h.smulEquiv (DihedralGroup.sr k)).injective hzy ▸ hz
  · intro hy
    exact Finset.mem_preimage.mpr (by
      simpa [← h.reflection_image_rotationOrbitFinset k x] using
        Finset.mem_image_of_mem (h.smulEquiv (DihedralGroup.sr k)) hy)

/-- Reflection identifies the adjacent-moved filter on an orbit for `d` with
the reflected orbit filter for `-d`. -/
theorem reflection_image_filter_adjacent_rotation_moved
    (h : D19ActsOnMoore57 V Γ) (k d : ZMod 19) (x : V) :
    ((h.rotationOrbitFinset x).filter fun y => Γ.Adj y (h.rotation d y)).image
        (h.smulEquiv (DihedralGroup.sr k)) =
      (h.rotationOrbitFinset (h.smul (DihedralGroup.sr k) x)).filter
        fun y => Γ.Adj y (h.rotation (-d) y) := by
  classical
  ext z
  constructor
  · intro hz
    rcases Finset.mem_image.mp hz with ⟨y, hy, rfl⟩
    rcases Finset.mem_filter.mp hy with ⟨hyOrbit, hyAdj⟩
    refine Finset.mem_filter.mpr ⟨?_, ?_⟩
    · simpa [h.reflection_image_rotationOrbitFinset k x] using
        Finset.mem_image_of_mem (h.smulEquiv (DihedralGroup.sr k)) hyOrbit
    · change Γ.Adj (h.smul (DihedralGroup.sr k) y)
        (h.rotation (-d) (h.smul (DihedralGroup.sr k) y))
      exact (h.reflection_adjacent_rotation_iff k d y).mpr hyAdj
  · intro hz
    rcases Finset.mem_filter.mp hz with ⟨hzOrbit, hzAdj⟩
    have hzImage :
        z ∈ (h.rotationOrbitFinset x).image
            (h.smulEquiv (DihedralGroup.sr k)) := by
      simpa [h.reflection_image_rotationOrbitFinset k x] using hzOrbit
    rcases Finset.mem_image.mp hzImage with ⟨y, hyOrbit, rfl⟩
    refine Finset.mem_image.mpr ⟨y, ?_, rfl⟩
    refine Finset.mem_filter.mpr ⟨hyOrbit, ?_⟩
    apply (h.reflection_adjacent_rotation_iff k d y).mp
    simpa using hzAdj

/-- Cardinal form of `reflection_image_filter_adjacent_rotation_moved`: the
reflected orbit with offset `-d` contributes the same number as the original
orbit with offset `d`. -/
theorem reflection_filter_adjacent_rotation_moved_card_eq
    (h : D19ActsOnMoore57 V Γ) (k d : ZMod 19) (x : V) :
    ((h.rotationOrbitFinset (h.smul (DihedralGroup.sr k) x)).filter
        fun y => Γ.Adj y (h.rotation (-d) y)).card =
      ((h.rotationOrbitFinset x).filter
        fun y => Γ.Adj y (h.rotation d y)).card := by
  classical
  rw [← h.reflection_image_filter_adjacent_rotation_moved k d x]
  exact Finset.card_image_of_injective _
    (h.smulEquiv (DihedralGroup.sr k)).injective

end D19ActsOnMoore57

end Moore57
