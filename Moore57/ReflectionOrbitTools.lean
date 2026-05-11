import Moore57.RotationOrbitFinset
import Moore57.Foundations.ZMod19.Lemmas

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

/-- If a reflection sends a point into its rotation orbit, then some reflection
in the same dihedral coset fixes that point exactly. -/
theorem exists_reflection_smul_fixed_of_reflection_mem_rotationOrbitFinset
    (h : D19ActsOnMoore57 V Γ) {k : ZMod 19} {x : V}
    (hrefOrbit :
      h.smul (DihedralGroup.sr k) x ∈ h.rotationOrbitFinset x) :
    ∃ k' : ZMod 19, h.smul (DihedralGroup.sr k') x = x := by
  rcases (h.mem_rotationOrbitFinset x
      (h.smul (DihedralGroup.sr k) x)).mp hrefOrbit with ⟨j, hj⟩
  refine ⟨k + j, ?_⟩
  calc
    h.smul (DihedralGroup.sr (k + j)) x
        = h.smul (DihedralGroup.sr k) (h.rotation j x) := by
          change h.smul (DihedralGroup.sr (k + j)) x =
            h.smul (DihedralGroup.sr k) (h.smul (DihedralGroup.r j) x)
          rw [← h.mul_smul, DihedralGroup.sr_mul_r]
    _ = h.rotation (-j) (h.smul (DihedralGroup.sr k) x) := by
          exact (h.rotation_neg_reflection_smul k j x).symm
    _ = h.rotation (-j) (h.rotation j x) := by
          rw [← hj]
    _ = x := by
          simpa [Equiv.Perm.mul_apply] using
            congrArg (fun σ : Equiv.Perm V => σ x)
              (h.rotation_add (-j) j).symm

/-- If a reflection preserves a full rotation orbit, then it has a unique
fixed point on that orbit.  This is the local counting fact needed for
representative-family arguments over rotation orbits. -/
theorem existsUnique_reflection_fixed_mem_rotationOrbitFinset_of_reflection_mem
    (h : D19ActsOnMoore57 V Γ) {k : ZMod 19} {x : V}
    (hinj : Function.Injective fun i : ZMod 19 => h.rotation i x)
    (hrefOrbit :
      h.smul (DihedralGroup.sr k) x ∈ h.rotationOrbitFinset x) :
    ∃! y : V,
      y ∈ h.rotationOrbitFinset x ∧
        h.smul (DihedralGroup.sr k) y = y := by
  rcases (h.mem_rotationOrbitFinset x
      (h.smul (DihedralGroup.sr k) x)).mp hrefOrbit with ⟨i, hi⟩
  let t : ZMod 19 := (2 : ZMod 19)⁻¹ * i
  let y : V := h.rotation t x
  refine ⟨y, ?_, ?_⟩
  · constructor
    · exact (h.mem_rotationOrbitFinset x y).mpr ⟨t, rfl⟩
    · dsimp [y]
      have htwo :
          (2 : ZMod 19) * t = i := by
        dsimp [t]
        rw [← mul_assoc, mul_inv_cancel₀ two_ne_zero_zmod19, one_mul]
      have htwo_add :
          t + t = i := by
        rw [← two_mul, htwo]
      have hneg_add :
          -t + i = t := by
        calc
          -t + i
              = -t + (t + t) := by rw [htwo_add]
          _ = t := by abel
      calc
        h.smul (DihedralGroup.sr k) (h.rotation t x)
            = h.rotation (-t) (h.smul (DihedralGroup.sr k) x) := by
                exact h.reflection_smul_rotation k t x
        _ = h.rotation (-t) (h.rotation i x) := by rw [← hi]
        _ = h.rotation (-t + i) x := by
                simpa [Equiv.Perm.mul_apply] using
                  congrArg (fun σ : Equiv.Perm V => σ x)
                    (h.rotation_add (-t) i).symm
        _ = h.rotation t x := by rw [hneg_add]
  · intro z hz
    rcases hz with ⟨hzOrbit, hzFixed⟩
    rcases (h.mem_rotationOrbitFinset x z).mp hzOrbit with ⟨j, hj⟩
    have hcoord :
        -j + i = j := by
      apply hinj
      calc
        h.rotation (-j + i) x
            = h.rotation (-j) (h.rotation i x) := by
                simpa [Equiv.Perm.mul_apply] using
                  congrArg (fun σ : Equiv.Perm V => σ x)
                    (h.rotation_add (-j) i)
        _ = h.rotation (-j) (h.smul (DihedralGroup.sr k) x) := by rw [hi]
        _ = h.smul (DihedralGroup.sr k) (h.rotation j x) := by
                exact h.rotation_neg_reflection_smul k j x
        _ = h.rotation j x := by rw [hj, hzFixed]
    have htwo_j : (2 : ZMod 19) * j = i := by
      calc
        (2 : ZMod 19) * j = j + j := by ring
        _ = (-j + i) + j := by rw [hcoord]
        _ = i := by abel
    have hj_eq : j = t := by
      calc
        j = (2 : ZMod 19)⁻¹ * ((2 : ZMod 19) * j) := by
              rw [← mul_assoc, inv_mul_cancel₀ two_ne_zero_zmod19, one_mul]
        _ = (2 : ZMod 19)⁻¹ * i := by rw [htwo_j]
        _ = t := by rfl
    rw [← hj, hj_eq]

/-- If a reflection sends a rotation orbit to a disjoint rotation orbit, then
there are no reflection-fixed vertices on the original orbit. -/
theorem not_exists_reflection_fixed_mem_rotationOrbitFinset_of_disjoint_reflection
    (h : D19ActsOnMoore57 V Γ) {k : ZMod 19} {x : V}
    (hdisj :
      Disjoint (h.rotationOrbitFinset x)
        (h.rotationOrbitFinset (h.smul (DihedralGroup.sr k) x))) :
    ¬ ∃ y : V,
      y ∈ h.rotationOrbitFinset x ∧
        h.smul (DihedralGroup.sr k) y = y := by
  rintro ⟨y, hyOrbit, hyFixed⟩
  have hyImage :
      (h.smulEquiv (DihedralGroup.sr k)) y ∈
        (h.rotationOrbitFinset x).image
          (h.smulEquiv (DihedralGroup.sr k)) :=
    Finset.mem_image_of_mem (h.smulEquiv (DihedralGroup.sr k)) hyOrbit
  have hyReflectedOrbit :
      y ∈ h.rotationOrbitFinset (h.smul (DihedralGroup.sr k) x) := by
    have hyImage' :
        y ∈ (h.rotationOrbitFinset x).image
          (h.smulEquiv (DihedralGroup.sr k)) := by
      change h.smul (DihedralGroup.sr k) y ∈
        (h.rotationOrbitFinset x).image
          (h.smulEquiv (DihedralGroup.sr k)) at hyImage
      rw [← hyFixed]
      exact hyImage
    simpa [h.reflection_image_rotationOrbitFinset k x] using hyImage'
  exact (Finset.disjoint_left.mp hdisj) hyOrbit hyReflectedOrbit

/-- Cardinal form of
`not_exists_reflection_fixed_mem_rotationOrbitFinset_of_disjoint_reflection`. -/
theorem reflection_fixed_points_in_rotationOrbitFinset_card_eq_zero_of_disjoint_reflection
    (h : D19ActsOnMoore57 V Γ) {k : ZMod 19} {x : V}
    (hdisj :
      Disjoint (h.rotationOrbitFinset x)
        (h.rotationOrbitFinset (h.smul (DihedralGroup.sr k) x))) :
    ((h.rotationOrbitFinset x).filter
        fun z : V => h.smul (DihedralGroup.sr k) z = z).card = 0 := by
  classical
  rw [Finset.card_filter_eq_zero_iff]
  intro y hyOrbit hyFixed
  exact
    h.not_exists_reflection_fixed_mem_rotationOrbitFinset_of_disjoint_reflection
      hdisj ⟨y, hyOrbit, hyFixed⟩

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
