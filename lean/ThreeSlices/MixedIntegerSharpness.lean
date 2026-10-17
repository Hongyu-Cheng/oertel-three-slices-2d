import ThreeSlices.MixedInteger
import ThreeSlices.Sharpness
import ThreeSlices.ConvexHullSlices

open Set

namespace ThreeSlices

def sharpConvexBody (r : ℝ) : Set Space :=
  sharpHull (sharpSmallTriangle r) standardChordTriangle

lemma sharpConvexBody_compact (r : ℝ) : IsCompact (sharpConvexBody r) :=
  isCompact_sharpHull (sharpSmallTriangle_isBody r) isBody_standardChordTriangle

lemma sharpConvexBody_sliceBodies (r : ℝ) (hr : 0 ≤ r) (hr₁ : r ≤ 1) :
    sliceBodies (sharpConvexBody r) 0 = sharpBodies r := by
  funext i
  have h := sliceAt_sharpHull_fin (sharpSmallTriangle_isBody r).2.1
    isBody_standardChordTriangle.2.1 (sharpSmallTriangle_subset r hr hr₁) i
  fin_cases i <;> simpa [sliceBodies, sharpConvexBody, sharpBodies] using h

lemma sharpConvexBody_zero_other (r : ℝ) (hr : 0 ≤ r) (hr₁ : r ≤ 1) (z : ℤ)
    (hz : ¬ ∃ i : Fin 3, z = 0 + (i : ℤ)) : area (sliceAt (sharpConvexBody r) z) = 0 := by
  have h := sliceAt_sharpHull_int_empty_of_not_fin (sharpSmallTriangle_isBody r).2.1
    isBody_standardChordTriangle.2.1 (sharpSmallTriangle_subset r hr hr₁)
    (by simpa using hz)
  simp [sharpConvexBody, h, area]

lemma mixedArea_sharpConvexBody (r : ℝ) (hr : 0 ≤ r) (hr₁ : r ≤ 1) :
    mixedArea (sharpConvexBody r) = totalArea (sharpBodies r) := by
  have h := mixedArea_eq_three_slices (sharpConvexBody_compact r) 0
    (sharpConvexBody_zero_other r hr hr₁)
  change mixedArea (sharpConvexBody r) = totalArea (sliceBodies (sharpConvexBody r) 0) at h
  rwa [sharpConvexBody_sliceBodies r hr hr₁] at h

lemma positiveSlices_sharpConvexBody (r : ℝ) (hr : 0 < r) (hr₁ : r ≤ 1) :
    (positiveSlices (sharpConvexBody r)).ncard = 3 := by
  have hset : positiveSlices (sharpConvexBody r) = Set.range (fun i : Fin 3 => (i : ℤ)) := by
    ext z
    constructor
    · intro hz
      by_contra hn
      have he := sharpConvexBody_zero_other r hr.le hr₁ z (by simpa [eq_comm] using hn)
      exact (ne_of_gt hz) he
    · rintro ⟨i, rfl⟩
      have h := area_sharpBodies_pos r hr i
      rw [← sharpConvexBody_sliceBodies r hr.le hr₁] at h
      simpa [positiveSlices, sliceBodies] using h
  rw [hset, Set.ncard_range_of_injective]
  · simp
  · intro i j h
    exact Fin.ext (Int.ofNat.inj h)

/-- Convex mixed-integer examples rule out every fraction strictly larger than two ninths. -/
theorem mixed_integer_sharpness (c : ℝ) (hc : (2 / 9 : ℝ) < c) :
    ∃ C : Set Space, IsCompact C ∧ Convex ℝ C ∧ (positiveSlices C).ncard = 3 ∧
      0 < mixedArea C ∧ ∀ z : ℤ, ∀ x : Plane, ((z : ℝ), x) ∈ C →
        ∃ H : Halfspace, H.Proper ∧ ((z : ℝ), x) ∈ H.closedSet ∧
          mixedArea (C ∩ H.closedSet) < c * mixedArea C := by
  obtain ⟨r, hr, hr₁, hbound⟩ := sharpness_factor c hc
  have hmass := mixedArea_sharpConvexBody r hr.le hr₁.le
  refine ⟨sharpConvexBody r, sharpConvexBody_compact r,
    convex_sharpHull _ _, positiveSlices_sharpConvexBody r hr hr₁.le, ?_, ?_⟩
  · rw [hmass]
    exact totalArea_sharpBodies_pos r
  intro z x hx
  obtain ⟨i, rfl, hxi⟩ := (mem_sharpHull_integer_iff (sharpSmallTriangle_isBody r).2.1
    isBody_standardChordTriangle.2.1 (sharpSmallTriangle_subset r hr.le hr₁.le) z x).mp hx
  have hxi' : x ∈ sharpBodies r i := by
    fin_cases i <;> simpa [sharpBodies] using hxi
  obtain ⟨H, hproper, hH, hsmall⟩ := sharpBodies_small_halfspace r i x hxi'
  refine ⟨H, hproper, ?_, ?_⟩
  · simpa [Halfspace.closedCap, Halfspace.closedSet] using hH
  rw [mixedArea_inter_closedSet_eq (sharpConvexBody_compact r) 0
    (sharpConvexBody_zero_other r hr.le hr₁.le) H,
    Halfspace.shiftHeight_zero, sharpConvexBody_sliceBodies r hr.le hr₁.le, hmass]
  apply hsmall.trans_lt (hbound.trans_le _)
  rw [totalArea_sharpBodies]
  have hc₀ : 0 < c := by linarith
  nlinarith [sq_nonneg r]

end ThreeSlices
