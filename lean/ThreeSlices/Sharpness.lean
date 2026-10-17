import ThreeSlices.SharpTriangle
import ThreeSlices.Scaling
import ThreeSlices.HalfspaceGeometry
import Grunbaum.SimplexCentroidCoordinates

open Set MeasureTheory
open scoped Pointwise

namespace ThreeSlices

lemma Halfspace.linearImage_proper (H : Halfspace) (E : Plane ≃L[ℝ] Plane)
    (hH : H.Proper) : (H.linearImage E).Proper := by
  rcases hH with hh | hp
  · exact Or.inl hh
  · apply Or.inr
    intro h
    apply hp
    ext x
    have hx := congrArg (fun f : Plane →L[ℝ] ℝ => f (E x)) h
    simpa [Halfspace.linearImage] using hx

/-- The centroid of the standard area-one-half triangle. -/
noncomputable def sharpCentroid : Plane := WithLp.toLp 2 ![(1 / 3 : ℝ), 1 / 3]

theorem sharpCentroid_eq_planarCentroid :
    sharpCentroid = planarCentroid standardChordTriangle := by
  have hT : standardChordTriangle = Grunbaum.simplexSet 2 := by
    ext x
    simp [standardChordTriangle, Grunbaum.simplexSet, Grunbaum.coordinateSum_apply,
      Fin.forall_fin_succ, Fin.sum_univ_two, and_assoc]
  rw [planarCentroid, hT]
  change sharpCentroid = Grunbaum.simplexCentroid 2
  ext i
  rw [Grunbaum.simplexCentroid_apply]
  fin_cases i <;> norm_num [sharpCentroid]

/-- The bottom slice is a centroid homothety of the two large slices. -/
def sharpSmallTriangle (r : ℝ) : Set Plane :=
  AffineMap.homothety sharpCentroid r '' standardChordTriangle

def sharpBodies (r : ℝ) : Bodies :=
  fun i => if i = 0 then sharpSmallTriangle r else standardChordTriangle

@[simp] lemma sharpBodies_zero (r : ℝ) : sharpBodies r 0 = sharpSmallTriangle r := by
  simp [sharpBodies]

@[simp] lemma sharpBodies_one (r : ℝ) : sharpBodies r 1 = standardChordTriangle := by
  simp [sharpBodies]

@[simp] lemma sharpBodies_two (r : ℝ) : sharpBodies r 2 = standardChordTriangle := by
  simp [sharpBodies]

@[simp] lemma sharpHomothety_apply (r : ℝ) (x : Plane) (i : Fin 2) :
    AffineMap.homothety sharpCentroid r x i = r * (x i - 1 / 3) + 1 / 3 := by
  fin_cases i <;> simp [AffineMap.homothety_apply, sharpCentroid]

lemma sharpSmallTriangle_subset (r : ℝ) (hr : 0 ≤ r) (hr₁ : r ≤ 1) :
    sharpSmallTriangle r ⊆ standardChordTriangle := by
  rintro _ ⟨x, hx, rfl⟩
  change 0 ≤ x 0 ∧ 0 ≤ x 1 ∧ x 0 + x 1 ≤ 1 at hx
  simp only [standardChordTriangle, mem_ofPred_eq, sharpHomothety_apply]
  have h₀ := mul_nonneg hr hx.1
  have h₁ := mul_nonneg hr hx.2.1
  have h₂ := mul_le_mul_of_nonneg_left hx.2.2 hr
  constructor
  · nlinarith
  · constructor <;> nlinarith

lemma area_sharpSmallTriangle (r : ℝ) : area (sharpSmallTriangle r) = r ^ 2 / 2 := by
  unfold area sharpSmallTriangle Measure.real
  rw [Measure.addHaar_image_homothety, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (abs_nonneg _)]
  have hd : Module.finrank ℝ Plane = 2 := by simp [Plane]
  rw [hd, abs_of_nonneg (sq_nonneg r)]
  change r ^ 2 * area standardChordTriangle = _
  rw [area_standardChordTriangle]
  ring

lemma totalArea_sharpBodies (r : ℝ) : totalArea (sharpBodies r) = 1 + r ^ 2 / 2 := by
  simp [totalArea, Fin.sum_univ_three, area_sharpSmallTriangle, area_standardChordTriangle]
  ring

lemma totalArea_sharpBodies_pos (r : ℝ) : 0 < totalArea (sharpBodies r) := by
  rw [totalArea_sharpBodies]
  positivity

lemma area_sharpBodies_pos (r : ℝ) (hr : 0 < r) : ∀ i, 0 < area (sharpBodies r i) := by
  intro i
  fin_cases i <;> simp [area_sharpSmallTriangle, area_standardChordTriangle]
  positivity

lemma sharpSmallTriangle_isBody (r : ℝ) :
    IsBody (sharpSmallTriangle r) :=
  ⟨isBody_standardChordTriangle.1.image (AffineMap.homothety_continuous _ _),
    isBody_standardChordTriangle.2.1.affine_image _,
    isBody_standardChordTriangle.2.2.image _⟩

lemma sharpBodies_isBody (r : ℝ) :
    ∀ i, IsBody (sharpBodies r i) := by
  intro i
  fin_cases i
  · exact sharpSmallTriangle_isBody r
  · exact isBody_standardChordTriangle
  · exact isBody_standardChordTriangle

lemma sharpBodies_compatible (r : ℝ) (hr : 0 ≤ r) (hr₁ : r ≤ 1) :
    Compatible (sharpBodies r) := by
  rintro _ ⟨_, ⟨x, hx, rfl⟩, _, ⟨y, hy, rfl⟩, rfl⟩
  exact isBody_standardChordTriangle.2.1 (sharpSmallTriangle_subset r hr hr₁ hx) hy
    (by norm_num) (by norm_num) (by norm_num)

def sharpBottomHalfspace : Halfspace := ⟨1, 0, 0⟩

lemma mem_sharpBottomHalfspace (x : Plane) : x ∈ sharpBottomHalfspace.closedCap 0 := by
  simp [sharpBottomHalfspace, Halfspace.closedCap]

lemma closedMass_sharpBottomHalfspace (r : ℝ) :
    closedMass (sharpBodies r) sharpBottomHalfspace = r ^ 2 / 2 := by
  simp [closedMass, Fin.sum_univ_three, sharpBottomHalfspace, Halfspace.closedCap,
    area_sharpSmallTriangle]
  simp [area]

/-- Tilt the cut at height one until the height-two slice is beyond its lower range. -/
def sharpMiddleHalfspace (f : Plane →L[ℝ] ℝ) (x : Plane) : Halfspace :=
  ⟨f x + 2, f, 2 * f x + 2⟩

/-- The opposite tilt isolates a cut in the height-two slice from the height-one slice. -/
def sharpTopHalfspace (f : Plane →L[ℝ] ℝ) (x : Plane) : Halfspace :=
  ⟨-(f x + 2), f, -f x - 4⟩

lemma sharpMiddleHalfspace_cut (f : Plane →L[ℝ] ℝ) (x : Plane) :
    (sharpMiddleHalfspace f x).closedCap 1 = {y | f y ≤ f x} := by
  ext y
  simp only [sharpMiddleHalfspace, Halfspace.closedCap, mem_ofPred_eq]
  norm_num
  constructor <;> intro h <;> linarith

lemma sharpTopHalfspace_cut (f : Plane →L[ℝ] ℝ) (x : Plane) :
    (sharpTopHalfspace f x).closedCap 2 = {y | f y ≤ f x} := by
  ext y
  simp only [sharpTopHalfspace, Halfspace.closedCap, mem_ofPred_eq]
  norm_num
  constructor <;> intro h <;> linarith

lemma sharpMiddleHalfspace_misses (f : Plane →L[ℝ] ℝ) (x : Plane)
    (hf : ∀ y ∈ standardChordTriangle, (-1 : ℝ) ≤ f y) :
    standardChordTriangle ∩ (sharpMiddleHalfspace f x).closedCap 2 = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  rintro y ⟨hy, hcap⟩
  have h := hf y hy
  simp only [sharpMiddleHalfspace, Halfspace.closedCap, mem_ofPred_eq] at hcap
  norm_num at hcap
  linarith

lemma sharpTopHalfspace_misses (f : Plane →L[ℝ] ℝ) (x : Plane)
    (hf : ∀ y ∈ standardChordTriangle, (-1 : ℝ) ≤ f y) :
    standardChordTriangle ∩ (sharpTopHalfspace f x).closedCap 1 = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  rintro y ⟨hy, hcap⟩
  have h := hf y hy
  simp only [sharpTopHalfspace, Halfspace.closedCap, mem_ofPred_eq] at hcap
  norm_num at hcap
  linarith

lemma closedMass_sharpMiddleHalfspace (r : ℝ) (f : Plane →L[ℝ] ℝ) (x : Plane)
    (hf : ∀ y ∈ standardChordTriangle, (-1 : ℝ) ≤ f y)
    (hcut : area (standardChordTriangle ∩ {y | f y ≤ f x}) ≤ 2 / 9) :
    closedMass (sharpBodies r) (sharpMiddleHalfspace f x) ≤ 2 / 9 + r ^ 2 / 2 := by
  have hsmall := area_mono
    (inter_subset_left : sharpSmallTriangle r ∩
      (sharpMiddleHalfspace f x).closedCap 0 ⊆ sharpSmallTriangle r)
    (sharpSmallTriangle_isBody r).1
  rw [area_sharpSmallTriangle] at hsmall
  simp only [closedMass, Fin.sum_univ_three, sharpBodies_zero, sharpBodies_one,
    sharpBodies_two, sharpMiddleHalfspace_cut, sharpMiddleHalfspace_misses f x hf]
  simp only [area, Measure.real, measure_empty, ENNReal.toReal_zero, add_zero] at *
  linarith

lemma closedMass_sharpTopHalfspace (r : ℝ) (f : Plane →L[ℝ] ℝ) (x : Plane)
    (hf : ∀ y ∈ standardChordTriangle, (-1 : ℝ) ≤ f y)
    (hcut : area (standardChordTriangle ∩ {y | f y ≤ f x}) ≤ 2 / 9) :
    closedMass (sharpBodies r) (sharpTopHalfspace f x) ≤ 2 / 9 + r ^ 2 / 2 := by
  have hsmall := area_mono
    (inter_subset_left : sharpSmallTriangle r ∩
      (sharpTopHalfspace f x).closedCap 0 ⊆ sharpSmallTriangle r)
    (sharpSmallTriangle_isBody r).1
  rw [area_sharpSmallTriangle] at hsmall
  simp only [closedMass, Fin.sum_univ_three, sharpBodies_zero, sharpBodies_one,
    sharpBodies_two, sharpTopHalfspace_cut, sharpTopHalfspace_misses f x hf]
  simp only [area, Measure.real, measure_empty, ENNReal.toReal_zero, add_zero] at *
  linarith

/-- Each point admits a halfspace with the required small mass. -/
theorem sharpBodies_small_halfspace (r : ℝ) (i : Fin 3) (x : Plane)
    (hx : x ∈ sharpBodies r i) :
    ∃ H : Halfspace, H.Proper ∧ x ∈ H.closedCap i ∧
      closedMass (sharpBodies r) H ≤ 2 / 9 + r ^ 2 / 2 := by
  fin_cases i
  · refine ⟨sharpBottomHalfspace, Or.inl (by norm_num [sharpBottomHalfspace]),
      mem_sharpBottomHalfspace x, ?_⟩
    rw [closedMass_sharpBottomHalfspace]
    linarith
  · obtain ⟨f, hf₀, hf, hcut⟩ := standardChordTriangle_small_cut x hx
    refine ⟨sharpMiddleHalfspace f x, Or.inr hf₀, ?_,
      closedMass_sharpMiddleHalfspace r f x hf hcut⟩
    change x ∈ (sharpMiddleHalfspace f x).closedCap 1
    rw [sharpMiddleHalfspace_cut]
    exact (le_refl (f x) : f x ≤ f x)
  · obtain ⟨f, hf₀, hf, hcut⟩ := standardChordTriangle_small_cut x hx
    refine ⟨sharpTopHalfspace f x, Or.inr hf₀, ?_,
      closedMass_sharpTopHalfspace r f x hf hcut⟩
    change x ∈ (sharpTopHalfspace f x).closedCap 2
    rw [sharpTopHalfspace_cut]
    exact (le_refl (f x) : f x ≤ f x)

/-- A positive homothety factor giving depth below the proposed bound. -/
lemma sharpness_factor (c : ℝ) (hc : (2 / 9 : ℝ) < c) :
    ∃ r : ℝ, 0 < r ∧ r < 1 ∧ 2 / 9 + r ^ 2 / 2 < c := by
  let r := min (1 / 2 : ℝ) (c - 2 / 9)
  have hr : 0 < r := lt_min (by norm_num) (by linarith)
  have hr₁ : r ≤ 1 / 2 := min_le_left _ _
  have hr₂ : r ≤ c - 2 / 9 := min_le_right _ _
  refine ⟨r, hr, by linarith, ?_⟩
  have hsq : r ^ 2 ≤ r / 2 := by nlinarith
  linarith

/-- No fraction larger than two ninths is valid for all compatible triples. -/
theorem sharpness (c : ℝ) (hc : (2 / 9 : ℝ) < c) :
    ∃ A : Bodies, (∀ i, IsBody (A i)) ∧ 0 < totalArea A ∧ Compatible A ∧
      ∀ i : Fin 3, ∀ x ∈ A i, ∃ H : Halfspace,
        H.Proper ∧ x ∈ H.closedCap i ∧ closedMass A H < c * totalArea A := by
  obtain ⟨r, hr, hr₁, hbound⟩ := sharpness_factor c hc
  refine ⟨sharpBodies r, sharpBodies_isBody r, totalArea_sharpBodies_pos r,
    sharpBodies_compatible r hr.le hr₁.le, ?_⟩
  intro i x hx
  obtain ⟨H, hproper, hH, hm⟩ := sharpBodies_small_halfspace r i x hx
  refine ⟨H, hproper, hH, hm.trans_lt (hbound.trans_le ?_)⟩
  rw [totalArea_sharpBodies]
  have hc₀ : 0 < c := by linarith
  nlinarith [sq_nonneg r]

/-- The sharpness examples may also be normalized to total area one. -/
theorem sharpness_normalized (c : ℝ) (hc : (2 / 9 : ℝ) < c) :
    ∃ A : Bodies, (∀ i, IsBody (A i)) ∧ totalArea A = 1 ∧ Compatible A ∧
      ∀ i : Fin 3, ∀ x ∈ A i, ∃ H : Halfspace,
        H.Proper ∧ x ∈ H.closedCap i ∧ closedMass A H < c := by
  obtain ⟨A, hA, hpos, hcompat, hsharp⟩ := sharpness c hc
  refine ⟨areaNormalize A hpos, areaNormalize_isBody A hA hpos,
    totalArea_areaNormalize A hpos, areaNormalize_compatible A hpos hcompat, ?_⟩
  intro i y hy
  rcases hy with ⟨x, hx, rfl⟩
  obtain ⟨H, hproper, hH, hmass⟩ := hsharp i x hx
  refine ⟨H.linearImage (normalizationEquiv A hpos),
    H.linearImage_proper (normalizationEquiv A hpos) hproper,
    (H.mem_linearImage_closedCap (normalizationEquiv A hpos) i x).2 hH, ?_⟩
  rw [areaNormalize, closedMass_linearImageBodies, normalizationEquiv_areaScale]
  have h := mul_lt_mul_of_pos_left hmass (inv_pos.mpr hpos)
  simpa [← mul_assoc, mul_comm, mul_left_comm, mul_assoc, hpos.ne'] using h

end ThreeSlices
