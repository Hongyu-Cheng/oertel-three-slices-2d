import ThreeSlices.Basic
import LeanPool.Isoperimetric.BrunnMinkowski

open Set MeasureTheory
open scoped Pointwise

namespace ThreeSlices

/-- The scalar contradiction in Section 3, with w representing sqrt (u * v). -/
theorem final_contradiction (u v σ τ w : ℝ)
    (hu : u ≤ 1 / 2) (hv : v ≤ 1 / 2)
    (hw : 0 ≤ w) (hw_sq : w ^ 2 = u * v)
    (hτ : (9 / 2 : ℝ) * σ ^ 2 ≤ τ)
    (hmass : (5 / 9 : ℝ) + τ - σ < u + v)
    (hbm : u + v + 2 * w ≤ 4 * σ) : False := by
  have hsum : (1 / 2 : ℝ) + (9 / 2 : ℝ) * (σ - 1 / 9) ^ 2 < u + v := by
    nlinarith
  have hp : 0 ≤ (1 - 2 * u) * (1 - 2 * v) :=
    mul_nonneg (by linarith) (by linarith)
  have hprod : 9 * (σ - 1 / 9) ^ 2 < 4 * w ^ 2 := by
    nlinarith
  have hlin : 3 * σ - 1 / 3 < 2 * w :=
    lt_of_pow_lt_pow_left₀ 2 (by positivity) (by nlinarith)
  nlinarith [sq_nonneg (σ - 2 / 9)]

theorem final_contradiction_sqrt (u v σ τ : ℝ)
    (hu₀ : 0 ≤ u) (hv₀ : 0 ≤ v) (hσ : 0 ≤ σ)
    (hu : u ≤ 1 / 2) (hv : v ≤ 1 / 2)
    (hτ : (9 / 2 : ℝ) * σ ^ 2 ≤ τ)
    (hmass : (5 / 9 : ℝ) + τ - σ < u + v)
    (hbm : Real.sqrt u + Real.sqrt v ≤ 2 * Real.sqrt σ) : False := by
  have hsq := mul_self_le_mul_self
    (add_nonneg (Real.sqrt_nonneg u) (Real.sqrt_nonneg v)) hbm
  refine final_contradiction u v σ τ (Real.sqrt u * Real.sqrt v) hu hv
    (mul_nonneg (Real.sqrt_nonneg u) (Real.sqrt_nonneg v)) ?_ hτ hmass ?_
  · rw [mul_pow, Real.sq_sqrt hu₀, Real.sq_sqrt hv₀]
  · nlinarith [Real.sq_sqrt hu₀, Real.sq_sqrt hv₀, Real.sq_sqrt hσ]

/-- Planar midpoint Brunn–Minkowski for compact nonempty outer sets. -/
theorem planar_midpoint_area {K₀ K₁ K₂ : Set Plane}
    (hK₀ : IsCompact K₀) (hK₁ : IsCompact K₁) (hK₂ : IsCompact K₂)
    (hne₀ : K₀.Nonempty) (hne₂ : K₂.Nonempty)
    (hmid : (1 / 2 : ℝ) • K₀ + (1 / 2 : ℝ) • K₂ ⊆ K₁) :
    Real.sqrt (volume.real K₀) + Real.sqrt (volume.real K₂) ≤
      2 * Real.sqrt (volume.real K₁) := by
  have hsum : K₀ + K₂ ⊆ (2 : ℝ) • K₁ := by
    calc
      K₀ + K₂ = (2 : ℝ) • ((1 / 2 : ℝ) • K₀ + (1 / 2 : ℝ) • K₂) := by
        simp [smul_add, smul_smul]
      _ ⊆ (2 : ℝ) • K₁ := smul_set_mono hmid
  have hbm := brunn_minkowski_euclideanSpace (d := 1)
    hne₀ hK₀.measurableSet hne₂ hK₂.measurableSet (hK₀.add hK₂).measurableSet
  simp only [Nat.cast_one] at hbm
  have hfin (K : Set Plane) (hK : IsCompact K) :
      (volume K) ^ ((1 : ℝ) + 1)⁻¹ ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_nonneg (by norm_num) hK.measure_ne_top
  have h := ENNReal.toReal_mono (hfin _ (hK₀.add hK₂)) hbm
  rw [ENNReal.toReal_add (hfin _ hK₀) (hfin _ hK₂)] at h
  simp only [← ENNReal.toReal_rpow, show ((1 : ℝ) + 1)⁻¹ = 1 / 2 by norm_num,
    ← Real.sqrt_eq_rpow] at h
  have hm := measureReal_mono (μ := (volume : Measure Plane)) hsum
    (hK₁.smul (2 : ℝ)).measure_ne_top
  have hscale : volume.real ((2 : ℝ) • K₁) = 4 * volume.real K₁ := by
    norm_num [Measure.real, Measure.addHaar_smul, ENNReal.toReal_mul]
  rw [hscale] at hm
  calc
    _ ≤ Real.sqrt (volume.real (K₀ + K₂)) := h
    _ ≤ Real.sqrt (4 * volume.real K₁) := Real.sqrt_le_sqrt hm
    _ = _ := by rw [Real.sqrt_mul (by norm_num)]; norm_num

end ThreeSlices
