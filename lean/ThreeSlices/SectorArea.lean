import ThreeSlices.Basic

open Set MeasureTheory

namespace ThreeSlices

/-- Cartesian coordinates preserve the Euclidean area used in this project. -/
lemma measurePreserving_coordinates :
    MeasurePreserving (fun x : Plane => (x 0, x 1)) volume volume := by
  convert (volume_preserving_finTwoArrow ℝ).comp
    (PiLp.volume_preserving_ofLp (Fin 2)) using 1
  rfl

private lemma volume_closedRegion_eq_regionBetween {f g : ℝ → ℝ} {s : Set ℝ}
    (hf : Measurable f) (hg : Measurable g) (hs : MeasurableSet s) :
    volume {p : ℝ × ℝ | p.1 ∈ s ∧ p.2 ∈ Icc (f p.1) (g p.1)} =
      volume (regionBetween f g s) := by
  change (volume : Measure ℝ).prod volume _ = (volume : Measure ℝ).prod volume _
  rw [Measure.prod_apply
    (measurableSet_region_between_cc hf hg hs),
    Measure.prod_apply (measurableSet_regionBetween hf hg hs)]
  apply lintegral_congr
  intro x
  by_cases hx : x ∈ s
  · simp only [regionBetween, preimage_ofPred_eq, hx, true_and]
    exact (Real.volume_Icc).trans Real.volume_Ioo.symm
  · simp [regionBetween, hx]

private lemma area_between_graphs_of_measurePreserving {f g : ℝ → ℝ} {a b : ℝ}
    {F : Plane → ℝ × ℝ} (hF : MeasurePreserving F volume volume)
    (hf : Continuous f) (hg : Continuous g)
    (hfg : ∀ x ∈ Icc a b, f x ≤ g x) :
    area {x : Plane | (F x).1 ∈ Icc a b ∧ (F x).2 ∈ Icc (f (F x).1) (g (F x).1)} =
      ∫ x in Icc a b, g x - f x := by
  rw [area]
  change volume.real (F ⁻¹'
    {p : ℝ × ℝ | p.1 ∈ Icc a b ∧ p.2 ∈ Icc (f p.1) (g p.1)}) = _
  rw [hF.measureReal_preimage
    (measurableSet_region_between_cc hf.measurable hg.measurable
      measurableSet_Icc).nullMeasurableSet]
  rw [measureReal_def, volume_closedRegion_eq_regionBetween
    hf.measurable hg.measurable measurableSet_Icc]
  change ((volume : Measure ℝ).prod volume (regionBetween f g (Icc a b))).toReal = _
  rw [
    volume_regionBetween_eq_integral hf.continuousOn.integrableOn_Icc
      hg.continuousOn.integrableOn_Icc measurableSet_Icc hfg]
  apply ENNReal.toReal_ofReal
  exact integral_nonneg_of_ae ((ae_restrict_iff' measurableSet_Icc).mpr
    (Filter.Eventually.of_forall fun x hx => sub_nonneg.mpr (hfg x hx)))

/-- Area by vertical integration, with both graphs and both endpoints included. -/
lemma area_between_graphs {f g : ℝ → ℝ} {a b : ℝ}
    (hf : Continuous f) (hg : Continuous g)
    (hfg : ∀ x ∈ Icc a b, f x ≤ g x) :
    area {x : Plane | x 0 ∈ Icc a b ∧ x 1 ∈ Icc (f (x 0)) (g (x 0))} =
      ∫ x in Icc a b, g x - f x :=
  area_between_graphs_of_measurePreserving measurePreserving_coordinates hf hg hfg

/-- The same formula integrating horizontal cross sections. -/
lemma area_between_graphs_swapped {f g : ℝ → ℝ} {a b : ℝ}
    (hf : Continuous f) (hg : Continuous g)
    (hfg : ∀ x ∈ Icc a b, f x ≤ g x) :
    area {x : Plane | x 1 ∈ Icc a b ∧ x 0 ∈ Icc (f (x 1)) (g (x 1))} =
      ∫ x in Icc a b, g x - f x :=
  area_between_graphs_of_measurePreserving
    (Measure.measurePreserving_swap.comp measurePreserving_coordinates) hf hg hfg

/-- The closed unit triangle has Euclidean area one half. -/
lemma area_standardTriangle :
    area {x : Plane | x 0 ∈ Icc (0 : ℝ) 1 ∧ x 1 ∈ Icc 0 (1 - x 0)} = 1 / 2 := by
  rw [area_between_graphs (f := fun _ => 0) (g := fun x => 1 - x)
    continuous_const (continuous_const.sub continuous_id)
    (by intro x hx; simpa using hx.2)]
  simp only [sub_zero]
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le zero_le_one]
  rw [intervalIntegral.integral_sub (f := fun _ : ℝ => 1) (g := fun x : ℝ => x)
    intervalIntegrable_const (continuous_id.intervalIntegrable _ _)]
  simp [integral_id]
  norm_num

/-- A triangle with horizontal base from the origin to `(p, 0)` and apex `(w, z)`. -/
lemma area_triangleRegion {p w z : ℝ} (hp : 0 ≤ p) (hz : 0 < z) :
    area {x : Plane | x 1 ∈ Icc 0 z ∧
      x 0 ∈ Icc (w / z * x 1) (p + (w - p) / z * x 1)} = p * z / 2 := by
  rw [area_between_graphs_swapped (f := fun y => w / z * y)
    (g := fun y => p + (w - p) / z * y)
    (continuous_const.mul continuous_id)
    (continuous_const.add (continuous_const.mul continuous_id)) (by
      intro y hy
      apply sub_nonneg.mp
      have h : 0 ≤ p * (1 - y / z) :=
        mul_nonneg hp (sub_nonneg.mpr ((div_le_one hz).mpr hy.2))
      convert h using 1
      ring)]
  have heq : (fun y => p + (w - p) / z * y - w / z * y) =
      fun y => p - (p / z) * y := by funext y; ring
  rw [heq, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le hz.le,
    intervalIntegral.integral_sub (f := fun _ : ℝ => p) (g := fun y : ℝ => p / z * y)
      intervalIntegrable_const
      ((continuous_const.mul continuous_id).intervalIntegrable _ _),
    intervalIntegral.integral_const, intervalIntegral.integral_const_mul, integral_id]
  simp only [sub_zero, zero_pow, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    smul_eq_mul]
  field_simp
  ring

/-- The cross sections in `area_triangleRegion` are exactly those of the convex hull. -/
lemma convexHull_triangle_eq_region {p w z : ℝ} (hp : 0 < p) (hz : 0 < z) :
    convexHull ℝ ({0, WithLp.toLp 2 ![p, 0], WithLp.toLp 2 ![w, z]} : Set Plane) =
      {x : Plane | x 1 ∈ Icc 0 z ∧
        x 0 ∈ Icc (w / z * x 1) (p + (w - p) / z * x 1)} := by
  let R : Set Plane := {x | x 1 ∈ Icc 0 z ∧
    x 0 ∈ Icc (w / z * x 1) (p + (w - p) / z * x 1)}
  have hR : Convex ℝ R := by
    intro x hx y hy a b ha hb hab
    change (a • x + b • y) 1 ∈ Icc 0 z ∧
      (a • x + b • y) 0 ∈ Icc (w / z * (a • x + b • y) 1)
        (p + (w - p) / z * (a • x + b • y) 1)
    simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, mem_Icc]
    constructor
    · constructor
      · exact add_nonneg (mul_nonneg ha hx.1.1) (mul_nonneg hb hy.1.1)
      · have h := add_le_add (mul_le_mul_of_nonneg_left hx.1.2 ha)
            (mul_le_mul_of_nonneg_left hy.1.2 hb)
        calc a * x 1 + b * y 1 ≤ a * z + b * z := h
          _ = z := by rw [← add_mul, hab, one_mul]
    · constructor
      · calc
          w / z * (a * x 1 + b * y 1) =
              a * (w / z * x 1) + b * (w / z * y 1) := by ring
          _ ≤ a * x 0 + b * y 0 := add_le_add
            (mul_le_mul_of_nonneg_left hx.2.1 ha) (mul_le_mul_of_nonneg_left hy.2.1 hb)
      · calc
          a * x 0 + b * y 0 ≤
              a * (p + (w - p) / z * x 1) + b * (p + (w - p) / z * y 1) :=
            add_le_add (mul_le_mul_of_nonneg_left hx.2.2 ha)
              (mul_le_mul_of_nonneg_left hy.2.2 hb)
          _ = (a + b) * p + (w - p) / z * (a * x 1 + b * y 1) := by ring
          _ = p + (w - p) / z * (a * x 1 + b * y 1) := by rw [hab, one_mul]
  apply Subset.antisymm
  · apply convexHull_min ?_ hR
    intro x hx
    rcases hx with rfl | rfl | rfl
    · simp [R, hz.le, hp.le]
    · simp [R, hz.le, hp.le]
    · simp [R, hz.le, hz.ne']
  · intro x hx
    have hy0 : 0 ≤ x 1 / z := div_nonneg hx.1.1 hz.le
    have hx0 : 0 ≤ (x 0 - w / z * x 1) / p :=
      div_nonneg (sub_nonneg.mpr hx.2.1) hp.le
    have hsum : (x 0 - w / z * x 1) / p + x 1 / z ≤ 1 := by
      apply le_sub_iff_add_le.mp
      apply (div_le_iff₀ hp).mpr
      calc x 0 - w / z * x 1 ≤ (p + (w - p) / z * x 1) - w / z * x 1 :=
          sub_le_sub_right hx.2.2 _
        _ = (1 - x 1 / z) * p := by ring
    apply mem_convexHull_of_exists_fintype
      ![1 - (x 0 - w / z * x 1) / p - x 1 / z,
        (x 0 - w / z * x 1) / p, x 1 / z]
      ![0, WithLp.toLp 2 ![p, 0], WithLp.toLp 2 ![w, z]]
    · intro i
      fin_cases i
      · change 0 ≤ 1 - (x 0 - w / z * x 1) / p - x 1 / z
        linarith
      · exact hx0
      · exact hy0
    · simp only [Fin.sum_univ_succ, Matrix.cons_val_zero, Matrix.cons_val_succ,
        Fin.sum_univ_zero, add_zero]
      ring
    · intro i
      fin_cases i <;> simp
    · ext i
      fin_cases i <;> simp [Fin.sum_univ_succ]
      · field_simp
        ring
      · field_simp

lemma area_convexHull_triangle {p w z : ℝ} (hp : 0 < p) (hz : 0 < z) :
    area (convexHull ℝ ({0, WithLp.toLp 2 ![p, 0], WithLp.toLp 2 ![w, z]} : Set Plane)) =
      p * z / 2 := by
  rw [convexHull_triangle_eq_region hp hz, area_triangleRegion hp.le hz]

end ThreeSlices
