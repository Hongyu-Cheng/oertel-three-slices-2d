import ThreeSlices.TsintsifasGeometry
import ThreeSlices.TsintsifasAlgebra
import ThreeSlices.SectorArea

open Set MeasureTheory

namespace ThreeSlices

private lemma horizontal_radial_bound {K : Set Plane} (hK : Convex ℝ K)
    {P W x : Plane} (hP : IsRadialEndpoint K P) (hW : W ∈ K)
    (hP₀ : P 0 ≠ 0) (hP₁ : P 1 = 0) (hW₁ : 0 < W 1)
    (hW₀ : 0 ≤ P 0 * (W 0 - P 0)) (hx : x ∈ K) (hx₁ : x 1 ≤ 0) :
    P 0 * (x 0 - P 0) ≤ 0 := by
  let a := x 1 / W 1
  let b := (x 0 - a * W 0) / P 0
  have ha : a ≤ 0 := div_nonpos_of_nonpos_of_nonneg hx₁ hW₁.le
  have hb : b * P 0 = x 0 - a * W 0 := div_mul_cancel₀ _ hP₀
  have he : a • W + b • P = x := by
    apply PiLp.ext
    intro i
    fin_cases i <;> simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
    · change a * W 0 + b * P 0 = x 0
      linarith only [hb]
    · change a * W 1 + b * P 1 = x 1
      rw [hP₁, mul_zero, add_zero]
      exact div_mul_cancel₀ _ hW₁.ne'
  by_contra h
  have hpos : 0 < P 0 * (x 0 - P 0) := lt_of_not_ge h
  have hnonneg := mul_nonneg (neg_nonneg.mpr ha) hW₀
  have hid : (P 0) ^ 2 * (a + b - 1) =
      P 0 * (x 0 - P 0) - a * (P 0 * (W 0 - P 0)) := by
    nlinarith only [congrArg (fun r : ℝ => P 0 * r) hb]
  have hab : 1 < a + b := by
    have hm : 0 < (P 0) ^ 2 * (a + b - 1) := by rw [hid]; linarith
    have := (mul_pos_iff_of_pos_left (sq_pos_iff.mpr hP₀)).mp hm
    linarith
  have hapos := coefficient_pos_of_radialEndpoint hK hW hP (by rwa [he]) hab
  linarith

/-- Outward upper points force the body's lower half into the endpoint strip. -/
theorem lower_halfplane_strip {K : Set Plane} (hK : Convex ℝ K)
    {P Q U W : Plane} {p q : ℝ} (hp : 0 < p) (hq : 0 < q)
    (hP : IsRadialEndpoint K P) (hQ : IsRadialEndpoint K Q)
    (hU : U ∈ K) (hW : W ∈ K)
    (hP₀ : P 0 = p) (hP₁ : P 1 = 0) (hQ₀ : Q 0 = -q) (hQ₁ : Q 1 = 0)
    (hU₁ : 0 < U 1) (hW₁ : 0 < W 1) (hU₀ : U 0 ≤ -q) (hW₀ : p ≤ W 0) :
    K ∩ {x : Plane | x 1 ≤ 0} ⊆ {x : Plane | -q ≤ x 0 ∧ x 0 ≤ p} := by
  intro x hx
  have hright := horizontal_radial_bound hK hP hW
    (by rw [hP₀]; exact hp.ne') hP₁ hW₁
    (by rw [hP₀]; exact mul_nonneg hp.le (sub_nonneg.mpr hW₀)) hx.1 hx.2
  have hleft := horizontal_radial_bound hK hQ hU
    (by rw [hQ₀]; exact neg_ne_zero.mpr hq.ne') hQ₁ hU₁
    (by rw [hQ₀]; exact mul_nonneg_of_nonpos_of_nonpos (by linarith) (by linarith))
    hx.1 hx.2
  rw [hP₀] at hright
  rw [hQ₀] at hleft
  constructor <;> nlinarith

/-- The right numerator sector bounded by the horizontal ray and `(w,z)`. -/
def stripNumeratorRight (w z : ℝ) : Set Plane :=
  {x | 0 ≤ x 0 ∧ 0 ≤ x 1 ∧ w * x 1 ≤ z * x 0}

/-- The left numerator sector bounded by `(-u,v)` and the horizontal ray. -/
def stripNumeratorLeft (u v : ℝ) : Set Plane :=
  {x | x 0 ≤ 0 ∧ 0 ≤ x 1 ∧ u * x 1 ≤ -v * x 0}

/-- The negative of the right numerator sector. -/
def stripDenominatorLeft (w z : ℝ) : Set Plane :=
  {x | x 0 ≤ 0 ∧ x 1 ≤ 0 ∧ z * x 0 ≤ w * x 1}

/-- The negative of the left numerator sector. -/
def stripDenominatorRight (u v : ℝ) : Set Plane :=
  {x | 0 ≤ x 0 ∧ x 1 ≤ 0 ∧ -v * x 0 ≤ u * x 1}

private lemma lower_left_wedge_area {q z w : ℝ} (hq : 0 < q)
    (hz : 0 < z) (hw : 0 < w) :
    area {x : Plane | x 0 ∈ Icc (-q) 0 ∧ x 1 ∈ Icc (z / w * x 0) 0} =
      q ^ 2 * z / (2 * w) := by
  rw [area_between_graphs (f := fun x => z / w * x) (g := fun _ => 0)
    (continuous_const.mul continuous_id) continuous_const
    (by intro x hx; exact mul_nonpos_of_nonneg_of_nonpos (div_nonneg hz.le hw.le) hx.2)]
  have he : (fun x : ℝ => 0 - z / w * x) = fun x => -(z / w) * x := by
    funext x
    ring
  rw [he, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by linarith : -q ≤ 0),
    intervalIntegral.integral_const_mul, integral_id]
  ring

private lemma lower_right_wedge_area {p v u : ℝ} (hp : 0 < p)
    (hv : 0 < v) (hu : 0 < u) :
    area {x : Plane | x 0 ∈ Icc 0 p ∧ x 1 ∈ Icc (-(v / u) * x 0) 0} =
      p ^ 2 * v / (2 * u) := by
  rw [area_between_graphs (f := fun x => -(v / u) * x) (g := fun _ => 0)
    (continuous_const.mul continuous_id) continuous_const
    (by
      intro x hx
      exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (div_nonneg hv.le hu.le)) hx.1)]
  have he : (fun x : ℝ => 0 - -(v / u) * x) = fun x => v / u * x := by
    funext x
    ring
  rw [he, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le hp.le,
    intervalIntegral.integral_const_mul, integral_id]
  ring

private lemma left_triangle_region_area {q u v : ℝ} (hq : 0 < q) (hv : 0 < v) :
    area {x : Plane | x 1 ∈ Icc 0 v ∧
      x 0 ∈ Icc (-q + (q - u) / v * x 1) (-(u / v) * x 1)} = q * v / 2 := by
  rw [area_between_graphs_swapped (f := fun y => -q + (q - u) / v * y)
    (g := fun y => -(u / v) * y)
    (continuous_const.add (continuous_const.mul continuous_id))
    (continuous_const.mul continuous_id) (by
      intro y hy
      have h := mul_le_mul_of_nonneg_left hy.2 (div_nonneg hq.le hv.le)
      have he : q / v * v = q := div_mul_cancel₀ _ hv.ne'
      have he' : (q - u) / v * y = q / v * y - u / v * y := by ring
      rw [he']
      linarith)]
  have he : (fun y : ℝ => -(u / v) * y - (-q + (q - u) / v * y)) =
      fun y => q - (q / v) * y := by funext y; ring
  rw [he, integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hv.le,
    intervalIntegral.integral_sub (f := fun _ : ℝ => q) (g := fun y => q / v * y)
      intervalIntegrable_const
      ((continuous_const.mul continuous_id).intervalIntegrable _ _),
    intervalIntegral.integral_const, intervalIntegral.integral_const_mul, integral_id]
  simp only [sub_zero, zero_pow, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    smul_eq_mul]
  field_simp
  ring

private lemma measure_ne_top_of_area_pos {S : Set Plane} (hS : 0 < area S) :
    volume S ≠ ⊤ := by
  intro h
  simp [area, Measure.real, h] at hS

/-- Body sectors are bounded by two endpoint triangles and strip wedges. -/
theorem strip_sector_area_bounds {K : Set Plane} (hK : IsBody K)
    (hzero : (0 : Plane) ∈ K) {p q u v w z : ℝ}
    (hp : 0 < p) (hq : 0 < q) (hu : 0 < u) (hv : 0 < v) (hw : 0 < w) (hz : 0 < z)
    (hqu : q ≤ u) (hpw : p ≤ w)
    (hP : IsRadialEndpoint K (WithLp.toLp 2 ![p, 0]))
    (hQ : IsRadialEndpoint K (WithLp.toLp 2 ![-q, 0]))
    (hU : WithLp.toLp 2 ![-u, v] ∈ K) (hW : WithLp.toLp 2 ![w, z] ∈ K) :
    p * z / 2 ≤ area (K ∩ stripNumeratorRight w z) ∧
      q * v / 2 ≤ area (K ∩ stripNumeratorLeft u v) ∧
      area (K ∩ stripDenominatorLeft w z) ≤ q ^ 2 * z / (2 * w) ∧
      area (K ∩ stripDenominatorRight u v) ≤ p ^ 2 * v / (2 * u) := by
  have hstrip := lower_halfplane_strip hK.2.1 hp hq hP hQ hU hW
    rfl rfl rfl rfl hv hz (by change -u ≤ -q; linarith) hpw
  have hnright : p * z / 2 ≤ area (K ∩ stripNumeratorRight w z) := by
    let T := convexHull ℝ ({0, WithLp.toLp 2 ![p, 0], WithLp.toLp 2 ![w, z]} : Set Plane)
    have hTK : T ⊆ K := convexHull_min (by
      intro x hx
      rcases hx with rfl | rfl | rfl
      · exact hzero
      · exact hP.1
      · exact hW) hK.2.1
    have hsub : T ⊆ K ∩ stripNumeratorRight w z := by
      intro x hx
      refine ⟨hTK hx, ?_⟩
      dsimp only [T] at hx
      rw [convexHull_triangle_eq_region hp hz] at hx
      refine ⟨?_, hx.1.1, ?_⟩
      · have := mul_nonneg (div_nonneg hw.le hz.le) hx.1.1
        linarith [hx.2.1]
      · have h := mul_le_mul_of_nonneg_left hx.2.1 hz.le
        have he : z * (w / z * x 1) = w * x 1 := by field_simp
        rw [he] at h
        simpa only [mul_comm] using h
    have hm : area T ≤ area (K ∩ stripNumeratorRight w z) :=
      measureReal_mono hsub (measure_ne_top_of_subset inter_subset_left
        (hK.1.measure_ne_top (μ := volume)))
    rwa [show area T = p * z / 2 from area_convexHull_triangle hp hz] at hm
  have hnleft : q * v / 2 ≤ area (K ∩ stripNumeratorLeft u v) := by
    let T : Set Plane := {x | x 1 ∈ Icc 0 v ∧
      x 0 ∈ Icc (-q + (q - u) / v * x 1) (-(u / v) * x 1)}
    have hsub : T ⊆ K ∩ stripNumeratorLeft u v := by
      intro x hx
      let a := x 1 / v
      let b := (-x 0 - u / v * x 1) / q
      have ha : 0 ≤ a := div_nonneg hx.1.1 hv.le
      have hb : 0 ≤ b := div_nonneg (by linarith [hx.2.2]) hq.le
      have hbq : b * q = -x 0 - u / v * x 1 := div_mul_cancel₀ _ hq.ne'
      have hlow := hx.2.1
      have he : (q - u) / v * x 1 = q * a - u / v * x 1 := by dsimp [a]; ring
      rw [he] at hlow
      have hab : a + b ≤ 1 := by nlinarith [hlow, hbq]
      have heq : a • WithLp.toLp 2 ![-u, v] + b • WithLp.toLp 2 ![-q, 0] = x := by
        apply PiLp.ext
        intro i
        fin_cases i <;> simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
        · change a * -u + b * -q = x 0
          dsimp [a, b]
          field_simp
          ring
        · change a * v + b * 0 = x 1
          rw [mul_zero, add_zero]
          exact div_mul_cancel₀ _ hv.ne'
      refine ⟨?_, ?_, hx.1.1, ?_⟩
      · rw [← heq]
        exact endpoint_triangle_mem hK.2.1 hzero hU hQ.1 ha hb hab
      · have := mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (div_nonneg hu.le hv.le)) hx.1.1
        linarith [hx.2.2]
      · have h := mul_le_mul_of_nonneg_left hx.2.2 hv.le
        have he : v * (-(u / v) * x 1) = -u * x 1 := by field_simp
        rw [he] at h
        linarith
    have hm : area T ≤ area (K ∩ stripNumeratorLeft u v) :=
      measureReal_mono hsub (measure_ne_top_of_subset inter_subset_left
        (hK.1.measure_ne_top (μ := volume)))
    rwa [show area T = q * v / 2 from left_triangle_region_area hq hv] at hm
  have hdleft : area (K ∩ stripDenominatorLeft w z) ≤ q ^ 2 * z / (2 * w) := by
    let R : Set Plane := {x | x 0 ∈ Icc (-q) 0 ∧ x 1 ∈ Icc (z / w * x 0) 0}
    have hR : area R = q ^ 2 * z / (2 * w) := lower_left_wedge_area hq hz hw
    have hsub : K ∩ stripDenominatorLeft w z ⊆ R := by
      intro x hx
      have hs := hstrip ⟨hx.1, hx.2.2.1⟩
      refine ⟨⟨hs.1, hx.2.1⟩, ?_, hx.2.2.1⟩
      rw [div_mul_eq_mul_div]
      exact (div_le_iff₀ hw).2 (by simpa only [mul_comm] using hx.2.2.2)
    have hm : area (K ∩ stripDenominatorLeft w z) ≤ area R :=
      measureReal_mono hsub (measure_ne_top_of_area_pos (by rw [hR]; positivity))
    rwa [hR] at hm
  have hdright : area (K ∩ stripDenominatorRight u v) ≤ p ^ 2 * v / (2 * u) := by
    let R : Set Plane := {x | x 0 ∈ Icc 0 p ∧ x 1 ∈ Icc (-(v / u) * x 0) 0}
    have hR : area R = p ^ 2 * v / (2 * u) := lower_right_wedge_area hp hv hu
    have hsub : K ∩ stripDenominatorRight u v ⊆ R := by
      intro x hx
      have hs := hstrip ⟨hx.1, hx.2.2.1⟩
      refine ⟨⟨hx.2.1, hs.2⟩, ?_, hx.2.2.1⟩
      rw [← neg_div, div_mul_eq_mul_div]
      exact (div_le_iff₀ hu).2 (by simpa only [neg_mul, mul_comm] using hx.2.2.2)
    have hm : area (K ∩ stripDenominatorRight u v) ≤ area R :=
      measureReal_mono hsub (measure_ne_top_of_area_pos (by rw [hR]; positivity))
    rwa [hR] at hm
  exact ⟨hnright, hnleft, hdleft, hdright⟩

/-- The unbounded configuration satisfies Tsintsifas's two-ratio product and sum bounds. -/
theorem strip_sector_area_ratios {K : Set Plane} (hK : IsBody K)
    (hzero : (0 : Plane) ∈ K) {p q u v w z : ℝ}
    (hp : 0 < p) (hq : 0 < q) (hu : 0 < u) (hv : 0 < v) (hw : 0 < w) (hz : 0 < z)
    (hqu : q ≤ u) (hpw : p ≤ w)
    (hP : IsRadialEndpoint K (WithLp.toLp 2 ![p, 0]))
    (hQ : IsRadialEndpoint K (WithLp.toLp 2 ![-q, 0]))
    (hU : WithLp.toLp 2 ![-u, v] ∈ K) (hW : WithLp.toLp 2 ![w, z] ∈ K)
    (hdleft : 0 < area (K ∩ stripDenominatorLeft w z))
    (hdright : 0 < area (K ∩ stripDenominatorRight u v)) :
    1 ≤ (area (K ∩ stripNumeratorRight w z) / area (K ∩ stripDenominatorLeft w z)) *
        (area (K ∩ stripNumeratorLeft u v) / area (K ∩ stripDenominatorRight u v)) ∧
      2 ≤ area (K ∩ stripNumeratorRight w z) / area (K ∩ stripDenominatorLeft w z) +
        area (K ∩ stripNumeratorLeft u v) / area (K ∩ stripDenominatorRight u v) := by
  obtain ⟨hnright, hnleft, hbleft, hbright⟩ :=
    strip_sector_area_bounds hK hzero hp hq hu hv hw hz hqu hpw hP hQ hU hW
  let N := area (K ∩ stripNumeratorRight w z)
  let M := area (K ∩ stripNumeratorLeft u v)
  let D := area (K ∩ stripDenominatorLeft w z)
  let E := area (K ∩ stripDenominatorRight u v)
  let r := N / D
  let s := M / E
  have hr : 0 ≤ r := div_nonneg (area_nonneg _) hdleft.le
  have hs : 0 ≤ s := div_nonneg (area_nonneg _) hdright.le
  have hrbound : p * w / q ^ 2 ≤ r := by
    apply (div_le_div_iff₀ (sq_pos_of_pos hq) hdleft).2
    have h₁ := (le_div_iff₀ (by positivity : 0 < 2 * w)).mp hbleft
    have h₂ := (div_le_iff₀ (by norm_num : (0 : ℝ) < 2)).mp hnright
    have h₃ := mul_le_mul_of_nonneg_left h₁ hp.le
    have h₄ := mul_le_mul_of_nonneg_right h₂ (sq_nonneg q)
    nlinarith only [h₃, h₄]
  have hsbound : q * u / p ^ 2 ≤ s := by
    apply (div_le_div_iff₀ (sq_pos_of_pos hp) hdright).2
    have h₁ := (le_div_iff₀ (by positivity : 0 < 2 * u)).mp hbright
    have h₂ := (div_le_iff₀ (by norm_num : (0 : ℝ) < 2)).mp hnleft
    have h₃ := mul_le_mul_of_nonneg_left h₁ hq.le
    have h₄ := mul_le_mul_of_nonneg_right h₂ (sq_nonneg p)
    nlinarith only [h₃, h₄]
  have hbase : 1 ≤ (p * w / q ^ 2) * (q * u / p ^ 2) := by
    rw [← mul_div_mul_comm]
    apply (le_div_iff₀ (mul_pos (sq_pos_of_pos hq) (sq_pos_of_pos hp))).2
    have h := mul_le_mul hpw hqu hq.le hw.le
    have hm := mul_le_mul_of_nonneg_left h (mul_nonneg hp.le hq.le)
    nlinarith only [hm]
  have hprod : 1 ≤ r * s := hbase.trans
    (mul_le_mul hrbound hsbound (by positivity) hr)
  refine ⟨hprod, ?_⟩
  simpa only [add_zero] using tsintsifas_unbounded r s 0 hr hs (by norm_num) hprod

end ThreeSlices
