import ThreeSlices.TriangleSectorFormulas

open Set MeasureTheory

namespace ThreeSlices

lemma isBody_standardChordTriangle : IsBody standardChordTriangle := by
  have hT : standardChordTriangle =
      convexHull ℝ ({0, WithLp.toLp 2 ![1, 0], WithLp.toLp 2 ![0, 1]} : Set Plane) := by
    rw [convexHull_triangle_eq_region (by norm_num : (0 : ℝ) < 1)
      (by norm_num : (0 : ℝ) < 1)]
    ext q
    simp [standardChordTriangle]
    constructor
    · rintro ⟨h₀, h₁, h₂⟩
      exact ⟨⟨h₁, by linarith⟩, h₀, by linarith⟩
    · rintro ⟨⟨h₁, _⟩, h₀, h₂⟩
      exact ⟨h₀, h₁, by linarith⟩
  rw [hT]
  exact ⟨(toFinite _).isCompact_convexHull ℝ, convex_convexHull ℝ _,
    ⟨0, subset_convexHull ℝ _ (by simp)⟩⟩

lemma triangleBarycentric_mem_Icc {x : Plane} (hx : x ∈ standardChordTriangle)
    (k : Fin 3) : triangleBarycentric x k ∈ Icc (0 : ℝ) 1 := by
  fin_cases k <;> simp [triangleBarycentric] <;>
    constructor <;> linarith [hx.1, hx.2.1, hx.2.2]

lemma triangleBarycentric_exists_ge_third (x : Plane) :
    ∃ k : Fin 3, (1 / 3 : ℝ) ≤ triangleBarycentric x k := by
  by_cases h₀ : (1 / 3 : ℝ) ≤ triangleBarycentric x 0
  · exact ⟨0, h₀⟩
  by_cases h₁ : (1 / 3 : ℝ) ≤ triangleBarycentric x 1
  · exact ⟨1, h₁⟩
  refine ⟨2, ?_⟩
  simp [triangleBarycentric] at *
  linarith

private lemma integral_triangle_width {a b : ℝ} (hab : a ≤ b) :
    (∫ s in Icc a b, b - s) = (b - a) ^ 2 / 2 := by
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab,
    intervalIntegral.integral_sub (f := fun _ : ℝ => b) (g := fun s : ℝ => s)
      intervalIntegrable_const (continuous_id.intervalIntegrable _ _),
    intervalIntegral.integral_const, integral_id]
  simp only [smul_eq_mul]
  ring

private lemma area_triangle_corner {a b : ℝ} (hab : a ≤ b) :
    area {q : Plane | q 0 ∈ Icc a b ∧ q 1 ∈ Icc 0 (b - q 0)} =
      (b - a) ^ 2 / 2 := by
  rw [area_between_graphs (f := fun _ => 0) (g := fun s => b - s)
    continuous_const (continuous_const.sub continuous_id)
    (by intro s hs; linarith [hs.2])]
  simpa only [sub_zero] using integral_triangle_width hab

private lemma area_triangle_corner_swapped {a b : ℝ} (hab : a ≤ b) :
    area {q : Plane | q 1 ∈ Icc a b ∧ q 0 ∈ Icc 0 (b - q 1)} =
      (b - a) ^ 2 / 2 := by
  rw [area_between_graphs_swapped (f := fun _ => 0) (g := fun s => b - s)
    continuous_const (continuous_const.sub continuous_id)
    (by intro s hs; linarith [hs.2])]
  simpa only [sub_zero] using integral_triangle_width hab

/-- The quadratic area formula for a barycentric cap of the unit triangle. -/
theorem area_standardChordTriangle_barycentric_cut (k : Fin 3) {a : ℝ}
    (ha : a ∈ Icc (0 : ℝ) 1) :
    area (standardChordTriangle ∩ {q | a ≤ triangleBarycentric q k}) =
      (1 - a) ^ 2 / 2 := by
  fin_cases k
  · change area (standardChordTriangle ∩ {q | a ≤ triangleBarycentric q 0}) = _
    have he : standardChordTriangle ∩ {q | a ≤ triangleBarycentric q 0} =
        {q : Plane | q 0 ∈ Icc 0 (1 - a) ∧ q 1 ∈ Icc 0 (1 - a - q 0)} := by
      ext q
      simp only [standardChordTriangle, mem_inter_iff, mem_ofPred_eq,
        triangleBarycentric, Matrix.cons_val_zero, mem_Icc]
      constructor
      · rintro ⟨⟨h₀, h₁, _⟩, hc⟩
        exact ⟨⟨h₀, by linarith⟩, h₁, by linarith⟩
      · rintro ⟨⟨h₀, _⟩, h₁, hc⟩
        exact ⟨⟨h₀, h₁, by linarith [ha.1]⟩, by linarith⟩
    rw [he, area_triangle_corner (by linarith [ha.2] : 0 ≤ 1 - a), sub_zero]
  · change area (standardChordTriangle ∩ {q | a ≤ triangleBarycentric q 1}) = _
    have he : standardChordTriangle ∩ {q | a ≤ triangleBarycentric q 1} =
        {q : Plane | q 0 ∈ Icc a 1 ∧ q 1 ∈ Icc 0 (1 - q 0)} := by
      ext q
      simp only [standardChordTriangle, mem_inter_iff, mem_ofPred_eq,
        triangleBarycentric, Matrix.cons_val_one, mem_Icc]
      constructor
      · rintro ⟨⟨_, h₁, hs⟩, hc⟩
        exact ⟨⟨hc, by linarith⟩, h₁, by linarith⟩
      · rintro ⟨⟨hc, _⟩, h₁, hs⟩
        exact ⟨⟨ha.1.trans hc, h₁, by linarith⟩, hc⟩
    rw [he, area_triangle_corner ha.2]
  · change area (standardChordTriangle ∩ {q | a ≤ triangleBarycentric q 2}) = _
    have he : standardChordTriangle ∩ {q | a ≤ triangleBarycentric q 2} =
        {q : Plane | q 1 ∈ Icc a 1 ∧ q 0 ∈ Icc 0 (1 - q 1)} := by
      ext q
      simp only [standardChordTriangle, mem_inter_iff, mem_ofPred_eq,
        triangleBarycentric, Matrix.cons_val_two, mem_Icc]
      constructor
      · rintro ⟨⟨h₀, _, hs⟩, hc⟩
        exact ⟨⟨hc, by linarith⟩, h₀, by linarith⟩
      · rintro ⟨⟨hc, _⟩, h₀, hs⟩
        exact ⟨⟨h₀, ha.1.trans hc, by linarith⟩, hc⟩
    rw [he, area_triangle_corner_swapped ha.2]

noncomputable def triangleCutNormal (k : Fin 3) : Plane →L[ℝ] ℝ :=
  ![EuclideanSpace.proj 0 + EuclideanSpace.proj 1,
    -EuclideanSpace.proj 0, -EuclideanSpace.proj 1] k

def triangleCutOffset (k : Fin 3) : ℝ := ![1, 0, 0] k

lemma triangleBarycentric_eq_offset_sub_normal (x : Plane) (k : Fin 3) :
    triangleBarycentric x k = triangleCutOffset k - triangleCutNormal k x := by
  fin_cases k <;> simp [triangleBarycentric, triangleCutOffset, triangleCutNormal]
  ring

lemma triangleCutNormal_ne_zero (k : Fin 3) : triangleCutNormal k ≠ 0 := by
  intro h
  fin_cases k
  · have he := congrArg (fun f : Plane →L[ℝ] ℝ => f (WithLp.toLp 2 ![1, 0])) h
    norm_num [triangleCutNormal] at he
  · have he := congrArg (fun f : Plane →L[ℝ] ℝ => f (WithLp.toLp 2 ![1, 0])) h
    norm_num [triangleCutNormal] at he
  · have he := congrArg (fun f : Plane →L[ℝ] ℝ => f (WithLp.toLp 2 ![0, 1])) h
    norm_num [triangleCutNormal] at he

lemma triangleCutNormal_lower_bound {y : Plane} (hy : y ∈ standardChordTriangle)
    (k : Fin 3) : (-1 : ℝ) ≤ triangleCutNormal k y := by
  fin_cases k <;> simp [triangleCutNormal] <;>
    linarith [hy.1, hy.2.1, hy.2.2]

lemma triangleCutNormal_cut_eq (x : Plane) (k : Fin 3) :
    {y | triangleCutNormal k y ≤ triangleCutNormal k x} =
      {y | triangleBarycentric x k ≤ triangleBarycentric y k} := by
  ext y
  simp only [mem_ofPred_eq, triangleBarycentric_eq_offset_sub_normal]
  constructor <;> intro h <;> linarith

/-- Every point admits a closed halfplane cut containing at most four ninths of the triangle. -/
theorem standardChordTriangle_small_cut (x : Plane) (hx : x ∈ standardChordTriangle) :
    ∃ f : Plane →L[ℝ] ℝ, f ≠ 0 ∧
      (∀ y ∈ standardChordTriangle, (-1 : ℝ) ≤ f y) ∧
      area (standardChordTriangle ∩ {y | f y ≤ f x}) ≤ 2 / 9 := by
  obtain ⟨k, hk⟩ := triangleBarycentric_exists_ge_third x
  refine ⟨triangleCutNormal k, triangleCutNormal_ne_zero k,
    fun y hy => triangleCutNormal_lower_bound hy k, ?_⟩
  rw [triangleCutNormal_cut_eq, area_standardChordTriangle_barycentric_cut k
    (triangleBarycentric_mem_Icc hx k)]
  have ha := triangleBarycentric_mem_Icc hx k
  nlinarith [mul_nonneg (sub_nonneg.mpr ha.2) (sub_nonneg.mpr hk)]

end ThreeSlices
