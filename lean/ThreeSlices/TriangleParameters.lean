import ThreeSlices.ChordTriangle
import ThreeSlices.SixRayConstruction
import ThreeSlices.TriangleSectorFormulas

open Set Module

namespace ThreeSlices

noncomputable def chordTriangleCenter (A B : ℝ) : Fin 3 → ℝ :=
  ![1 / (1 + A + B), A / (1 + A + B), B / (1 + A + B)]

noncomputable def chordTriangleLineParameters (A B : ℝ) (t : Fin 3 → Fin 2 → ℝ) : Fin 3 → ℝ :=
  ![A * t 1 1 / (B * t 0 1), B * t 2 1 / t 1 0, t 0 0 / (A * t 2 0)]

lemma chordTriangleCenter_pos {A B : ℝ} (hA : 0 < A) (hB : 0 < B) (i : Fin 3) :
    0 < chordTriangleCenter A B i := by
  have hD : 0 < 1 + A + B := by linarith
  fin_cases i <;> simp [chordTriangleCenter] <;> positivity

lemma chordTriangleCenter_sum {A B : ℝ} (hA : 0 < A) (hB : 0 < B) :
    ∑ i, chordTriangleCenter A B i = 1 := by
  rw [Fin.sum_univ_three]
  simp [chordTriangleCenter]
  have hD : 1 + A + B ≠ 0 := by linarith
  field_simp [hD]

lemma chordTriangleLineParameters_pos {A B : ℝ} (hA : 0 < A) (hB : 0 < B)
    (t : Fin 3 → Fin 2 → ℝ) (ht : ∀ i k, 0 < t i k) (i : Fin 3) :
    0 < chordTriangleLineParameters A B t i := by
  fin_cases i
  · exact div_pos (mul_pos hA (ht 1 1)) (mul_pos hB (ht 0 1))
  · exact div_pos (mul_pos hB (ht 2 1)) (ht 1 0)
  · exact div_pos (ht 0 0) (mul_pos hA (ht 2 0))

private lemma opposite_chordNormal_value (e : Basis (Fin 2) ℝ Plane) (k : Fin 2)
    (u v : Plane) (s t : ℝ) (hu : u = s • v) (he : e k = t • (-v)) :
    t * chordNormal e u = -s := by
  have hown : chordNormal e (e k) = 1 := by fin_cases k <;> simp [chordNormal]
  rw [he, map_smul, map_neg] at hown
  rw [hu, map_smul]
  change t * (s * chordNormal e v) = -s
  change t * -chordNormal e v = 1 at hown
  linear_combination -s * hown

private lemma normalizedRay_opposites (a b : ℝ) :
    normalizedNumeratorRay a b 2 0 = -normalizedNumeratorRay a b 0 0 ∧
    normalizedNumeratorRay a b 2 1 = -normalizedNumeratorRay a b 1 0 ∧
    normalizedNumeratorRay a b 1 1 = -normalizedNumeratorRay a b 0 1 := by
  refine ⟨?_, ?_, ?_⟩ <;> apply PiLp.ext <;> intro i <;>
    fin_cases i <;> simp [normalizedNumeratorRay, PiLp.neg_apply]

lemma normalized_radial_chordNormal_opposite_values {a b : ℝ}
    (e : Fin 3 → Basis (Fin 2) ℝ Plane) (t : Fin 3 → Fin 2 → ℝ)
    (he : ∀ i k, e i k = t i k • normalizedNumeratorRay a b i k) :
    t 2 0 * chordNormal (e 2) (e 0 0) = -t 0 0 ∧
    t 2 1 * chordNormal (e 2) (e 1 0) = -t 1 0 ∧
    t 0 0 * chordNormal (e 0) (e 2 0) = -t 2 0 ∧
    t 0 1 * chordNormal (e 0) (e 1 1) = -t 1 1 ∧
    t 1 1 * chordNormal (e 1) (e 0 1) = -t 0 1 ∧
    t 1 0 * chordNormal (e 1) (e 2 1) = -t 2 1 := by
  obtain ⟨hr₀, hr₁, hr₂⟩ := normalizedRay_opposites a b
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact opposite_chordNormal_value (e 2) 0 (e 0 0) _ _ _ (he 0 0) (by rw [he 2 0, hr₀])
  · exact opposite_chordNormal_value (e 2) 1 (e 1 0) _ _ _ (he 1 0) (by rw [he 2 1, hr₁])
  · exact opposite_chordNormal_value (e 0) 0 (e 2 0) _ _ _ (he 2 0)
      (by rw [he 0 0, hr₀]; simp)
  · exact opposite_chordNormal_value (e 0) 1 (e 1 1) _ _ _ (he 1 1)
      (by rw [he 0 1, hr₂]; simp)
  · exact opposite_chordNormal_value (e 1) 1 (e 0 1) _ _ _ (he 0 1) (by rw [he 1 1, hr₂])
  · exact opposite_chordNormal_value (e 1) 0 (e 2 1) _ _ _ (he 2 1)
      (by rw [he 1 0, hr₁]; simp)

/-- Feasibility of the six endpoints gives the six weak vertex conditions of the comparison triangle. -/
theorem chordTriangle_weak_vertex_scalar_bounds
    {a b A B : ℝ} (hA : 0 < A) (hB : 0 < B)
    (e : Fin 3 → Basis (Fin 2) ℝ Plane) (t : Fin 3 → Fin 2 → ℝ)
    (ht : ∀ i k, 0 < t i k)
    (he : ∀ i k, e i k = t i k • normalizedNumeratorRay a b i k)
    (hrel : ∀ x, chordNormal (e 2) x = -A * chordNormal (e 0) x - B * chordNormal (e 1) x)
    (hfeas : ∀ i k j, chordNormal (e j) (e i k) ≤ 1) :
    t 1 0 ≤ t 2 1 * (A + B) ∧ t 0 0 ≤ t 2 0 * (A + B) ∧
      A * t 2 0 ≤ t 0 0 * (1 + B) ∧ A * t 1 1 ≤ t 0 1 * (1 + B) ∧
      B * t 0 1 ≤ t 1 1 * (1 + A) ∧ B * t 2 1 ≤ t 1 0 * (1 + A) := by
  obtain ⟨hv₀, hv₁, hv₂, hv₃, hv₄, hv₅⟩ := normalized_radial_chordNormal_opposite_values e t he
  have hown (i : Fin 3) (k : Fin 2) : chordNormal (e i) (e i k) = 1 := by
    fin_cases k <;> simp [chordNormal]
  have h₀ := hrel (e 1 0)
  have h₁ := hrel (e 0 0)
  have h₂ := hrel (e 2 0)
  have h₃ := hrel (e 1 1)
  have h₄ := hrel (e 0 1)
  have h₅ := hrel (e 2 1)
  rw [hown 1 0] at h₀
  rw [hown 0 0] at h₁
  rw [hown 2 0] at h₂
  rw [hown 1 1] at h₃
  rw [hown 0 1] at h₄
  rw [hown 2 1] at h₅
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hu := mul_le_mul_of_nonneg_left (hfeas 1 0 0) (mul_pos (ht 2 1) hA).le
    have hv := congrArg (fun z : ℝ => t 2 1 * z) h₀
    nlinarith only [hu, hv, hv₁]
  · have hu := mul_le_mul_of_nonneg_left (hfeas 0 0 1) (mul_pos (ht 2 0) hB).le
    have hv := congrArg (fun z : ℝ => t 2 0 * z) h₁
    nlinarith only [hu, hv, hv₀]
  · have hu := mul_le_mul_of_nonneg_left (hfeas 2 0 1) (mul_pos (ht 0 0) hB).le
    have hv := congrArg (fun z : ℝ => t 0 0 * z) h₂
    have hw := congrArg (fun z : ℝ => A * z) hv₂
    nlinarith only [hu, hv, hw]
  · have hu := mul_le_mul_of_nonneg_left (hfeas 1 1 2) (ht 0 1).le
    have hv := congrArg (fun z : ℝ => t 0 1 * z) h₃
    have hw := congrArg (fun z : ℝ => A * z) hv₃
    nlinarith only [hu, hv, hw]
  · have hu := mul_le_mul_of_nonneg_left (hfeas 0 1 2) (ht 1 1).le
    have hv := congrArg (fun z : ℝ => t 1 1 * z) h₄
    have hw := congrArg (fun z : ℝ => B * z) hv₄
    nlinarith only [hu, hv, hw]
  · have hu := mul_le_mul_of_nonneg_left (hfeas 2 1 0) (mul_pos (ht 1 0) hA).le
    have hv := congrArg (fun z : ℝ => t 1 0 * z) h₅
    have hw := congrArg (fun z : ℝ => B * z) hv₅
    nlinarith only [hu, hv, hw]

/-- The radial endpoint constraints imply the weak barycentric vertex signs. -/
theorem chordTriangle_weak_vertex_conditions
    {a b A B : ℝ} (hA : 0 < A) (hB : 0 < B)
    (e : Fin 3 → Basis (Fin 2) ℝ Plane) (t : Fin 3 → Fin 2 → ℝ)
    (ht : ∀ i k, 0 < t i k)
    (he : ∀ i k, e i k = t i k • normalizedNumeratorRay a b i k)
    (hrel : ∀ x, chordNormal (e 2) x = -A * chordNormal (e 0) x - B * chordNormal (e 1) x)
    (hfeas : ∀ i k j, chordNormal (e j) (e i k) ≤ 1) (i : Fin 3) :
    chordTriangleCenter A B (i + 2) ≤ chordTriangleLineParameters A B t (i + 1) *
      (1 - chordTriangleCenter A B i) ∧
      chordTriangleLineParameters A B t (i + 2) * chordTriangleCenter A B (i + 1) ≤
        1 - chordTriangleCenter A B i := by
  obtain ⟨h₀, h₁, h₂, h₃, h₄, h₅⟩ :=
    chordTriangle_weak_vertex_scalar_bounds hA hB e t ht he hrel hfeas
  have hD : 0 < 1 + A + B := by linarith
  fin_cases i <;> constructor
  · have hh : 1 ≤ t 2 1 * (A + B) / t 1 0 :=
      (le_div_iff₀ (ht 1 0)).2 (by simpa using h₀)
    convert mul_le_mul_of_nonneg_left hh (div_nonneg hB.le hD.le) using 1 <;>
      simp [chordTriangleCenter, chordTriangleLineParameters]
    all_goals field_simp [(ht 1 0).ne', hD.ne']
    all_goals ring
  · have hh : t 0 0 / t 2 0 ≤ A + B := (div_le_iff₀ (ht 2 0)).2 (by simpa [mul_comm] using h₁)
    convert div_le_div_of_nonneg_right hh hD.le using 1 <;>
      simp [chordTriangleCenter, chordTriangleLineParameters] <;>
      field_simp [(ht 2 0).ne', hA.ne', hD.ne']
    all_goals ring
  · have hh : 1 ≤ t 0 0 * (1 + B) / (A * t 2 0) :=
      (le_div_iff₀ (mul_pos hA (ht 2 0))).2 (by simpa using h₂)
    convert mul_le_mul_of_nonneg_left hh (div_nonneg zero_le_one hD.le) using 1 <;>
      simp [chordTriangleCenter, chordTriangleLineParameters]
    all_goals field_simp [(ht 2 0).ne', hA.ne', hD.ne']
    all_goals ring
  · have hh : A * t 1 1 / t 0 1 ≤ 1 + B := (div_le_iff₀ (ht 0 1)).2 (by simpa [mul_comm] using h₃)
    convert div_le_div_of_nonneg_right hh hD.le using 1 <;>
      simp [chordTriangleCenter, chordTriangleLineParameters] <;>
      field_simp [(ht 0 1).ne', hB.ne', hD.ne']
    all_goals ring
  · have hh : 1 ≤ t 1 1 * (1 + A) / (B * t 0 1) :=
      (le_div_iff₀ (mul_pos hB (ht 0 1))).2 (by simpa using h₄)
    convert mul_le_mul_of_nonneg_left hh (div_nonneg hA.le hD.le) using 1 <;>
      simp [chordTriangleCenter, chordTriangleLineParameters]
    all_goals field_simp [(ht 0 1).ne', hB.ne', hD.ne']
    all_goals ring
  · have hh : B * t 2 1 / t 1 0 ≤ 1 + A := (div_le_iff₀ (ht 1 0)).2 (by simpa [mul_comm] using h₅)
    convert div_le_div_of_nonneg_right hh hD.le using 1 <;>
      simp [chordTriangleCenter, chordTriangleLineParameters] <;>
      field_simp [(ht 1 0).ne', hD.ne']
    all_goals ring

noncomputable def chordTriangleFanLine (A B : ℝ) (t : Fin 3 → Fin 2 → ℝ)
    (i : Fin 3) (q : Plane) : ℝ :=
  triangleBarycentric q (i + 1) - chordTriangleCenter A B (i + 1) +
    chordTriangleLineParameters A B t i *
      (triangleBarycentric q (i + 2) - chordTriangleCenter A B (i + 2))

noncomputable def chordTrianglePulledLine (e : Fin 3 → Basis (Fin 2) ℝ Plane)
    (A B : ℝ) (t : Fin 3 → Fin 2 → ℝ) : Fin 3 → Plane → ℝ :=
  ![fun x => (-A * chordNormal (e 0) x - chordTriangleLineParameters A B t 0 * B * chordNormal (e 1) x) / (1 + A + B),
    fun x => (-B * chordNormal (e 1) x - chordTriangleLineParameters A B t 1 * chordNormal (e 2) x) / (1 + A + B),
    fun x => (-chordNormal (e 2) x - chordTriangleLineParameters A B t 2 * A * chordNormal (e 0) x) / (1 + A + B)]

theorem chordTriangleFanLine_map {A B : ℝ} (hA : 0 < A) (hB : 0 < B)
    (e : Fin 3 → Basis (Fin 2) ℝ Plane) (t : Fin 3 → Fin 2 → ℝ)
    (E : Plane ≃ᴬ[ℝ] Plane)
    (hrel : ∀ x, chordNormal (e 2) x = -A * chordNormal (e 0) x - B * chordNormal (e 1) x)
    (hE₀ : ∀ x, E x 0 = A * (1 - chordNormal (e 0) x) / (1 + A + B))
    (hE₁ : ∀ x, E x 1 = B * (1 - chordNormal (e 1) x) / (1 + A + B))
    (i : Fin 3) (x : Plane) :
    chordTriangleFanLine A B t i (E x) = chordTrianglePulledLine e A B t i x := by
  have hD : 1 + A + B ≠ 0 := by linarith
  fin_cases i <;> simp [chordTriangleFanLine, triangleBarycentric,
    chordTriangleCenter, chordTrianglePulledLine, hE₀, hE₁, hrel x, -chordNormal_apply] <;>
    field_simp [hD] <;> ring

lemma chordTrianglePulledLine_combo (e : Fin 3 → Basis (Fin 2) ℝ Plane)
    (A B : ℝ) (t : Fin 3 → Fin 2 → ℝ) (i : Fin 3) (x y : Plane) (s r : ℝ) :
    chordTrianglePulledLine e A B t i (s • x + r • y) =
      s * chordTrianglePulledLine e A B t i x + r * chordTrianglePulledLine e A B t i y := by
  fin_cases i <;> simp [chordTrianglePulledLine, map_add, map_smul] <;> ring

theorem chordTriangle_side_coordinate {A B : ℝ} (hA : 0 < A) (hB : 0 < B)
    (e : Fin 3 → Basis (Fin 2) ℝ Plane) (E : Plane ≃ᴬ[ℝ] Plane)
    (hrel : ∀ x, chordNormal (e 2) x = -A * chordNormal (e 0) x - B * chordNormal (e 1) x)
    (hE₀ : ∀ x, E x 0 = A * (1 - chordNormal (e 0) x) / (1 + A + B))
    (hE₁ : ∀ x, E x 1 = B * (1 - chordNormal (e 1) x) / (1 + A + B))
    (i : Fin 3) (k : Fin 2) : triangleBarycentric (E (e i k)) (i + 1) = 0 := by
  have hown (j : Fin 3) : chordNormal (e j) (e j k) = 1 := by
    fin_cases k <;> simp [chordNormal]
  have hD : 1 + A + B ≠ 0 := by linarith
  fin_cases i
  · simp [triangleBarycentric, hE₀, hown]
  · simp [triangleBarycentric, hE₁, hown]
  · simp [triangleBarycentric, hE₀, hE₁, -chordNormal_apply]
    field_simp [hD]
    have hr := hrel (e 2 k)
    rw [hown 2] at hr
    nlinarith only [hr]

theorem chordTrianglePulledLine_endpoint_zeros {a b A B : ℝ}
    (hA : 0 < A) (hB : 0 < B)
    (e : Fin 3 → Basis (Fin 2) ℝ Plane) (t : Fin 3 → Fin 2 → ℝ)
    (ht : ∀ i k, 0 < t i k)
    (he : ∀ i k, e i k = t i k • normalizedNumeratorRay a b i k) :
    chordTrianglePulledLine e A B t 0 (e 0 1) = 0 ∧
    chordTrianglePulledLine e A B t 0 (e 1 1) = 0 ∧
    chordTrianglePulledLine e A B t 1 (e 1 0) = 0 ∧
    chordTrianglePulledLine e A B t 1 (e 2 1) = 0 ∧
    chordTrianglePulledLine e A B t 2 (e 0 0) = 0 ∧
    chordTrianglePulledLine e A B t 2 (e 2 0) = 0 := by
  obtain ⟨hv₀, hv₁, hv₂, hv₃, hv₄, hv₅⟩ := normalized_radial_chordNormal_opposite_values e t he
  have hown (i : Fin 3) (k : Fin 2) : chordNormal (e i) (e i k) = 1 := by
    fin_cases k <;> simp [chordNormal]
  have hD : 1 + A + B ≠ 0 := by linarith
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hz : (-A / t 0 1) * (t 0 1 + t 1 1 * chordNormal (e 1) (e 0 1)) / (1 + A + B) = 0 := by rw [hv₄]; ring
    convert hz using 1; simp [chordTrianglePulledLine, chordTriangleLineParameters, hown, -chordNormal_apply]
    field_simp [hB.ne', (ht 0 1).ne', hD]
    ring
  · have hz : (-A / t 0 1) * (t 0 1 * chordNormal (e 0) (e 1 1) + t 1 1) / (1 + A + B) = 0 := by rw [hv₃]; ring
    convert hz using 1; simp [chordTrianglePulledLine, chordTriangleLineParameters, hown, -chordNormal_apply]
    field_simp [hB.ne', (ht 0 1).ne', hD]
    ring
  · have hz : (-B / t 1 0) * (t 1 0 + t 2 1 * chordNormal (e 2) (e 1 0)) / (1 + A + B) = 0 := by rw [hv₁]; ring
    convert hz using 1; simp [chordTrianglePulledLine, chordTriangleLineParameters, hown, -chordNormal_apply]
    field_simp [(ht 1 0).ne', hD]
    ring
  · have hz : (-B / t 1 0) * (t 1 0 * chordNormal (e 1) (e 2 1) + t 2 1) / (1 + A + B) = 0 := by rw [hv₅]; ring
    convert hz using 1; simp [chordTrianglePulledLine, chordTriangleLineParameters, hown, -chordNormal_apply]
    field_simp [(ht 1 0).ne', hD]
    ring
  · have hz : (-1 / t 2 0) * (t 2 0 * chordNormal (e 2) (e 0 0) + t 0 0) / (1 + A + B) = 0 := by rw [hv₀]; ring
    convert hz using 1; simp [chordTrianglePulledLine, chordTriangleLineParameters, hown, -chordNormal_apply]
    field_simp [hA.ne', (ht 2 0).ne', hD]
    ring
  · have hz : (-1 / t 2 0) * (t 2 0 + t 0 0 * chordNormal (e 0) (e 2 0)) / (1 + A + B) = 0 := by rw [hv₂]; ring
    convert hz using 1; simp [chordTrianglePulledLine, chordTriangleLineParameters, hown, -chordNormal_apply]
    field_simp [hA.ne', (ht 2 0).ne', hD]
    ring

private lemma parameter_barycentric_pair_injective (i : Fin 3) (p q : Plane)
    (hp : triangleBarycentric p i = 0) (hq : triangleBarycentric q i = 0)
    (hnext : triangleBarycentric p (i + 1) = triangleBarycentric q (i + 1)) : p = q := by
  fin_cases i <;> apply PiLp.ext <;> intro k <;> fin_cases k <;>
    simp [triangleBarycentric] at hp hq hnext ⊢ <;> linarith

private lemma parameter_center_cyclic_sum {A B : ℝ} (hA : 0 < A) (hB : 0 < B) (i : Fin 3) :
    chordTriangleCenter A B i + chordTriangleCenter A B (i + 1) +
      chordTriangleCenter A B (i + 2) = 1 := by
  have hD : 1 + A + B ≠ 0 := by linarith
  fin_cases i <;> simp [chordTriangleCenter] <;> field_simp [hD]
  all_goals ring

private lemma parameter_barycentric_cyclic_sum (i : Fin 3) (q : Plane) :
    triangleBarycentric q i + triangleBarycentric q (i + 1) +
      triangleBarycentric q (i + 2) = 1 := by
  fin_cases i <;> simp [triangleBarycentric]
  all_goals ring

private lemma parameter_side_lower_coordinate {A B : ℝ} (hA : 0 < A) (hB : 0 < B)
    (t : Fin 3 → Fin 2 → ℝ) (i : Fin 3) (q : Plane)
    (hside : triangleBarycentric q i = 0)
    (hline : chordTriangleFanLine A B t (i + 1) q = 0) :
    triangleBarycentric q (i + 1) = chordTriangleCenter A B (i + 1) +
      (1 - chordTriangleLineParameters A B t (i + 1)) * chordTriangleCenter A B i := by
  have hl : triangleBarycentric q (i + 2) - chordTriangleCenter A B (i + 2) +
      chordTriangleLineParameters A B t (i + 1) *
        (triangleBarycentric q i - chordTriangleCenter A B i) = 0 := by
    simpa [chordTriangleFanLine, add_assoc] using hline
  rw [hside] at hl
  nlinarith only [hl, parameter_center_cyclic_sum hA hB i, parameter_barycentric_cyclic_sum i q, hside]

private lemma parameter_side_upper_coordinate {A B : ℝ} (hA : 0 < A) (hB : 0 < B)
    (t : Fin 3 → Fin 2 → ℝ) (ht : ∀ i k, 0 < t i k) (i : Fin 3) (q : Plane)
    (hside : triangleBarycentric q i = 0)
    (hline : chordTriangleFanLine A B t (i + 2) q = 0) :
    triangleBarycentric q (i + 1) = chordTriangleCenter A B (i + 1) +
      chordTriangleCenter A B i / chordTriangleLineParameters A B t (i + 2) := by
  have hl : triangleBarycentric q i - chordTriangleCenter A B i +
      chordTriangleLineParameters A B t (i + 2) *
        (triangleBarycentric q (i + 1) - chordTriangleCenter A B (i + 1)) = 0 := by
    simpa [chordTriangleFanLine, add_assoc] using hline
  rw [hside] at hl
  have hm := (chordTriangleLineParameters_pos hA hB t ht (i + 2)).ne'
  apply (sub_eq_iff_eq_add').1
  apply (eq_div_iff hm).2
  nlinarith only [hl]

private lemma parameter_width_pos_of_side_endpoints {A B : ℝ} (hA : 0 < A) (hB : 0 < B)
    (t : Fin 3 → Fin 2 → ℝ) (ht : ∀ i k, 0 < t i k) (i : Fin 3)
    (hlower : chordTriangleCenter A B (i + 2) ≤ chordTriangleLineParameters A B t (i + 1) *
      (1 - chordTriangleCenter A B i))
    (hupper : chordTriangleLineParameters A B t (i + 2) * chordTriangleCenter A B (i + 1) ≤
      1 - chordTriangleCenter A B i)
    (p q : Plane) (hp : triangleBarycentric p i = 0)
    (hq : triangleBarycentric q i = 0)
    (hpLine : chordTriangleFanLine A B t (i + 1) p = 0)
    (hqLine : chordTriangleFanLine A B t (i + 2) q = 0) (hpq : p ≠ q) :
    0 < chordTriangleLineParameters A B t (i + 1) + 1 / chordTriangleLineParameters A B t (i + 2) - 1 := by
  have hsum := parameter_center_cyclic_sum hA hB i
  have hy := chordTriangleCenter_pos hA hB (i + 1)
  have hz := chordTriangleCenter_pos hA hB (i + 2)
  have hm := chordTriangleLineParameters_pos hA hB t ht (i + 2)
  have hd : 0 < 1 - chordTriangleCenter A B i := by linarith
  have hlow := (div_le_iff₀ hd).2 hlower
  have hhigh : chordTriangleCenter A B (i + 1) / (1 - chordTriangleCenter A B i) ≤
      1 / chordTriangleLineParameters A B t (i + 2) :=
    (div_le_div_iff₀ hd hm).2 (by nlinarith only [hupper])
  have hh := add_le_add hlow hhigh
  rw [← add_div, show chordTriangleCenter A B (i + 2) + chordTriangleCenter A B (i + 1) =
      1 - chordTriangleCenter A B i by linarith, div_self hd.ne'] at hh
  by_contra hc
  have heq : 1 - chordTriangleLineParameters A B t (i + 1) =
      1 / chordTriangleLineParameters A B t (i + 2) := by linarith
  have hpc := parameter_side_lower_coordinate hA hB t i p hp hpLine
  have hqc := parameter_side_upper_coordinate hA hB t ht i q hq hqLine
  rw [heq] at hpc
  apply hpq
  apply parameter_barycentric_pair_injective i p q hp hq
  rw [hpc, hqc]
  ring

/-- Positive sector width follows from feasible vertices and the distinct radial endpoints on each side. -/
theorem chordTriangle_width_pos {a b A B : ℝ} (hA : 0 < A) (hB : 0 < B)
    (e : Fin 3 → Basis (Fin 2) ℝ Plane) (t : Fin 3 → Fin 2 → ℝ) (ht : ∀ i k, 0 < t i k)
    (he : ∀ i k, e i k = t i k • normalizedNumeratorRay a b i k)
    (hrel : ∀ x, chordNormal (e 2) x = -A * chordNormal (e 0) x - B * chordNormal (e 1) x)
    (hfeas : ∀ i k j, chordNormal (e j) (e i k) ≤ 1)
    (E : Plane ≃ᴬ[ℝ] Plane)
    (hE₀ : ∀ x, E x 0 = A * (1 - chordNormal (e 0) x) / (1 + A + B))
    (hE₁ : ∀ x, E x 1 = B * (1 - chordNormal (e 1) x) / (1 + A + B)) (i : Fin 3) :
    0 < chordTriangleLineParameters A B t (i + 1) + 1 / chordTriangleLineParameters A B t (i + 2) - 1 := by
  have hweak := chordTriangle_weak_vertex_conditions hA hB e t ht he hrel hfeas i
  obtain ⟨hz₀, hz₁, hz₂, hz₃, hz₄, hz₅⟩ := chordTrianglePulledLine_endpoint_zeros hA hB e t ht he
  have hmap := chordTriangleFanLine_map hA hB e t E hrel hE₀ hE₁
  have hside := chordTriangle_side_coordinate hA hB e E hrel hE₀ hE₁
  fin_cases i
  · apply parameter_width_pos_of_side_endpoints hA hB t ht 0 hweak.1 hweak.2
      (E (e 2 1)) (E (e 2 0)) (hside 2 1) (hside 2 0)
      ((hmap 1 (e 2 1)).trans hz₃) ((hmap 2 (e 2 0)).trans hz₅)
    exact E.injective.ne ((e 2).injective.ne (by decide : (1 : Fin 2) ≠ 0))
  · apply parameter_width_pos_of_side_endpoints hA hB t ht 1 hweak.1 hweak.2
      (E (e 0 0)) (E (e 0 1)) (hside 0 0) (hside 0 1)
      ((hmap 2 (e 0 0)).trans hz₄) ((hmap 0 (e 0 1)).trans hz₀)
    exact E.injective.ne ((e 0).injective.ne (by decide : (0 : Fin 2) ≠ 1))
  · apply parameter_width_pos_of_side_endpoints hA hB t ht 2 hweak.1 hweak.2
      (E (e 1 1)) (E (e 1 0)) (hside 1 1) (hside 1 0)
      ((hmap 0 (e 1 1)).trans hz₁) ((hmap 1 (e 1 0)).trans hz₂)
    exact E.injective.ne ((e 1).injective.ne (by decide : (1 : Fin 2) ≠ 0))

private lemma parameter_side_endpoint_cross_signs {A B : ℝ} (hA : 0 < A) (hB : 0 < B)
    (t : Fin 3 → Fin 2 → ℝ) (ht : ∀ i k, 0 < t i k) (i : Fin 3)
    (p q : Plane) (hp : triangleBarycentric p i = 0) (hq : triangleBarycentric q i = 0)
    (hpLine : chordTriangleFanLine A B t (i + 1) p = 0)
    (hqLine : chordTriangleFanLine A B t (i + 2) q = 0)
    (hc : 0 < chordTriangleLineParameters A B t (i + 1) + 1 / chordTriangleLineParameters A B t (i + 2) - 1) :
    chordTriangleFanLine A B t (i + 2) p < 0 ∧ chordTriangleFanLine A B t (i + 1) q < 0 := by
  have hpc := parameter_side_lower_coordinate hA hB t i p hp hpLine
  have hqc := parameter_side_upper_coordinate hA hB t ht i q hq hqLine
  have hm := chordTriangleLineParameters_pos hA hB t ht (i + 2)
  have hx := chordTriangleCenter_pos hA hB i
  have hpVal : chordTriangleFanLine A B t (i + 2) p =
      -chordTriangleLineParameters A B t (i + 2) * chordTriangleCenter A B i *
        (chordTriangleLineParameters A B t (i + 1) + 1 / chordTriangleLineParameters A B t (i + 2) - 1) := by
    simp [chordTriangleFanLine, add_assoc, hp, hpc]
    field_simp [hm.ne']
    ring
  have hqPrev : triangleBarycentric q (i + 2) = 1 - triangleBarycentric q (i + 1) := by
    nlinarith only [parameter_barycentric_cyclic_sum i q, hq]
  have hxPrev : chordTriangleCenter A B (i + 2) = 1 - chordTriangleCenter A B i -
      chordTriangleCenter A B (i + 1) := by nlinarith only [parameter_center_cyclic_sum hA hB i]
  have hqVal : chordTriangleFanLine A B t (i + 1) q = -chordTriangleCenter A B i *
      (chordTriangleLineParameters A B t (i + 1) + 1 / chordTriangleLineParameters A B t (i + 2) - 1) := by
    simp [chordTriangleFanLine, add_assoc, hq, hqPrev, hxPrev, hqc]
    ring
  rw [hpVal, hqVal]
  exact ⟨mul_neg_of_neg_of_pos (mul_neg_of_neg_of_pos (neg_neg_of_pos hm) hx) hc,
    mul_neg_of_neg_of_pos (neg_neg_of_pos hx) hc⟩

private lemma parameter_sector_iff_lines {A B : ℝ} (hA : 0 < A) (hB : 0 < B)
    (t : Fin 3 → Fin 2 → ℝ) (ht : ∀ i k, 0 < t i k) (i : Fin 3) (q : Plane) :
    (q ∈ barycentricNumeratorSector (chordTriangleCenter A B) (chordTriangleLineParameters A B t) i ↔
      chordTriangleFanLine A B t (i + 1) q ≤ 0 ∧ chordTriangleFanLine A B t (i + 2) q ≤ 0) ∧
    (q ∈ barycentricDenominatorSector (chordTriangleCenter A B) (chordTriangleLineParameters A B t) i ↔
      0 ≤ chordTriangleFanLine A B t (i + 1) q ∧ 0 ≤ chordTriangleFanLine A B t (i + 2) q) := by
  have hm := chordTriangleLineParameters_pos hA hB t ht (i + 2)
  have hnext : chordTriangleFanLine A B t (i + 1) q =
      -(triangleBarycentric q (i + 1) - chordTriangleCenter A B (i + 1)) +
        (chordTriangleLineParameters A B t (i + 1) - 1) *
          (triangleBarycentric q i - chordTriangleCenter A B i) := by
    simp only [chordTriangleFanLine]
    have hs := parameter_barycentric_cyclic_sum i q
    have hx := parameter_center_cyclic_sum hA hB i
    simp [add_assoc]
    nlinarith only [hs, hx]
  have hprev : chordTriangleFanLine A B t (i + 2) q = triangleBarycentric q i - chordTriangleCenter A B i +
      chordTriangleLineParameters A B t (i + 2) *
        (triangleBarycentric q (i + 1) - chordTriangleCenter A B (i + 1)) := by
    simp [chordTriangleFanLine, add_assoc]
  constructor
  · change (_ ≤ _ ∧ _ ≤ _) ↔ _
    rw [← sub_le_iff_le_add', le_div_iff₀ hm, hnext, hprev]
    constructor <;> rintro ⟨h₀, h₁⟩ <;> constructor <;> nlinarith only [h₀, h₁]
  · change (_ ≤ _ ∧ _ ≤ _) ↔ _
    rw [add_comm (chordTriangleCenter A B (i + 1)), ← le_sub_iff_add_le, div_le_iff₀ hm, hnext, hprev]
    constructor <;> rintro ⟨h₀, h₁⟩ <;> constructor <;> nlinarith only [h₀, h₁]

private lemma basis_cone_iff_negative_pair (e : Basis (Fin 2) ℝ Plane) (F G : Plane → ℝ)
    (hF : ∀ x y s r, F (s • x + r • y) = s * F x + r * F y)
    (hG : ∀ x y s r, G (s • x + r • y) = s * G x + r * G y)
    (hF₀ : F (e 0) = 0) (hG₁ : G (e 1) = 0)
    (hF₁ : F (e 1) < 0) (hG₀ : G (e 0) < 0) (x : Plane) :
    (x ∈ chordSector e ↔ F x ≤ 0 ∧ G x ≤ 0) ∧
      (-x ∈ chordSector e ↔ 0 ≤ F x ∧ 0 ≤ G x) := by
  have hFx : F x = e.repr x 1 * F (e 1) := by
    calc
      F x = F (e.repr x 0 • e 0 + e.repr x 1 • e 1) := congrArg F (basis_two_repr e x).symm
      _ = e.repr x 1 * F (e 1) := by rw [hF, hF₀]; ring
  have hGx : G x = e.repr x 0 * G (e 0) := by
    calc
      G x = G (e.repr x 0 • e 0 + e.repr x 1 • e 1) := congrArg G (basis_two_repr e x).symm
      _ = e.repr x 0 * G (e 0) := by rw [hG, hG₁]; ring
  constructor
  · change (0 ≤ e.repr x 0 ∧ 0 ≤ e.repr x 1) ↔ _
    rw [hFx, hGx]
    simp [mul_nonpos_iff, hF₁.le, hG₀.le, not_le.mpr hF₁, not_le.mpr hG₀, and_comm]
  · change (0 ≤ e.repr (-x) 0 ∧ 0 ≤ e.repr (-x) 1) ↔ _
    rw [hFx, hGx]
    simp [map_neg, mul_nonneg_iff, hF₁.le, hG₀.le, not_le.mpr hF₁, not_le.mpr hG₀, and_comm]

/-- The canonical affine map realizes all six cones with the cyclic vertex labeling. -/
theorem chordTriangle_sector_images {a b A B : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hA : 0 < A) (hB : 0 < B)
    (e : Fin 3 → Basis (Fin 2) ℝ Plane) (t : Fin 3 → Fin 2 → ℝ) (ht : ∀ i k, 0 < t i k)
    (he : ∀ i k, e i k = t i k • normalizedNumeratorRay a b i k)
    (hrel : ∀ x, chordNormal (e 2) x = -A * chordNormal (e 0) x - B * chordNormal (e 1) x)
    (hfeas : ∀ i k j, chordNormal (e j) (e i k) ≤ 1)
    (E : Plane ≃ᴬ[ℝ] Plane)
    (hE₀ : ∀ x, E x 0 = A * (1 - chordNormal (e 0) x) / (1 + A + B))
    (hE₁ : ∀ x, E x 1 = B * (1 - chordNormal (e 1) x) / (1 + A + B)) :
    ∀ i : Fin 3,
      E '' normalizedNumeratorSector a b i =
        barycentricNumeratorSector (chordTriangleCenter A B) (chordTriangleLineParameters A B t) (i + 1) ∧
      E '' normalizedDenominatorSector a b i =
        barycentricDenominatorSector (chordTriangleCenter A B) (chordTriangleLineParameters A B t) (i + 1) := by
  obtain ⟨hz₀, hz₁, hz₂, hz₃, hz₄, hz₅⟩ := chordTrianglePulledLine_endpoint_zeros hA hB e t ht he
  have hmap := chordTriangleFanLine_map hA hB e t E hrel hE₀ hE₁
  have hside := chordTriangle_side_coordinate hA hB e E hrel hE₀ hE₁
  have hwidth := chordTriangle_width_pos hA hB e t ht he hrel hfeas E hE₀ hE₁
  have hsign₀ := parameter_side_endpoint_cross_signs hA hB t ht 0
    (E (e 2 1)) (E (e 2 0)) (hside 2 1) (hside 2 0)
    ((hmap 1 (e 2 1)).trans hz₃) ((hmap 2 (e 2 0)).trans hz₅) (hwidth 0)
  have hsign₁ := parameter_side_endpoint_cross_signs hA hB t ht 1
    (E (e 0 0)) (E (e 0 1)) (hside 0 0) (hside 0 1)
    ((hmap 2 (e 0 0)).trans hz₄) ((hmap 0 (e 0 1)).trans hz₀) (hwidth 1)
  have hsign₂ := parameter_side_endpoint_cross_signs hA hB t ht 2
    (E (e 1 1)) (E (e 1 0)) (hside 1 1) (hside 1 0)
    ((hmap 0 (e 1 1)).trans hz₁) ((hmap 1 (e 1 0)).trans hz₂) (hwidth 2)
  norm_num at hsign₀ hsign₁ hsign₂
  rw [hmap 2 (e 2 1), hmap 1 (e 2 0)] at hsign₀
  rw [hmap 0 (e 0 0), hmap 2 (e 0 1)] at hsign₁
  rw [hmap 1 (e 1 1), hmap 0 (e 1 0)] at hsign₂
  have hpair₀ := basis_cone_iff_negative_pair (e 0)
    (chordTrianglePulledLine e A B t 2) (chordTrianglePulledLine e A B t 0)
    (chordTrianglePulledLine_combo e A B t 2) (chordTrianglePulledLine_combo e A B t 0)
    hz₄ hz₀ hsign₁.2 hsign₁.1
  have hpair₁ := basis_cone_iff_negative_pair (e 1)
    (chordTrianglePulledLine e A B t 1) (chordTrianglePulledLine e A B t 0)
    (chordTrianglePulledLine_combo e A B t 1) (chordTrianglePulledLine_combo e A B t 0)
    hz₂ hz₁ hsign₂.1 hsign₂.2
  have hpair₂ := basis_cone_iff_negative_pair (e 2)
    (chordTrianglePulledLine e A B t 2) (chordTrianglePulledLine e A B t 1)
    (chordTrianglePulledLine_combo e A B t 2) (chordTrianglePulledLine_combo e A B t 1)
    hz₅ hz₃ hsign₀.1 hsign₀.2
  intro i
  have hcone := chordSector_eq_normalized ha hb i (e i) (t i) (ht i) (he i)
  have hn (x : Plane) : x ∈ normalizedNumeratorSector a b i ↔
      E x ∈ barycentricNumeratorSector (chordTriangleCenter A B) (chordTriangleLineParameters A B t) (i + 1) := by
    rw [← hcone, (parameter_sector_iff_lines hA hB t ht (i + 1) (E x)).1, hmap, hmap]
    fin_cases i <;> norm_num
    · exact (hpair₀ x).1
    · simpa only [and_comm] using (hpair₁ x).1
    · simpa only [and_comm] using (hpair₂ x).1
  have hd (x : Plane) : x ∈ normalizedDenominatorSector a b i ↔
      E x ∈ barycentricDenominatorSector (chordTriangleCenter A B) (chordTriangleLineParameters A B t) (i + 1) := by
    rw [normalizedDenominatorSector_eq_opposite, ← hcone,
      (parameter_sector_iff_lines hA hB t ht (i + 1) (E x)).2, hmap, hmap]
    change (-x ∈ chordSector (e i)) ↔ _
    fin_cases i <;> norm_num
    · exact (hpair₀ x).2
    · simpa only [and_comm] using (hpair₁ x).2
    · simpa only [and_comm] using (hpair₂ x).2
  constructor
  · change E.toEquiv '' _ = _
    rw [Equiv.image_eq_preimage_symm]
    ext q
    have h := hn (E.symm q)
    rw [E.apply_symm_apply] at h
    exact h
  · change E.toEquiv '' _ = _
    rw [Equiv.image_eq_preimage_symm]
    ext q
    have h := hd (E.symm q)
    rw [E.apply_symm_apply] at h
    exact h

end ThreeSlices
