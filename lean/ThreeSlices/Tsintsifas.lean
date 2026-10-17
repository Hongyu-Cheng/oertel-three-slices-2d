import ThreeSlices.TriangleSectorFormulas
import ThreeSlices.RecessionCases
import ThreeSlices.TriangleParameters

open Set Module

namespace ThreeSlices

private lemma ratio_sum_of_triangle_images {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (P : Set Plane) (hP : IsCompact P) (hzero : (0 : Plane) ∈ interior P)
    (E : Plane ≃ᴬ[ℝ] Plane) (x l : Fin 3 → ℝ)
    (htriangle : E '' P = standardChordTriangle)
    (hnum : ∀ i, E '' normalizedNumeratorSector a b i = barycentricNumeratorSector x l (i + 1))
    (hden : ∀ i, E '' normalizedDenominatorSector a b i = barycentricDenominatorSector x l (i + 1))
    (hx : ∀ i, 0 < x i) (hsum : ∑ i, x i = 1) (hl : ∀ i, 0 < l i)
    (hwidth : ∀ i, 0 < l (i + 1) + 1 / l (i + 2) - 1)
    (hlower : ∀ i, x (i + 2) ≤ l (i + 1) * (1 - x i))
    (hupper : ∀ i, l (i + 2) * x (i + 1) ≤ 1 - x i) :
    (3 / 2 : ℝ) ≤ normalizedSectorRatioSum P a b := by
  have hpos (i : Fin 3) :
      0 < area (standardChordTriangle ∩ barycentricDenominatorSector x l (i + 1)) := by
    rw [← htriangle, ← hden i, ← image_inter E.injective, area_affine_image]
    exact mul_pos (affineAreaScale_pos E) (normalized_denominator_area_pos hP hzero ha hb i)
  have hpos' (i : Fin 3) :
      0 < area (standardChordTriangle ∩ barycentricDenominatorSector x l i) := by
    fin_cases i
    · exact hpos 2
    · exact hpos 0
    · exact hpos 1
  have hratio (i : Fin 3) := affine_image_sector_ratio E P
    (normalizedNumeratorSector a b i) (normalizedDenominatorSector a b i)
  simp only [htriangle, hnum, hden] at hratio
  have h := barycentric_triangle_ratio_sum x l hx hsum hl hwidth hlower hupper hpos'
  rw [normalizedSectorRatioSum, Fin.sum_univ_three]
  rw [← hratio 0, ← hratio 1, ← hratio 2]
  simp only [Fin.sum_univ_three] at h
  simpa [add_comm, add_left_comm, add_assoc] using h

/-- The bounded chord polygon satisfies the six-sector inequality. -/
theorem normalized_bounded_chord_ratio_sum {K : Set Plane} (hK : IsBody K)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (e : Fin 3 → Basis (Fin 2) ℝ Plane) (t : Fin 3 → Fin 2 → ℝ)
    (ht : ∀ i k, 0 < t i k)
    (he : ∀ i k, e i k = t i k • normalizedNumeratorRay a b i k)
    (hend : ∀ i k, IsRadialEndpoint K (e i k))
    (hbdd : Bornology.IsBounded (chordPolygon e)) :
    (3 / 2 : ℝ) ≤ normalizedSectorRatioSum (chordPolygon e) a b := by
  obtain ⟨A, B, hA, hB, hrel, E, htriangle, hE₀, hE₁⟩ :=
    bounded_chordPolygon_coordinate_data e hbdd
  have hfeas (i : Fin 3) (k : Fin 2) (j : Fin 3) : chordNormal (e j) (e i k) ≤ 1 :=
    mem_iInter.mp (normalized_radial_endpoints_mem_chordPolygon hK.2.1 ha hb e t ht he hend i k) j
  have himages := chordTriangle_sector_images ha hb hA hB e t ht he hrel hfeas E hE₀ hE₁
  have hweak := chordTriangle_weak_vertex_conditions hA hB e t ht he hrel hfeas
  exact ratio_sum_of_triangle_images ha hb (chordPolygon e) (chordPolygon_isCompact e hbdd)
    (origin_mem_interior_chordPolygon e) E (chordTriangleCenter A B)
    (chordTriangleLineParameters A B t) htriangle (fun i => (himages i).1)
    (fun i => (himages i).2) (chordTriangleCenter_pos hA hB) (chordTriangleCenter_sum hA hB)
    (chordTriangleLineParameters_pos hA hB t ht)
    (chordTriangle_width_pos hA hB e t ht he hrel hfeas E hE₀ hE₁)
    (fun i => (hweak i).1) (fun i => (hweak i).2)

/-- Tsintsifas's six-sector inequality, with both bounded and unbounded chord cases proved. -/
theorem normalized_tsintsifas : NormalizedTsintsifasStatement := by
  apply normalized_tsintsifas_of_closed_ratios
  intro K hK hzero a b ha hb
  obtain ⟨e, t, ht, he, hend⟩ := exists_six_radial_bases hK hzero ha hb
  by_cases hbdd : Bornology.IsBounded (chordPolygon e)
  · apply (normalized_bounded_chord_ratio_sum hK ha hb e t ht he hend hbdd).trans
    exact normalized_chord_ratio_le hK hzero ha hb e (chordPolygon_isCompact e hbdd) hend
      (fun i => chordSector_eq_normalized ha hb i (e i) (t i) (ht i) (he i))
      (fun i => openChordSector_eq_normalized ha hb i (e i) (t i) (ht i) (he i))
  · obtain ⟨r, hne, hr⟩ := unbounded_chordPolygon_has_recession e hbdd
    have h := normalized_recession_ratio_sum hK hzero ha hb e t ht he hend r hr hne
    linarith

end ThreeSlices
