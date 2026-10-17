import ThreeSlices.RecessionStrip
import ThreeSlices.FanSymmetry

open Set Module

namespace ThreeSlices

private noncomputable def cycleFan (e : Fin 3 → Basis (Fin 2) ℝ Plane) :
    Fin 3 → Basis (Fin 2) ℝ Plane :=
  ![((e 1).map fanCycle.toLinearEquiv).reindex (Equiv.swap 0 1),
    (e 2).map fanCycle.toLinearEquiv,
    ((e 0).map fanCycle.toLinearEquiv).reindex (Equiv.swap 0 1)]

private def cycleScales (t : Fin 3 → Fin 2 → ℝ) : Fin 3 → Fin 2 → ℝ :=
  ![![t 1 1, t 1 0], t 2, ![t 0 1, t 0 0]]

private lemma cycleScales_pos (t : Fin 3 → Fin 2 → ℝ) (ht : ∀ i k, 0 < t i k) :
    ∀ i k, 0 < cycleScales t i k := by
  intro i k
  fin_cases i <;> fin_cases k <;> exact ht _ _

private lemma cycleFan_scaled (e : Fin 3 → Basis (Fin 2) ℝ Plane)
    (t : Fin 3 → Fin 2 → ℝ)
    (he : ∀ i k, e i k = t i k • normalizedNumeratorRay 1 1 i k) :
    ∀ i k, cycleFan e i k = cycleScales t i k • normalizedNumeratorRay 1 1 i k := by
  intro i k
  fin_cases i <;> fin_cases k <;>
    simp [cycleFan, cycleScales, Basis.reindex_apply, he, map_smul, fanCycle_ray,
      fanCycleRayIndex, fanCycleIndex]

private lemma cycleFan_radial {A : Set Plane} (e : Fin 3 → Basis (Fin 2) ℝ Plane)
    (hend : ∀ i k, IsRadialEndpoint A (e i k)) :
    ∀ i k, IsRadialEndpoint (fanCycle '' A) (cycleFan e i k) := by
  intro i k
  fin_cases i <;> fin_cases k <;>
    simp [cycleFan, Basis.reindex_apply]
  all_goals exact (hend _ _).linear_image fanCycle

private lemma cycleFan_polygon (e : Fin 3 → Basis (Fin 2) ℝ Plane) :
    chordPolygon (cycleFan e) = fanCycle '' chordPolygon e := by
  rw [chordPolygon_linear_image]
  ext x
  simp [chordPolygon, Fin.forall_fin_succ, cycleFan, chordHalfplane_swap]
  tauto

private lemma cycleFan_recession (e : Fin 3 → Basis (Fin 2) ℝ Plane) {r : Plane}
    (hr : IsRecessionDirection (chordPolygon e) r) :
    IsRecessionDirection (chordPolygon (cycleFan e)) (fanCycle r) := by
  rw [cycleFan_polygon]
  rintro y ⟨x, hx, rfl⟩ t ht
  exact ⟨x + t • r, hr x hx t ht, by simp⟩

private theorem canonical_recession_ratio_sum {A : Set Plane} (hA : IsBody A)
    (hzero : (0 : Plane) ∈ interior A)
    (e : Fin 3 → Basis (Fin 2) ℝ Plane) (t : Fin 3 → Fin 2 → ℝ)
    (ht : ∀ i k, 0 < t i k)
    (he : ∀ i k, e i k = t i k • normalizedNumeratorRay 1 1 i k)
    (hend : ∀ i k, IsRadialEndpoint A (e i k))
    (r : Plane) (hr : IsRecessionDirection (chordPolygon e) r) (hne : r ≠ 0) :
    2 ≤ normalizedSectorRatioSum A 1 1 := by
  have hfan (i : Fin 3) : chordSector (e i) = normalizedNumeratorSector 1 1 i :=
    chordSector_eq_normalized (by norm_num) (by norm_num) i (e i) (t i) (ht i) (he i)
  have hB := hA.linear_image fanCycle
  have hBzero := origin_mem_interior_linear_image hzero fanCycle
  have ht' := cycleScales_pos t ht
  have he' := cycleFan_scaled e t he
  have hend' := cycleFan_radial e hend
  have hr' := cycleFan_recession e hr
  rcases recession_mem_open_normalized_denominator 1 1 e hfan hr hne with h | h | h
  · have hpos := fanCycle_denominator_zero_to_two h.1 (by simpa using h.2)
    have hb := recession_firstQuadrant_ratio_sum hB hBzero (by norm_num) (by norm_num)
      (cycleFan e) (cycleScales t) ht' he' hend' (fanCycle r) hr' hpos.1 hpos.2
    rwa [normalizedSectorRatioSum_cycle] at hb
  · have hpos : 0 < fanCycle (fanCycle r) 0 ∧ 0 < fanCycle (fanCycle r) 1 := by
      simp only [fanCycle_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
      constructor <;> linarith [h.1, h.2]
    have hb := recession_firstQuadrant_ratio_sum (hB.linear_image fanCycle)
      (origin_mem_interior_linear_image hBzero fanCycle) (by norm_num) (by norm_num)
      (cycleFan (cycleFan e)) (cycleScales (cycleScales t))
      (cycleScales_pos _ ht') (cycleFan_scaled _ _ he') (cycleFan_radial _ hend')
      (fanCycle (fanCycle r)) (cycleFan_recession _ hr') hpos.1 hpos.2
    simpa only [normalizedSectorRatioSum_cycle] using hb
  · exact recession_firstQuadrant_ratio_sum hA hzero (by norm_num) (by norm_num)
      e t ht he hend r hr h.1 h.2

/-- The unbounded branch of Tsintsifas for the normalized radial fan. -/
theorem normalized_recession_ratio_sum {A : Set Plane} (hA : IsBody A)
    (hzero : (0 : Plane) ∈ interior A) {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (e : Fin 3 → Basis (Fin 2) ℝ Plane) (t : Fin 3 → Fin 2 → ℝ)
    (ht : ∀ i k, 0 < t i k)
    (he : ∀ i k, e i k = t i k • normalizedNumeratorRay a b i k)
    (hend : ∀ i k, IsRadialEndpoint A (e i k))
    (r : Plane) (hr : IsRecessionDirection (chordPolygon e) r) (hne : r ≠ 0) :
    2 ≤ normalizedSectorRatioSum A a b := by
  let E := fanDiagonal a b ha hb
  let e' : Fin 3 → Basis (Fin 2) ℝ Plane := fun i => (e i).map E.toLinearEquiv
  let t' : Fin 3 → Fin 2 → ℝ := fun i k => t i k * fanDiagonalRayFactor a b i k
  have ht' : ∀ i k, 0 < t' i k := fun i k =>
    mul_pos (ht i k) (fanDiagonalRayFactor_pos ha hb i k)
  have he' : ∀ i k, e' i k = t' i k • normalizedNumeratorRay 1 1 i k := by
    intro i k
    change E (e i k) = t' i k • normalizedNumeratorRay 1 1 i k
    rw [he i k, map_smul]
    dsimp [E, t']
    rw [fanDiagonal_ray, mul_smul]
  have hend' : ∀ i k, IsRadialEndpoint (E '' A) (e' i k) := fun i k =>
    (hend i k).linear_image E
  have hn : E r ≠ 0 := by intro hz; apply hne; exact E.injective (by simpa using hz)
  have hbound := canonical_recession_ratio_sum (hA.linear_image E)
    (origin_mem_interior_linear_image hzero E) e' t' ht' he' hend' (E r)
    (chordPolygon_recession_linear_image E e hr) hn
  rwa [normalizedSectorRatioSum_diagonal] at hbound

end ThreeSlices
