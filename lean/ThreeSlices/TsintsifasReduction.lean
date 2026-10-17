import ThreeSlices.NormalizedCovering
import ThreeSlices.SectorBoundary
import ThreeSlices.SectorPositivity
import ThreeSlices.SixRayConstruction

open Set MeasureTheory Module

namespace ThreeSlices

noncomputable def normalizedSectorRatioSum (A : Set Plane) (a b : ℝ) : ℝ :=
  ∑ i : Fin 3, area (A ∩ normalizedNumeratorSector a b i) /
    area (A ∩ normalizedDenominatorSector a b i)

lemma normalizedSectorRatioSum_eq {A : Set Plane} {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    normalizedSectorRatioSum A a b =
      area (A ∩ {x | x 1 < 0} ∩ {x | 0 ≤ a * x 0 + b * x 1}) /
        area (A \ ({x | x 1 < 0} ∪ {x | 0 ≤ a * x 0 + b * x 1})) +
      area (A ∩ {x | 0 ≤ a * x 0 + b * x 1} ∩ {x | x 0 < 0}) /
        area (A \ ({x | 0 ≤ a * x 0 + b * x 1} ∪ {x | x 0 < 0})) +
      area (A ∩ {x | x 0 < 0} ∩ {x | x 1 < 0}) /
        area (A \ ({x | x 0 < 0} ∪ {x | x 1 < 0})) := by
  obtain ⟨h₀, h₁, h₂, h₃, h₄, h₅⟩ := normalized_sector_areas_eq_closed (A := A) ha hb
  simp only [normalizedSectorRatioSum, Fin.sum_univ_three]
  simp only [normalizedNumeratorSector, normalizedDenominatorSector, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  rw [← h₀, ← h₁, ← h₂, ← h₃, ← h₄, ← h₅]

theorem normalized_tsintsifas_of_closed_ratios
    (h : ∀ (A : Set Plane), IsBody A → (0 : Plane) ∈ interior A →
      ∀ a b : ℝ, 0 < a → 0 < b → (3 / 2 : ℝ) ≤ normalizedSectorRatioSum A a b) :
    NormalizedTsintsifasStatement := by
  intro A hA hzero a b ha hb
  simpa only [normalizedSectorRatioSum_eq ha hb] using h A hA hzero a b ha hb

theorem normalized_denominator_area_pos {A : Set Plane} (hA : IsCompact A)
    (hzero : (0 : Plane) ∈ interior A) {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (i : Fin 3) : 0 < area (A ∩ normalizedDenominatorSector a b i) := by
  obtain ⟨_, hpp, hxp, hyp, _, _⟩ := normalized_strict_sector_areas_pos hA hzero ha hb
  have hf (S : Set Plane) : volume (A ∩ S) ≠ ⊤ :=
    measure_ne_top_of_subset inter_subset_left (hA.measure_ne_top (μ := volume))
  fin_cases i
  · apply hyp.trans_le
    apply measureReal_mono _ (hf _)
    intro x hx
    exact ⟨hx.1, hx.2.1.le, hx.2.2.le⟩
  · apply hxp.trans_le
    apply measureReal_mono _ (hf _)
    intro x hx
    exact ⟨hx.1, hx.2.1.le, hx.2.2.le⟩
  · apply hpp.trans_le
    apply measureReal_mono _ (hf _)
    intro x hx
    exact ⟨hx.1, hx.2.1.le, hx.2.2.le⟩

/-- The bounded chord replacement decreases the sum of the three ratios. -/
theorem normalized_chord_ratio_le {A : Set Plane} (hA : IsBody A)
    (hzero : (0 : Plane) ∈ interior A) {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (e : Fin 3 → Basis (Fin 2) ℝ Plane) (hP : IsCompact (chordPolygon e))
    (hend : ∀ i k, IsRadialEndpoint A (e i k))
    (hclosed : ∀ i, chordSector (e i) = normalizedNumeratorSector a b i)
    (hopen : ∀ i, openChordSector (e i) = normalizedOpenNumeratorSector a b i) :
    normalizedSectorRatioSum (chordPolygon e) a b ≤ normalizedSectorRatioSum A a b := by
  apply Finset.sum_le_sum
  intro i _
  have hD : normalizedDenominatorSector a b i ⊆ (⋃ j, openChordSector (e j))ᶜ := by
    simpa only [hopen] using normalizedDenominatorSector_avoids_openNumerators a b i
  simpa only [hclosed] using chordPolygon_sector_ratio_le hA.1 hA.2.1
    (interior_subset hzero) e hP (fun j => ⟨hend j 0, hend j 1⟩) hD i
    (normalized_denominator_area_pos hA.1 hzero ha hb i)

lemma scaled_normalized_ray_avoids_open_sectors {a b t : ℝ}
    (ha : 0 < a) (hb : 0 < b) (ht : 0 < t) (i : Fin 3) (k : Fin 2) (j : Fin 3) :
    t • normalizedNumeratorRay a b i k ∉ normalizedOpenNumeratorSector a b j := by
  have hat := mul_pos ht ha
  have hbt := mul_pos ht hb
  fin_cases i <;> fin_cases k <;> fin_cases j <;>
    simp [normalizedNumeratorRay, normalizedOpenNumeratorSector,
      PiLp.smul_apply, smul_eq_mul] <;> intro h <;> nlinarith

/-- The six original radial endpoints remain feasible after all three chord cuts. -/
theorem normalized_radial_endpoints_mem_chordPolygon {A : Set Plane} (hA : Convex ℝ A)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (e : Fin 3 → Basis (Fin 2) ℝ Plane) (t : Fin 3 → Fin 2 → ℝ)
    (ht : ∀ i k, 0 < t i k)
    (he : ∀ i k, e i k = t i k • normalizedNumeratorRay a b i k)
    (hend : ∀ i k, IsRadialEndpoint A (e i k)) (i : Fin 3) (k : Fin 2) :
    e i k ∈ chordPolygon e := by
  apply mem_iInter.mpr
  intro j
  apply body_diff_openSector_subset_chordHalfplane hA (e j) (hend j 0) (hend j 1)
  refine ⟨(hend i k).1, ?_⟩
  rw [openChordSector_eq_normalized ha hb j (e j) (t j) (ht j) (he j), he i k]
  exact scaled_normalized_ray_avoids_open_sectors ha hb (ht i k) i k j

theorem origin_mem_interior_chordPolygon (e : Fin 3 → Basis (Fin 2) ℝ Plane) :
    (0 : Plane) ∈ interior (chordPolygon e) := by
  let U : Set Plane := ⋂ i, {x | (e i).repr x 0 + (e i).repr x 1 < 1}
  have hU : IsOpen U := isOpen_iInter_of_finite fun i =>
    isOpen_lt (((e i).coord 0).continuous_of_finiteDimensional.add
      ((e i).coord 1).continuous_of_finiteDimensional) continuous_const
  have hsub : U ⊆ chordPolygon e := by
    intro x hx
    apply mem_iInter.mpr
    intro i
    have hi : (e i).repr x 0 + (e i).repr x 1 < 1 := mem_iInter.mp hx i
    exact hi.le
  apply interior_mono hsub
  rw [hU.interior_eq]
  exact mem_iInter.mpr fun _ => by simp

lemma IsBody.linear_image {A : Set Plane} (hA : IsBody A) (E : Plane ≃L[ℝ] Plane) :
    IsBody (E '' A) :=
  ⟨hA.1.image E.continuous, hA.2.1.linear_image E.toLinearMap, hA.2.2.image E⟩

lemma origin_mem_interior_linear_image {A : Set Plane}
    (hzero : (0 : Plane) ∈ interior A) (E : Plane ≃L[ℝ] Plane) :
    (0 : Plane) ∈ interior (E '' A) := by
  change (0 : Plane) ∈ interior (E.toHomeomorph '' A)
  rw [← E.toHomeomorph.image_interior]
  exact ⟨0, hzero, map_zero E⟩

lemma chordPolygon_linear_image {ι : Type*} (E : Plane ≃L[ℝ] Plane)
    (e : ι → Basis (Fin 2) ℝ Plane) :
    E '' chordPolygon e = chordPolygon (fun i => (e i).map E.toLinearEquiv) := by
  rw [ContinuousLinearEquiv.image_eq_preimage_symm]
  ext y
  simp only [chordPolygon, mem_preimage, mem_iInter, chordHalfplane, mem_ofPred_eq]
  rfl

lemma chordPolygon_recession_linear_image {ι : Type*} (E : Plane ≃L[ℝ] Plane)
    (e : ι → Basis (Fin 2) ℝ Plane) {r : Plane}
    (hr : IsRecessionDirection (chordPolygon e) r) :
    IsRecessionDirection (chordPolygon (fun i => (e i).map E.toLinearEquiv)) (E r) := by
  rw [← chordPolygon_linear_image]
  rintro y ⟨x, hx, rfl⟩ t ht
  exact ⟨x + t • r, hr x hx t ht, by simp⟩

lemma chordHalfplane_swap (e : Basis (Fin 2) ℝ Plane) :
    chordHalfplane (e.reindex (Equiv.swap 0 1)) = chordHalfplane e := by
  ext x
  change e.repr x 1 + e.repr x 0 ≤ 1 ↔ e.repr x 0 + e.repr x 1 ≤ 1
  rw [add_comm]

end ThreeSlices
