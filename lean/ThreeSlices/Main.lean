import ThreeSlices.PairContradiction
import ThreeSlices.OpenCover
import ThreeSlices.Grunbaum

open Set MeasureTheory
open scoped BigOperators

namespace ThreeSlices

lemma closed_cap_le_mass (A : Bodies) (H : Halfspace) (i : Fin 3) :
    area (A i ∩ H.closedCap i) ≤ closedMass A H :=
  Finset.single_le_sum (fun j _ => area_nonneg (A j ∩ H.closedCap j)) (Finset.mem_univ i)

lemma open_cap_le_mass (A : Bodies) (H : Halfspace) (i : Fin 3) :
    area (A i ∩ H.openCap i) ≤ openMass A H :=
  Finset.single_le_sum (fun j _ => area_nonneg (A j ∩ H.openCap j)) (Finset.mem_univ i)

lemma horizontal_mass_lower (A : Bodies) (H : Halfspace) {x : Plane}
    (hnorm : totalArea A = 1) (h₀ : area (A 0) ≤ 1 / 2) (h₂ : area (A 2) ≤ 1 / 2)
    (hflat : H.planar = 0) (hx : x ∈ H.closedCap 1) :
    (1 / 2 : ℝ) ≤ closedMass A H := by
  have hc : H.height ≤ H.threshold := by
    simpa [Halfspace.closedCap, hflat, sub_nonneg] using hx
  have he₁ : H.closedCap 1 = univ := by
    ext y
    simp [Halfspace.closedCap, hflat, sub_nonneg, hc]
  unfold totalArea at hnorm
  rw [Fin.sum_univ_three] at hnorm
  by_cases hh : 0 ≤ H.height
  · have ht : 0 ≤ H.threshold := le_trans hh hc
    have he₀ : H.closedCap 0 = univ := by
      ext y
      simp [Halfspace.closedCap, hflat, ht]
    have hp := area_nonneg (A 2 ∩ H.closedCap 2)
    unfold closedMass
    rw [Fin.sum_univ_three, he₀, he₁, inter_univ, inter_univ]
    linarith
  · have ht : H.height * 2 ≤ H.threshold := by linarith
    have he₂ : H.closedCap 2 = univ := by
      ext y
      simp [Halfspace.closedCap, hflat, sub_nonneg, ht]
    have hp := area_nonneg (A 0 ∩ H.closedCap 0)
    unfold closedMass
    rw [Fin.sum_univ_three, he₁, he₂, inter_univ, inter_univ]
    linarith

/-- The entire non-large-slice case reduces to the precise planar covering lemma. -/
theorem middle_centerpoint_of_covering (hcover : PlanarCoveringStatement)
    (A : Bodies) (hA : ∀ i, IsBody (A i)) (hnorm : totalArea A = 1)
    (hcompat : Compatible A) (h₀ : area (A 0) ≤ 1 / 2) (h₂ : area (A 2) ≤ 1 / 2) :
    ∃ x ∈ A 1, ∀ H : Halfspace, x ∈ H.closedCap 1 → (2 / 9 : ℝ) ≤ closedMass A H := by
  classical
  by_contra h
  push Not at h
  have hbad : ∀ x ∈ A 1, ∃ H : Halfspace,
      H.planar ≠ 0 ∧ x ∈ H.closedCap 1 ∧ closedMass A H < (2 / 9 : ℝ) := by
    intro x hx
    obtain ⟨H, hxH, hsmall⟩ := h x hx
    refine ⟨H, ?_, hxH, hsmall⟩
    intro hz
    have hl := horizontal_mass_lower A H hnorm h₀ h₂ hz hxH
    linarith
  obtain ⟨ι, inst, G, hq, hcov, hmass⟩ :=
    finite_bad_open_cover A (fun i => (hA i).1) 1 (2 / 9) hbad
  let _ : Fintype ι := inst
  obtain ⟨r, s, hselect⟩ := hcover (A 1) (hA 1) (2 / 9) (by norm_num)
    ι inst G hq hcov (fun j => (open_cap_le_mass A (G j) 1).trans (hmass j).le)
  exact pair_contradiction A (G r) (G s) hA hnorm hcompat h₀ h₂ (hmass r) (hmass s) hselect

lemma large_slice_centerpoint (A : Bodies) (i : Fin 3)
    (hA : IsBody (A i)) (hlarge : (1 / 2 : ℝ) < area (A i)) :
    ∃ x ∈ A i, ∀ H : Halfspace, x ∈ H.closedCap i → (2 / 9 : ℝ) ≤ closedMass A H := by
  have hp : 0 < area (A i) := by linarith
  refine ⟨planarCentroid (A i), planarCentroid_mem hA hp, ?_⟩
  intro H hxH
  have hb := planarCentroid_closedCap_lower hA hp H i hxH
  have hl : (2 / 9 : ℝ) ≤ area (A i ∩ H.closedCap i) := by linarith
  exact hl.trans (closed_cap_le_mass A H i)

/-- Derive the normalized main theorem from the planar covering lemma. -/
theorem centerpoint_of_covering (hcover : PlanarCoveringStatement) : CenterpointStatement := by
  intro A hA hnorm hcompat
  by_cases h₀ : (1 / 2 : ℝ) < area (A 0)
  · obtain ⟨x, hx, hbound⟩ := large_slice_centerpoint A 0 (hA 0) h₀
    exact ⟨0, x, hx, hbound⟩
  by_cases h₂ : (1 / 2 : ℝ) < area (A 2)
  · obtain ⟨x, hx, hbound⟩ := large_slice_centerpoint A 2 (hA 2) h₂
    exact ⟨2, x, hx, hbound⟩
  obtain ⟨x, hx, hbound⟩ := middle_centerpoint_of_covering hcover A hA hnorm hcompat
    (le_of_not_gt h₀) (le_of_not_gt h₂)
  exact ⟨1, x, hx, hbound⟩

end ThreeSlices
