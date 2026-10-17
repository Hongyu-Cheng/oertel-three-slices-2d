import ThreeSlices.Basic
import ThreeSlices.SectorSelection

open Set MeasureTheory

namespace ThreeSlices

/-- One cap consists of its singly covered sector and its two pairwise overlaps. -/
lemma cap_area_decomposition {A U V W : Set Plane} (hA : IsCompact A)
    (hU : MeasurableSet U) (hV : MeasurableSet V) (hW : MeasurableSet W)
    (hcover : A ⊆ U ∪ V ∪ W) (htriple : A ∩ U ∩ V ∩ W = ∅) :
    area (A ∩ U) = area (A \ (V ∪ W)) +
      area (A ∩ U ∩ V) + area (A ∩ U ∩ W) := by
  have he : A ∩ U = (A \ (V ∪ W) ∪ (A ∩ U ∩ V)) ∪ (A ∩ U ∩ W) := by
    ext x
    have hc : x ∈ A → (x ∈ U ∨ x ∈ V) ∨ x ∈ W := fun hx => hcover hx
    simp only [mem_inter_iff, mem_union, mem_sdiff]
    constructor
    · tauto
    · intro hx
      have ha : x ∈ A := by tauto
      have hh := hc ha
      tauto
  have hd₁ : Disjoint (A \ (V ∪ W)) (A ∩ U ∩ V) := by
    rw [Set.disjoint_left]
    intro x hx hy
    exact hx.2 (Or.inl hy.2)
  have hd₂ : Disjoint (A \ (V ∪ W) ∪ (A ∩ U ∩ V)) (A ∩ U ∩ W) := by
    rw [Set.disjoint_left]
    intro x hx hy
    rcases hx with hx | hx
    · exact hx.2 (Or.inr hy.2)
    · have hm : x ∈ A ∩ U ∩ V ∩ W := ⟨hx, hy.2⟩
      rw [htriple] at hm
      exact hm
  have hf := hA.measure_ne_top (μ := volume)
  have hf₀ : volume (A \ (V ∪ W)) ≠ ⊤ := measure_ne_top_of_subset sdiff_subset hf
  have hf₁ : volume (A ∩ U ∩ V) ≠ ⊤ :=
    measure_ne_top_of_subset (inter_subset_left.trans inter_subset_left) hf
  have hf₂ : volume (A ∩ U ∩ W) ≠ ⊤ :=
    measure_ne_top_of_subset (inter_subset_left.trans inter_subset_left) hf
  have hfu : volume (A \ (V ∪ W) ∪ (A ∩ U ∩ V)) ≠ ⊤ := by
    apply measure_ne_top_of_subset _ hf
    exact union_subset sdiff_subset (inter_subset_left.trans inter_subset_left)
  unfold area
  conv_lhs => rw [he]
  rw [measureReal_union hd₂ ((hA.measurableSet.inter hU).inter hW) hfu hf₂,
    measureReal_union hd₁ ((hA.measurableSet.inter hU).inter hV) hf₀ hf₁]

/-- Counting measurable sectors with multiplicities one and two. -/
theorem sector_area_budget {A U V W : Set Plane} (hA : IsCompact A)
    (hU : MeasurableSet U) (hV : MeasurableSet V) (hW : MeasurableSet W)
    (hcover : A ⊆ U ∪ V ∪ W) (htriple : A ∩ U ∩ V ∩ W = ∅)
    (β : ℝ) (hu : area (A ∩ U) ≤ β) (hv : area (A ∩ V) ≤ β)
    (hw : area (A ∩ W) ≤ β) :
    area (A \ (V ∪ W)) + area (A \ (W ∪ U)) + area (A \ (U ∪ V)) +
      2 * (area (A ∩ V ∩ W) + area (A ∩ W ∩ U) + area (A ∩ U ∩ V)) ≤ 3 * β := by
  have hvcover : A ⊆ V ∪ W ∪ U := by
    intro x hx
    have := hcover hx
    simp only [mem_union] at this ⊢
    tauto
  have hwcover : A ⊆ W ∪ U ∪ V := by
    intro x hx
    have := hcover hx
    simp only [mem_union] at this ⊢
    tauto
  have hvtriple : A ∩ V ∩ W ∩ U = ∅ := by
    simpa only [inter_assoc, inter_left_comm, inter_comm] using htriple
  have hwtriple : A ∩ W ∩ U ∩ V = ∅ := by
    simpa only [inter_assoc, inter_left_comm, inter_comm] using htriple
  have hu' := cap_area_decomposition hA hU hV hW hcover htriple
  have hv' := cap_area_decomposition hA hV hW hU hvcover hvtriple
  have hw' := cap_area_decomposition hA hW hU hV hwcover hwtriple
  have huv : A ∩ U ∩ V = A ∩ V ∩ U := by rw [inter_right_comm]
  have hvw : A ∩ V ∩ W = A ∩ W ∩ V := by rw [inter_right_comm]
  have hwu : A ∩ W ∩ U = A ∩ U ∩ W := by rw [inter_right_comm]
  rw [← huv] at hv'
  rw [← hvw] at hw'
  rw [← hwu] at hu'
  linarith

/-- A selected pair remains valid after either cap is enlarged. -/
theorem pair_bound_of_enlargement {A U V U' V' : Set Plane} (hA : IsCompact A)
    (hU : U ⊆ U') (hV : V ⊆ V') {β : ℝ} (hβ : 0 ≤ β)
    (hbound : area (A \ (U ∪ V)) ^ 2 ≤ β * area (A ∩ U ∩ V)) :
    area (A \ (U' ∪ V')) ^ 2 ≤ β * area (A ∩ U' ∩ V') := by
  have hf := hA.measure_ne_top (μ := volume)
  have hσ : area (A \ (U' ∪ V')) ≤ area (A \ (U ∪ V)) := by
    exact measureReal_mono (sdiff_subset_sdiff_right (union_subset_union hU hV))
      (measure_ne_top_of_subset sdiff_subset hf)
  have hτ : area (A ∩ U ∩ V) ≤ area (A ∩ U' ∩ V') := by
    exact measureReal_mono (inter_subset_inter (inter_subset_inter subset_rfl hU) hV)
      (measure_ne_top_of_subset (inter_subset_left.trans inter_subset_left) hf)
  have hsquare : area (A \ (U' ∪ V')) ^ 2 ≤ area (A \ (U ∪ V)) ^ 2 := by
    nlinarith [area_nonneg (A \ (U' ∪ V')), area_nonneg (A \ (U ∪ V))]
  exact hsquare.trans (hbound.trans (mul_le_mul_of_nonneg_left hτ hβ))

/-- The measure-theoretic and selection steps of Lemma 2, including zero-area sectors. -/
theorem sector_pair_of_ratio {A U V W : Set Plane} (hA : IsCompact A)
    (hU : MeasurableSet U) (hV : MeasurableSet V) (hW : MeasurableSet W)
    (hcover : A ⊆ U ∪ V ∪ W) (htriple : A ∩ U ∩ V ∩ W = ∅)
    (β : ℝ) (hβ : 0 < β) (hu : area (A ∩ U) ≤ β)
    (hv : area (A ∩ V) ≤ β) (hw : area (A ∩ W) ≤ β)
    (hratio : (3 / 2 : ℝ) ≤ area (A ∩ V ∩ W) / area (A \ (V ∪ W)) +
      area (A ∩ W ∩ U) / area (A \ (W ∪ U)) +
      area (A ∩ U ∩ V) / area (A \ (U ∪ V))) :
    area (A \ (V ∪ W)) ^ 2 ≤ β * area (A ∩ V ∩ W) ∨
    area (A \ (W ∪ U)) ^ 2 ≤ β * area (A ∩ W ∩ U) ∨
    area (A \ (U ∪ V)) ^ 2 ≤ β * area (A ∩ U ∩ V) := by
  let σ : Fin 3 → ℝ := ![area (A \ (V ∪ W)), area (A \ (W ∪ U)),
    area (A \ (U ∪ V))]
  let τ : Fin 3 → ℝ := ![area (A ∩ V ∩ W), area (A ∩ W ∩ U), area (A ∩ U ∩ V)]
  have hσ : ∀ i, 0 ≤ σ i := by intro i; fin_cases i <;> exact area_nonneg _
  have hτ : ∀ i, 0 ≤ τ i := by intro i; fin_cases i <;> exact area_nonneg _
  have hex : ∃ i, σ i ^ 2 ≤ β * τ i := by
    by_cases hs : ∀ i, 0 < σ i
    · apply sector_selection β hβ σ τ hs hτ
      · have hb := sector_area_budget hA hU hV hW hcover htriple β hu hv hw
        simp [Fin.sum_univ_three, σ, τ]
        linarith
      · simpa [Fin.sum_univ_three, σ, τ] using hratio
    · push Not at hs
      obtain ⟨i, hi⟩ := hs
      refine ⟨i, ?_⟩
      have hz : σ i = 0 := le_antisymm hi (hσ i)
      rw [hz, zero_pow (by norm_num : 2 ≠ 0)]
      exact mul_nonneg hβ.le (hτ i)
  obtain ⟨i, hi⟩ := hex
  fin_cases i
  · exact Or.inl hi
  · exact Or.inr (Or.inl hi)
  · exact Or.inr (Or.inr hi)

end ThreeSlices
