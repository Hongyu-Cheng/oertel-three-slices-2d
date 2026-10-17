import ThreeSlices.Trimming

open Set MeasureTheory
open scoped BigOperators

namespace ThreeSlices

lemma pair_mass_eq (A : Bodies) (H G : Halfspace) (hA : ∀ i, IsCompact (A i)) :
    openMass A H + openMass A G = totalArea A - ∑ i, area (trimmed A H G i) +
      ∑ i, area (A i ∩ H.openCap i ∩ G.openCap i) := by
  unfold openMass totalArea
  rw [← Finset.sum_add_distrib]
  calc
    _ = ∑ i, (area (A i) - area (trimmed A H G i) +
        area (A i ∩ H.openCap i ∩ G.openCap i)) :=
      Finset.sum_congr rfl (fun i _ => slice_inclusion_exclusion A H G i (hA i))
    _ = _ := by rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]

/-- Section 3's contradiction for compact convex slices and two small halfspaces. -/
theorem pair_contradiction (A : Bodies) (H G : Halfspace)
    (hA : ∀ i, IsBody (A i)) (hnorm : totalArea A = 1) (hcompat : Compatible A)
    (h₀ : area (A 0) ≤ 1 / 2) (h₂ : area (A 2) ≤ 1 / 2)
    (hH : openMass A H < 2 / 9) (hG : openMass A G < 2 / 9)
    (hselect : area (trimmed A H G 1) ^ 2 ≤
      (2 / 9 : ℝ) * area (A 1 ∩ H.openCap 1 ∩ G.openCap 1)) : False := by
  let u := area (trimmed A H G 0)
  let v := area (trimmed A H G 2)
  let σ := area (trimmed A H G 1)
  let τ := area (A 1 ∩ H.openCap 1 ∩ G.openCap 1)
  have hu : u ≤ 1 / 2 := (area_mono (trimmed_subset A H G 0) (hA 0).1).trans h₀
  have hv : v ≤ 1 / 2 := (area_mono (trimmed_subset A H G 2) (hA 2).1).trans h₂
  have hτ : (9 / 2 : ℝ) * σ ^ 2 ≤ τ := by
    dsimp [σ, τ]
    nlinarith [hselect]
  have hid := pair_mass_eq A H G (fun i => (hA i).1)
  rw [hnorm, Fin.sum_univ_three, Fin.sum_univ_three] at hid
  have hn : (5 / 9 : ℝ) + τ - σ < u + v := by
    have ha := area_nonneg (A 0 ∩ H.openCap 0 ∩ G.openCap 0)
    have hb := area_nonneg (A 2 ∩ H.openCap 2 ∩ G.openCap 2)
    dsimp [u, v, σ, τ]
    linarith
  have hsum : (1 / 2 : ℝ) < u + v := by
    nlinarith [sq_nonneg (σ - 1 / 9)]
  have hup : 0 < u := by linarith
  have hvp : 0 < v := by linarith
  have hbm := planar_midpoint_area
    (trimmed_compact A H G 0 (hA 0).1)
    (trimmed_compact A H G 1 (hA 1).1)
    (trimmed_compact A H G 2 (hA 2).1)
    (nonempty_of_measureReal_ne_zero hup.ne')
    (nonempty_of_measureReal_ne_zero hvp.ne')
    (trimmed_compatible A H G hcompat)
  exact final_contradiction_sqrt u v σ τ (area_nonneg _) (area_nonneg _)
    (area_nonneg _) hu hv hτ hn hbm

end ThreeSlices
