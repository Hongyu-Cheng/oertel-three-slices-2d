import ThreeSlices.Basic

open Set MeasureTheory Filter
open scoped Topology

namespace ThreeSlices

def Halfspace.enlarge (H : Halfspace) (ε : ℝ) : Halfspace :=
  { H with threshold := H.threshold + ε }

lemma cap_area_enlarge_tendsto (A : Bodies) (H : Halfspace) (i : Fin 3)
    (hA : IsCompact (A i)) :
    Tendsto (fun n : ℕ => area (A i ∩ (H.enlarge (1 / ((n : ℝ) + 1))).openCap i))
      atTop (𝓝 (area (A i ∩ H.closedCap i))) := by
  let F : ℕ → Set Plane := fun n => A i ∩ (H.enlarge (1 / ((n : ℝ) + 1))).openCap i
  have hm : Antitone F := by
    intro n m hnm x hx
    refine ⟨hx.1, ?_⟩
    have hε : 1 / ((m : ℝ) + 1) ≤ 1 / ((n : ℝ) + 1) :=
      one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.succ_le_succ hnm)
    have hxm := hx.2
    change H.planar x < H.threshold + 1 / ((m : ℝ) + 1) - H.height * (i : ℝ) at hxm
    change H.planar x < H.threshold + 1 / ((n : ℝ) + 1) - H.height * (i : ℝ)
    linarith
  have heq : (⋂ n, F n) = A i ∩ H.closedCap i := by
    ext x
    constructor
    · intro hx
      refine ⟨(mem_iInter.mp hx 0).1, ?_⟩
      change H.planar x ≤ H.threshold - H.height * (i : ℝ)
      by_contra h
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt
        (sub_pos.mpr (lt_of_not_ge h))
      have hxN := (mem_iInter.mp hx n).2
      change H.planar x < H.threshold + 1 / ((n : ℝ) + 1) - H.height * (i : ℝ) at hxN
      linarith
    · rintro ⟨hxA, hxH⟩
      apply mem_iInter.mpr
      intro n
      refine ⟨hxA, ?_⟩
      have hε : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
      change H.planar x ≤ H.threshold - H.height * (i : ℝ) at hxH
      change H.planar x < H.threshold + 1 / ((n : ℝ) + 1) - H.height * (i : ℝ)
      linarith
  have hfin := hA.measure_ne_top (μ := volume)
  have ht := tendsto_measure_iInter_atTop (μ := volume) (s := F)
    (fun n => (hA.measurableSet.inter
      ((H.enlarge (1 / ((n : ℝ) + 1))).isOpen_openCap i).measurableSet).nullMeasurableSet)
    hm ⟨0, measure_ne_top_of_subset inter_subset_left hfin⟩
  rw [heq] at ht
  simpa only [area, Measure.real, Function.comp_def, F] using
    (ENNReal.tendsto_toReal (measure_ne_top_of_subset inter_subset_left hfin)).comp ht

lemma enlarge_bad_halfspace (A : Bodies) (H : Halfspace)
    (hA : ∀ i, IsCompact (A i)) {β : ℝ} (hsmall : closedMass A H < β) :
    ∃ G : Halfspace, G.planar = H.planar ∧
      (∀ i, H.closedCap i ⊆ G.openCap i) ∧ openMass A G < β := by
  have ht : Tendsto (fun n : ℕ => openMass A (H.enlarge (1 / ((n : ℝ) + 1))))
      atTop (𝓝 (closedMass A H)) := by
    exact tendsto_finsetSum _ (fun i _ => cap_area_enlarge_tendsto A H i (hA i))
  obtain ⟨n, hn⟩ := (ht.eventually (eventually_lt_nhds hsmall)).exists
  refine ⟨H.enlarge (1 / ((n : ℝ) + 1)), rfl, ?_, hn⟩
  intro i x hx
  have hε : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
  change H.planar x ≤ H.threshold - H.height * (i : ℝ) at hx
  change H.planar x < H.threshold + 1 / ((n : ℝ) + 1) - H.height * (i : ℝ)
  linarith

lemma finite_bad_open_cover (A : Bodies) (hA : ∀ i, IsCompact (A i))
    (i : Fin 3) (β : ℝ)
    (hbad : ∀ x ∈ A i, ∃ H : Halfspace,
      H.planar ≠ 0 ∧ x ∈ H.closedCap i ∧ closedMass A H < β) :
    ∃ (ι : Type) (_ : Fintype ι) (G : ι → Halfspace),
      (∀ j, (G j).planar ≠ 0) ∧ A i ⊆ ⋃ j, (G j).openCap i ∧
        (∀ j, openMass A (G j) < β) := by
  classical
  have hh (x : A i) : ∃ G : Halfspace,
      G.planar ≠ 0 ∧ x.val ∈ G.openCap i ∧ openMass A G < β := by
    obtain ⟨H, hq, hx, hsmall⟩ := hbad x.val x.property
    obtain ⟨G, he, hsub, hG⟩ := enlarge_bad_halfspace A H hA hsmall
    exact ⟨G, by rwa [he], hsub i hx, hG⟩
  choose G hq hmem hsmall using hh
  have hcov : A i ⊆ ⋃ x : A i, (G x).openCap i := by
    intro x hx
    exact mem_iUnion.mpr ⟨⟨x, hx⟩, hmem ⟨x, hx⟩⟩
  obtain ⟨s, hs⟩ := (hA i).elim_finite_subcover (fun x : A i => (G x).openCap i)
    (fun x => (G x).isOpen_openCap i) hcov
  refine ⟨s, inferInstance, (fun j : s => G j.val), (fun j => hq j.val), ?_,
    (fun j => hsmall j.val)⟩
  intro x hx
  obtain ⟨j, hj, hcap⟩ := mem_iUnion₂.mp (hs hx)
  exact mem_iUnion.mpr ⟨⟨j, hj⟩, hcap⟩

end ThreeSlices
