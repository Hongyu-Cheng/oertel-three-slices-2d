import ThreeSlices.Basic
import ThreeSlices.Algebra

open Set MeasureTheory
open scoped Pointwise

namespace ThreeSlices

def trimmed (A : Bodies) (H G : Halfspace) (i : Fin 3) : Set Plane :=
  A i \ (H.openCap i ∪ G.openCap i)

lemma trimmed_subset (A : Bodies) (H G : Halfspace) (i : Fin 3) :
    trimmed A H G i ⊆ A i := sdiff_subset

lemma trimmed_compact (A : Bodies) (H G : Halfspace) (i : Fin 3)
    (hA : IsCompact (A i)) : IsCompact (trimmed A H G i) :=
  hA.inter_right ((H.isOpen_openCap i).union (G.isOpen_openCap i)).isClosed_compl

lemma Halfspace.convex_compl_openCap (H : Halfspace) (i : Fin 3) :
    Convex ℝ (H.openCap i)ᶜ := by
  simpa [Halfspace.openCap, Set.preimage, compl_ofPred] using
    (convex_Ici (H.threshold - H.height * (i : ℝ))).linear_preimage H.planar.toLinearMap

lemma Halfspace.keep_midpoint (H : Halfspace) {x y : Plane}
    (hx : x ∉ H.openCap 0) (hy : y ∉ H.openCap 2) :
    (1 / 2 : ℝ) • x + (1 / 2 : ℝ) • y ∉ H.openCap 1 := by
  simp [Halfspace.openCap] at hx hy ⊢
  norm_num at *
  linarith

lemma trimmed_compatible (A : Bodies) (H G : Halfspace) (hA : Compatible A) :
    Compatible (trimmed A H G) := by
  rintro _ ⟨_, ⟨x, hx, rfl⟩, _, ⟨y, hy, rfl⟩, rfl⟩
  refine ⟨hA ⟨_, ⟨x, hx.1, rfl⟩, _, ⟨y, hy.1, rfl⟩, rfl⟩, ?_⟩
  exact fun h => h.elim
    (H.keep_midpoint (fun h => hx.2 (Or.inl h)) (fun h => hy.2 (Or.inl h)))
    (G.keep_midpoint (fun h => hx.2 (Or.inr h)) (fun h => hy.2 (Or.inr h)))

lemma positive_area_interior {A : Set Plane} (hc : Convex ℝ A) (hp : 0 < area A) :
    (interior A).Nonempty := by
  by_contra h
  have hspan : affineSpan ℝ A ≠ ⊤ := by
    intro he
    exact h (hc.interior_nonempty_iff_affineSpan_eq_top.mpr he)
  have hz : volume A = 0 := measure_mono_null (subset_affineSpan ℝ A)
    (Measure.addHaar_affineSubspace volume (affineSpan ℝ A) hspan)
  simp [area, Measure.real, hz] at hp

lemma slice_inclusion_exclusion (A : Bodies) (H G : Halfspace) (i : Fin 3)
    (hA : IsCompact (A i)) :
    area (A i ∩ H.openCap i) + area (A i ∩ G.openCap i) =
      area (A i) - area (trimmed A H G i) + area (A i ∩ H.openCap i ∩ G.openCap i) := by
  have hfin := hA.measure_ne_top (μ := volume)
  have hH := (H.isOpen_openCap i).measurableSet
  have hG := (G.isOpen_openCap i).measurableSet
  have hp := measureReal_inter_add_sdiff (μ := volume) (s := A i) (hH.union hG) hfin
  have hu := measureReal_union_add_inter (μ := volume) (s := A i ∩ H.openCap i)
    (hA.measurableSet.inter hG)
    (measure_ne_top_of_subset inter_subset_left hfin)
    (measure_ne_top_of_subset inter_subset_left hfin)
  rw [inter_union_distrib_left] at hp
  have he : (A i ∩ H.openCap i) ∩ (A i ∩ G.openCap i) = A i ∩ H.openCap i ∩ G.openCap i := by
    ext x
    simp only [mem_inter_iff]
    tauto
  rw [he] at hu
  change volume.real (A i ∩ H.openCap i) + volume.real (A i ∩ G.openCap i) =
    volume.real (A i) - volume.real (A i \ (H.openCap i ∪ G.openCap i)) +
      volume.real (A i ∩ H.openCap i ∩ G.openCap i)
  linarith

end ThreeSlices
