import ThreeSlices.Basic

open Set MeasureTheory
open scoped ENNReal

namespace ThreeSlices

abbrev Space := ℝ × Plane

def sliceAt (C : Set Space) (z : ℝ) : Set Plane := {x | (z, x) ∈ C}

noncomputable def mixedVolume (C : Set Space) : ℝ≥0∞ :=
  ∑' z : ℤ, volume (sliceAt C z)

noncomputable def mixedArea (C : Set Space) : ℝ := (mixedVolume C).toReal

def Halfspace.closedSet (H : Halfspace) : Set Space :=
  {p | H.planar p.2 ≤ H.threshold - H.height * p.1}

def positiveSlices (C : Set Space) : Set ℤ := {z | 0 < area (sliceAt C z)}

lemma compact_sliceAt {C : Set Space} (hC : IsCompact C) (z : ℝ) :
    IsCompact (sliceAt C z) := by
  have hs : sliceAt C z = Prod.snd '' (C ∩ {p : Space | p.1 = z}) := by
    ext x
    constructor
    · intro hx
      exact ⟨(z, x), ⟨hx, rfl⟩, rfl⟩
    · rintro ⟨⟨t, x⟩, ⟨hx, ht⟩, rfl⟩
      change t = z at ht
      subst t
      exact hx
  rw [hs]
  exact (hC.inter_right (isClosed_eq continuous_fst continuous_const)).image continuous_snd

lemma convex_sliceAt {C : Set Space} (hC : Convex ℝ C) (z : ℝ) :
    Convex ℝ (sliceAt C z) :=
  hC.affine_preimage ((AffineMap.const ℝ Plane z).prod (AffineMap.id ℝ Plane))

lemma Halfspace.isClosed_closedSet (H : Halfspace) : IsClosed H.closedSet :=
  isClosed_le (H.planar.continuous.comp continuous_snd)
    (continuous_const.sub (continuous_const.mul continuous_fst))

lemma volume_sliceAt_ne_top {C : Set Space} (hC : IsCompact C) (z : ℝ) :
    volume (sliceAt C z) ≠ ⊤ := (compact_sliceAt hC z).measure_ne_top

lemma volume_sliceAt_eq_zero {C : Set Space} (hC : IsCompact C) (z : ℝ)
    (hz : area (sliceAt C z) = 0) : volume (sliceAt C z) = 0 := by
  exact ((ENNReal.toReal_eq_zero_iff _).mp hz).resolve_right (volume_sliceAt_ne_top hC z)

lemma mixedVolume_eq_three_slices {C : Set Space} (hC : IsCompact C) (k : ℤ)
    (hzero : ∀ z : ℤ, (¬ ∃ i : Fin 3, z = k + (i : ℤ)) →
      area (sliceAt C z) = 0) :
    mixedVolume C = ∑ i : Fin 3, volume (sliceAt C (k + (i : ℤ))) := by
  have hinj : Function.Injective (fun i : Fin 3 => k + (i : ℤ)) := by
    intro i j hij
    exact Fin.ext (Int.ofNat.inj (add_left_cancel hij))
  have hs : Function.support (fun z : ℤ => volume (sliceAt C z)) ⊆
      Set.range (fun i : Fin 3 => k + (i : ℤ)) := by
    intro z hz
    by_contra hzr
    exact hz (volume_sliceAt_eq_zero hC z (hzero z (by simpa [eq_comm] using hzr)))
  simpa only [mixedVolume, Int.cast_add] using
    (hinj.tsum_eq hs).symm.trans
      (tsum_fintype fun i : Fin 3 => volume (sliceAt C ((k + (i : ℤ) : ℤ) : ℝ)))

lemma mixedArea_eq_three_slices {C : Set Space} (hC : IsCompact C) (k : ℤ)
    (hzero : ∀ z : ℤ, (¬ ∃ i : Fin 3, z = k + (i : ℤ)) →
      area (sliceAt C z) = 0) :
    mixedArea C = ∑ i : Fin 3, area (sliceAt C (k + (i : ℤ))) := by
  unfold mixedArea
  rw [mixedVolume_eq_three_slices hC k hzero]
  exact ENNReal.toReal_sum fun i _ => volume_sliceAt_ne_top hC _

end ThreeSlices
