import ThreeSlices.MixedIntegerBasic
import ThreeSlices.ConsecutiveSlices
import ThreeSlices.Scaling

open Set MeasureTheory
open scoped Pointwise

namespace ThreeSlices

def sliceBodies (C : Set Space) (k : ℤ) : Bodies :=
  fun i => sliceAt C (k + (i : ℤ))

def Halfspace.shiftHeight (H : Halfspace) (k : ℤ) : Halfspace :=
  { H with threshold := H.threshold - H.height * (k : ℝ) }

lemma Halfspace.mem_shiftHeight_closedCap (H : Halfspace) (k : ℤ) (i : Fin 3) (x : Plane) :
    x ∈ (H.shiftHeight k).closedCap i ↔ (((k + (i : ℤ)) : ℝ), x) ∈ H.closedSet := by
  simp [Halfspace.shiftHeight, Halfspace.closedCap, Halfspace.closedSet, mul_add, sub_sub]

lemma sliceBodies_compatible {C : Set Space} (hC : Convex ℝ C) (k : ℤ) :
    Compatible (sliceBodies C k) := by
  rintro _ ⟨_, ⟨x, hx, rfl⟩, _, ⟨y, hy, rfl⟩, rfl⟩
  have hm := hC hx hy (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) + 1 / 2 = 1)
  change (((k + ((1 : Fin 3) : ℤ)) : ℝ), (1 / 2 : ℝ) • x + (1 / 2 : ℝ) • y) ∈ C
  convert hm using 1
  ext
  · norm_num
    ring
  · rfl

@[simp] lemma Halfspace.shiftHeight_zero (H : Halfspace) : H.shiftHeight 0 = H := by
  cases H
  simp [Halfspace.shiftHeight]

lemma mixedArea_inter_closedSet_eq {C : Set Space} (hcompact : IsCompact C) (k : ℤ)
    (hzero : ∀ z : ℤ, (¬ ∃ i : Fin 3, z = k + (i : ℤ)) → area (sliceAt C z) = 0)
    (H : Halfspace) : mixedArea (C ∩ H.closedSet) =
      closedMass (sliceBodies C k) (H.shiftHeight k) := by
  have hCH := hcompact.inter_right H.isClosed_closedSet
  have hzeroH (z : ℤ) (hz : ¬ ∃ i : Fin 3, z = k + (i : ℤ)) :
      area (sliceAt (C ∩ H.closedSet) z) = 0 := by
    apply le_antisymm _ (area_nonneg _)
    calc
      area (sliceAt (C ∩ H.closedSet) z) ≤ area (sliceAt C z) :=
        area_mono (fun _ h => h.1) (compact_sliceAt hcompact z)
      _ = 0 := hzero z hz
  rw [mixedArea_eq_three_slices hCH k hzeroH]
  apply Finset.sum_congr rfl
  intro j _
  apply congrArg area
  ext y
  change (y ∈ sliceBodies C k j ∧ (((k + (j : ℤ)) : ℝ), y) ∈ H.closedSet) ↔
    (y ∈ sliceBodies C k j ∧ y ∈ (H.shiftHeight k).closedCap j)
  rw [H.mem_shiftHeight_closedCap]

/-- The mixed-integer assertion of Theorem 1, with exactly three positive-area integer slices. -/
def MixedIntegerCenterpointStatement : Prop :=
  ∀ C : Set Space, IsCompact C → Convex ℝ C → (positiveSlices C).ncard = 3 →
    ∃ z : ℤ, ∃ x : Plane, ((z : ℝ), x) ∈ C ∧ ∀ H : Halfspace,
      ((z : ℝ), x) ∈ H.closedSet → (2 / 9 : ℝ) * mixedArea C ≤ mixedArea (C ∩ H.closedSet)

/-- The mixed-integer conclusion, including any additional zero-area integer slices. -/
theorem mixed_integer_centerpoint : MixedIntegerCenterpointStatement := by
  intro C hcompact hconvex hcard
  obtain ⟨k, hk⟩ := positiveSlices_consecutive hcompact hconvex hcard
  have hpos (i : Fin 3) : 0 < area (sliceBodies C k i) := by
    simpa [sliceBodies, Int.cast_add] using (hk (k + (i : ℤ))).mpr ⟨i, rfl⟩
  have hbody (i : Fin 3) : IsBody (sliceBodies C k i) := by
    refine ⟨compact_sliceAt hcompact _, convex_sliceAt hconvex _, ?_⟩
    by_contra h
    have he : sliceBodies C k i = ∅ := Set.not_nonempty_iff_eq_empty.mp h
    simpa [he, area] using hpos i
  have hzero (z : ℤ) (hz : ¬ ∃ i : Fin 3, z = k + (i : ℤ)) :
      area (sliceAt C z) = 0 :=
    le_antisymm (le_of_not_gt fun hp => hz ((hk z).mp hp)) (area_nonneg _)
  have hmass : mixedArea C = totalArea (sliceBodies C k) :=
    mixedArea_eq_three_slices hcompact k hzero
  obtain ⟨i, x, hx, hpoint⟩ := centerpoint_unnormalized (sliceBodies C k) hbody
    (sliceBodies_compatible hconvex k)
  refine ⟨k + (i : ℤ), x, ?_, ?_⟩
  · simpa [sliceBodies, sliceAt, Int.cast_add] using hx
  intro H hH
  rw [hmass, mixedArea_inter_closedSet_eq hcompact k hzero H]
  exact hpoint (H.shiftHeight k)
    ((H.mem_shiftHeight_closedCap k i x).mpr (by simpa [Int.cast_add] using hH))

end ThreeSlices
