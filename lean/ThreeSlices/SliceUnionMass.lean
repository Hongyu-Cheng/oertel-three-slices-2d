import ThreeSlices.MixedInteger
import ThreeSlices.ConvexHullSlices

open Set

namespace ThreeSlices

lemma compact_sliceUnion (A : Bodies) (hA : ∀ i, IsCompact (A i)) :
    IsCompact (sliceUnion A) :=
  isCompact_iUnion fun i => isCompact_singleton.prod (hA i)

lemma sliceAt_sliceUnion_fin (A : Bodies) (i : Fin 3) :
    sliceAt (sliceUnion A) (i : ℝ) = A i := by
  ext x
  simp only [sliceAt, sliceUnion, mem_ofPred_eq, mem_iUnion, mem_prod, mem_singleton_iff]
  constructor
  · rintro ⟨j, hj, hx⟩
    have hji : j = i := by
      apply Fin.ext
      exact_mod_cast hj.symm
    simpa only [hji] using hx
  · intro hx
    exact ⟨i, rfl, hx⟩

lemma sliceAt_sliceUnion_int_empty_of_not_fin (A : Bodies) {z : ℤ}
    (hz : ¬ ∃ i : Fin 3, z = (i : ℤ)) :
    sliceAt (sliceUnion A) (z : ℝ) = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro x hx
  obtain ⟨i, hi⟩ := mem_iUnion.mp hx
  have hzi : (z : ℝ) = ((i : ℤ) : ℝ) := by simpa using hi.1
  exact hz ⟨i, by exact_mod_cast hzi⟩

@[simp] lemma sliceBodies_sliceUnion (A : Bodies) : sliceBodies (sliceUnion A) 0 = A := by
  funext i
  simpa [sliceBodies] using sliceAt_sliceUnion_fin A i

lemma mixedArea_sliceUnion (A : Bodies) (hA : ∀ i, IsCompact (A i)) :
    mixedArea (sliceUnion A) = totalArea A := by
  have hzero (z : ℤ) (hz : ¬ ∃ i : Fin 3, z = 0 + (i : ℤ)) :
      area (sliceAt (sliceUnion A) z) = 0 := by
    rw [sliceAt_sliceUnion_int_empty_of_not_fin A (by simpa using hz)]
    simp [area]
  simpa [sliceAt_sliceUnion_fin, totalArea] using
    mixedArea_eq_three_slices (compact_sliceUnion A hA) 0 hzero

lemma mixedArea_sliceUnion_inter_closedSet (A : Bodies) (hA : ∀ i, IsCompact (A i))
    (H : Halfspace) : mixedArea (sliceUnion A ∩ H.closedSet) = closedMass A H := by
  have hzero (z : ℤ) (hz : ¬ ∃ i : Fin 3, z = 0 + (i : ℤ)) :
      area (sliceAt (sliceUnion A) z) = 0 := by
    rw [sliceAt_sliceUnion_int_empty_of_not_fin A (by simpa using hz)]
    simp [area]
  simpa using mixedArea_inter_closedSet_eq (compact_sliceUnion A hA) 0 hzero H

end ThreeSlices
