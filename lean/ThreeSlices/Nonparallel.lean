import ThreeSlices.Trimming

open Set

namespace ThreeSlices

/-- The normals of two members of a proper three-halfplane cover are independent. -/
theorem Halfspace.normals_independent_of_proper_triple (H K L : Halfspace)
    (hH : H.planar ≠ 0)
    (hcover : H.openCap 1 ∪ K.openCap 1 ∪ L.openCap 1 = univ)
    (hHK : H.openCap 1 ∪ K.openCap 1 ≠ univ)
    (hHL : H.openCap 1 ∪ L.openCap 1 ≠ univ)
    (hKL : K.openCap 1 ∪ L.openCap 1 ≠ univ) :
    LinearIndependent ℝ ![H.planar, K.planar] := by
  classical
  apply (LinearIndependent.pair_iff' hH).mpr
  intro c he
  obtain ⟨p, hp⟩ := (ne_univ_iff_exists_notMem _).mp hKL
  obtain ⟨q, hq⟩ := (ne_univ_iff_exists_notMem _).mp hHL
  obtain ⟨r, hr⟩ := (ne_univ_iff_exists_notMem _).mp hHK
  have hpH : p ∈ H.openCap 1 := by
    have hc : p ∈ H.openCap 1 ∪ K.openCap 1 ∪ L.openCap 1 := hcover.symm ▸ mem_univ p
    rcases hc with (h | h) | h
    · exact h
    · exact False.elim (hp (Or.inl h))
    · exact False.elim (hp (Or.inr h))
  have hqK : q ∈ K.openCap 1 := by
    have hc : q ∈ H.openCap 1 ∪ K.openCap 1 ∪ L.openCap 1 := hcover.symm ▸ mem_univ q
    rcases hc with (h | h) | h
    · exact False.elim (hq (Or.inl h))
    · exact h
    · exact False.elim (hq (Or.inr h))
  have hpK : p ∉ K.openCap 1 := fun h => hp (Or.inl h)
  have hpL : p ∉ L.openCap 1 := fun h => hp (Or.inr h)
  have hqH : q ∉ H.openCap 1 := fun h => hq (Or.inl h)
  have hqL : q ∉ L.openCap 1 := fun h => hq (Or.inr h)
  have hrH : r ∉ H.openCap 1 := fun h => hr (Or.inl h)
  have hrK : r ∉ K.openCap 1 := fun h => hr (Or.inr h)
  have heval : ∀ x, c * H.planar x = K.planar x := by
    intro x
    simpa using congrArg (fun f : Plane →L[ℝ] ℝ => f x) he
  simp only [Halfspace.openCap, mem_ofPred_eq, not_lt] at hpH hpK hqH hqK hrH hrK
  rw [← heval p] at hpK
  rw [← heval q] at hqK
  rw [← heval r] at hrK
  have hpq : H.planar p < H.planar q := hpH.trans_le hqH
  have hc : c < 0 := by
    by_contra h
    have hm := mul_le_mul_of_nonneg_left hpq.le (le_of_not_gt h)
    linarith
  have hpr : H.planar p ≤ H.planar r := hpH.le.trans hrH
  have hrq : H.planar r ≤ H.planar q :=
    ((mul_lt_mul_left_of_neg hc).mp (hqK.trans_le hrK)).le
  have hmem : H.planar r ∈ segment ℝ (H.planar p) (H.planar q) := by
    rw [segment_eq_Icc hpq.le]
    exact ⟨hpr, hrq⟩
  have himage : H.planar r ∈ H.planar '' segment ℝ p q := by
    change H.planar r ∈ H.planar.toLinearMap.toAffineMap '' segment ℝ p q
    rw [image_segment]
    exact hmem
  obtain ⟨z, hzseg, hzH⟩ := himage
  have hzL : z ∉ L.openCap 1 :=
    (L.convex_compl_openCap 1).segment_subset hpL hqL hzseg
  have hznotH : z ∉ H.openCap 1 := by
    simp only [Halfspace.openCap, mem_ofPred_eq, not_lt]
    rw [hzH]
    exact hrH
  have hznotK : z ∉ K.openCap 1 := by
    simp only [Halfspace.openCap, mem_ofPred_eq, not_lt]
    rw [← heval z, hzH]
    exact hrK
  have hzcover : z ∈ H.openCap 1 ∪ K.openCap 1 ∪ L.openCap 1 := hcover.symm ▸ mem_univ z
  rcases hzcover with (hz | hz) | hz
  · exact hznotH hz
  · exact hznotK hz
  · exact hzL hz

end ThreeSlices
