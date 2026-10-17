import ThreeSlices.MixedIntegerBasic

open Set

namespace ThreeSlices

def sliceUnion (A : Bodies) : Set Space :=
  ⋃ i : Fin 3, ({(i : ℝ)} : Set ℝ) ×ˢ A i

def sharpHull (A0 T : Set Plane) : Set Space :=
  convexHull ℝ (sliceUnion ![A0, T, T])

lemma sliceUnion_three (A : Bodies) :
    sliceUnion A = ({0} ×ˢ A 0 ∪ {1} ×ˢ A 1) ∪ {2} ×ˢ A 2 := by
  ext p
  norm_num [sliceUnion, Fin.exists_fin_succ, or_assoc]

private lemma compact_convexJoin {s t : Set Space} (hs : IsCompact s) (ht : IsCompact t) :
    IsCompact (convexJoin ℝ s t) := by
  have heq : convexJoin ℝ s t =
      (fun q : Space × Space × ℝ => (1 - q.2.2) • q.1 + q.2.2 • q.2.1) ''
        (s ×ˢ (t ×ˢ Icc 0 1)) := by
    ext p
    simp [mem_convexJoin, segment_eq_image, and_assoc]
  rw [heq]
  exact (hs.prod (ht.prod isCompact_Icc)).image (by fun_prop)

lemma isCompact_sharpHull {A0 T : Set Plane} (hA : IsBody A0) (hT : IsBody T) :
    IsCompact (sharpHull A0 T) := by
  have h0 := (convex_singleton (0 : ℝ)).prod hA.2.1
  have h1 := (convex_singleton (1 : ℝ)).prod hT.2.1
  have h2 := (convex_singleton (2 : ℝ)).prod hT.2.1
  have hn0 := (singleton_nonempty (0 : ℝ)).prod hA.2.2
  have hn1 := (singleton_nonempty (1 : ℝ)).prod hT.2.2
  have hn2 := (singleton_nonempty (2 : ℝ)).prod hT.2.2
  rw [sharpHull, sliceUnion_three]
  change IsCompact (convexHull ℝ (({0} ×ˢ A0 ∪ {1} ×ˢ T) ∪ {2} ×ˢ T))
  rw [convexHull_union (hn0.mono subset_union_left) hn2,
    h0.convexHull_union h1 hn0 hn1, h2.convexHull_eq]
  exact compact_convexJoin
    (compact_convexJoin ((isCompact_singleton).prod hA.1) ((isCompact_singleton).prod hT.1))
    ((isCompact_singleton).prod hT.1)

lemma convex_sharpHull (A0 T : Set Plane) : Convex ℝ (sharpHull A0 T) :=
  convex_convexHull ℝ _

private lemma convex_zero_boundary {A0 : Set Plane} (hA : Convex ℝ A0) :
    Convex ℝ {p : Space | 0 ≤ p.1 ∧ (p.1 = 0 → p.2 ∈ A0)} := by
  intro p hp q hq a b ha hb hab
  change 0 ≤ a * p.1 + b * q.1 ∧
    (a * p.1 + b * q.1 = 0 → a • p.2 + b • q.2 ∈ A0)
  refine ⟨add_nonneg (mul_nonneg ha hp.1) (mul_nonneg hb hq.1), ?_⟩
  intro hz
  by_cases ha0 : a = 0
  · have hb1 : b = 1 := by linarith
    simpa [ha0, hb1] using hq.2 (by simpa [ha0, hb1] using hz)
  by_cases hb0 : b = 0
  · have ha1 : a = 1 := by linarith
    simpa [hb0, ha1] using hp.2 (by simpa [hb0, ha1] using hz)
  obtain ⟨hpa, hqb⟩ :=
    (add_eq_zero_iff_of_nonneg (mul_nonneg ha hp.1) (mul_nonneg hb hq.1)).mp hz
  exact hA (hp.2 ((mul_eq_zero.mp hpa).resolve_left ha0))
    (hq.2 ((mul_eq_zero.mp hqb).resolve_left hb0)) ha hb hab

lemma sharpHull_subset {A0 T : Set Plane} (hT : Convex ℝ T) (hAT : A0 ⊆ T) :
    sharpHull A0 T ⊆ Icc (0 : ℝ) 2 ×ˢ T := by
  apply convexHull_min _ ((convex_Icc 0 2).prod hT)
  rw [sliceUnion_three]
  rintro p ((hp | hp) | hp)
  · have hz : p.1 = 0 := hp.1
    exact ⟨by simp [hz], hAT hp.2⟩
  · have hz : p.1 = 1 := hp.1
    exact ⟨by simp [hz], hp.2⟩
  · have hz : p.1 = 2 := hp.1
    exact ⟨by simp [hz], hp.2⟩

lemma sliceAt_sharpHull_zero {A0 T : Set Plane} (hA : Convex ℝ A0) :
    sliceAt (sharpHull A0 T) 0 = A0 := by
  have hb : sharpHull A0 T ⊆ {p : Space | 0 ≤ p.1 ∧ (p.1 = 0 → p.2 ∈ A0)} := by
    apply convexHull_min _ (convex_zero_boundary hA)
    rw [sliceUnion_three]
    rintro p ((hp | hp) | hp)
    · simp_all
    · simp_all
    · simp_all
  ext x
  constructor
  · intro hx
    exact (hb hx).2 rfl
  · intro hx
    apply subset_convexHull
    exact mem_iUnion.mpr ⟨0, by simpa using hx⟩

lemma sliceAt_sharpHull_one {A0 T : Set Plane} (hT : Convex ℝ T) (hAT : A0 ⊆ T) :
    sliceAt (sharpHull A0 T) 1 = T := by
  ext x
  constructor
  · intro hx
    exact (sharpHull_subset hT hAT hx).2
  · intro hx
    apply subset_convexHull
    exact mem_iUnion.mpr ⟨1, by simpa using hx⟩

lemma sliceAt_sharpHull_two {A0 T : Set Plane} (hT : Convex ℝ T) (hAT : A0 ⊆ T) :
    sliceAt (sharpHull A0 T) 2 = T := by
  ext x
  constructor
  · intro hx
    exact (sharpHull_subset hT hAT hx).2
  · intro hx
    apply subset_convexHull
    exact mem_iUnion.mpr ⟨2, by simpa using hx⟩

lemma sliceAt_sharpHull_fin {A0 T : Set Plane} (hA : Convex ℝ A0)
    (hT : Convex ℝ T) (hAT : A0 ⊆ T) (i : Fin 3) :
    sliceAt (sharpHull A0 T) (i : ℝ) = (![A0, T, T] : Bodies) i := by
  fin_cases i
  · simpa using sliceAt_sharpHull_zero hA
  · simpa using sliceAt_sharpHull_one hT hAT
  · simpa using sliceAt_sharpHull_two hT hAT

lemma sharpHull_integer_inter {A0 T : Set Plane} (hA : Convex ℝ A0)
    (hT : Convex ℝ T) (hAT : A0 ⊆ T) :
    sharpHull A0 T ∩ (Set.range (fun z : ℤ => (z : ℝ)) ×ˢ Set.univ) =
      sliceUnion ![A0, T, T] := by
  ext p
  constructor
  · rintro ⟨hp, ⟨⟨z, hz⟩, _⟩⟩
    have hb := (sharpHull_subset hT hAT hp).1
    change 0 ≤ p.1 ∧ p.1 ≤ 2 at hb
    have hzb : 0 ≤ (z : ℝ) ∧ (z : ℝ) ≤ 2 := by simpa only [hz] using hb
    have h0 : (0 : ℤ) ≤ z := by exact_mod_cast hzb.1
    have h2 : z ≤ (2 : ℤ) := by exact_mod_cast hzb.2
    have hz3 : z = 0 ∨ z = 1 ∨ z = 2 := by omega
    rcases hz3 with rfl | rfl | rfl
    · refine mem_iUnion.mpr ⟨0, ?_⟩
      refine ⟨hz.symm, ?_⟩
      have hpx : p.2 ∈ sliceAt (sharpHull A0 T) 0 := by
        change (0, p.2) ∈ sharpHull A0 T
        have heq : p = (0, p.2) := Prod.ext (by simpa using hz.symm) rfl
        rwa [← heq]
      simpa [sliceAt_sharpHull_zero hA] using hpx
    · refine mem_iUnion.mpr ⟨1, ?_⟩
      exact ⟨hz.symm, by simpa using (sharpHull_subset hT hAT hp).2⟩
    · refine mem_iUnion.mpr ⟨2, ?_⟩
      exact ⟨hz.symm, by simpa using (sharpHull_subset hT hAT hp).2⟩
  · intro hp
    refine ⟨subset_convexHull ℝ _ hp, ?_⟩
    obtain ⟨i, hi⟩ := mem_iUnion.mp hp
    exact ⟨⟨(i : ℤ), by simpa using hi.1.symm⟩, mem_univ _⟩

lemma mem_sharpHull_integer_iff {A0 T : Set Plane} (hA : Convex ℝ A0)
    (hT : Convex ℝ T) (hAT : A0 ⊆ T) (z : ℤ) (x : Plane) :
    ((z : ℝ), x) ∈ sharpHull A0 T ↔
      ∃ i : Fin 3, z = (i : ℤ) ∧ x ∈ (![A0, T, T] : Bodies) i := by
  constructor
  · intro hp
    have hs : ((z : ℝ), x) ∈ sliceUnion ![A0, T, T] := by
      rw [← sharpHull_integer_inter hA hT hAT]
      exact ⟨hp, ⟨⟨z, rfl⟩, mem_univ x⟩⟩
    obtain ⟨i, hi⟩ := mem_iUnion.mp hs
    have hz : (z : ℝ) = ((i : ℤ) : ℝ) := by simpa using hi.1
    exact ⟨i, by exact_mod_cast hz, hi.2⟩
  · rintro ⟨i, rfl, hx⟩
    apply subset_convexHull
    exact mem_iUnion.mpr ⟨i, ⟨by simp, hx⟩⟩

lemma sliceAt_sharpHull_int_empty_of_not_fin {A0 T : Set Plane} (hA : Convex ℝ A0)
    (hT : Convex ℝ T) (hAT : A0 ⊆ T) {z : ℤ}
    (hz : ¬ ∃ i : Fin 3, z = (i : ℤ)) :
    sliceAt (sharpHull A0 T) (z : ℝ) = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro x hx
  obtain ⟨i, hi, _⟩ := (mem_sharpHull_integer_iff hA hT hAT z x).mp hx
  exact hz ⟨i, hi⟩

end ThreeSlices
