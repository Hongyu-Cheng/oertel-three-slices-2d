import ThreeSlices.MixedIntegerBasic

open Set MeasureTheory

namespace ThreeSlices

private lemma area_homothety_image (y : Plane) (t : ℝ) (A : Set Plane) :
    area (AffineMap.homothety y t '' A) =
      |t ^ Module.finrank ℝ Plane| * area A := by
  unfold area Measure.real
  rw [volume.addHaar_image_homothety, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (abs_nonneg _)]

/-- A positive-area slice remains positive at every layer strictly between it and
another nonempty slice. -/
lemma area_sliceAt_pos_between {C : Set Space} (hcompact : IsCompact C)
    (hconvex : Convex ℝ C) {a z b : ℝ} (haz : a < z) (hzb : z < b)
    (ha : 0 < area (sliceAt C a)) (hb : (sliceAt C b).Nonempty) :
    0 < area (sliceAt C z) := by
  obtain ⟨y, hy⟩ := hb
  let t : ℝ := (b - z) / (b - a)
  let u : ℝ := (z - a) / (b - a)
  have hba : 0 < b - a := by linarith
  have ht : 0 < t := div_pos (sub_pos.mpr hzb) hba
  have hu : 0 ≤ u := le_of_lt (div_pos (sub_pos.mpr haz) hba)
  have htu : t + u = 1 := by
    dsimp [t, u]
    field_simp [hba.ne']
    ring
  have hz : t * a + u * b = z := by
    dsimp [t, u]
    field_simp [hba.ne']
    ring
  have hsub : AffineMap.homothety y t '' sliceAt C a ⊆ sliceAt C z := by
    rintro _ ⟨x, hx, rfl⟩
    have hp := hconvex hx hy ht.le hu htu
    change (t * a + u * b, t • x + u • y) ∈ C at hp
    change (z, AffineMap.homothety y t x) ∈ C
    have hu' : u = 1 - t := by linarith
    have he : AffineMap.homothety y t x = t • x + u • y := by
      simp only [AffineMap.homothety_apply, vsub_eq_sub, vadd_eq_add, smul_sub]
      rw [hu', sub_smul, one_smul]
      abel
    rw [he, ← hz]
    exact hp
  have hpos : 0 < area (AffineMap.homothety y t '' sliceAt C a) := by
    rw [area_homothety_image]
    exact mul_pos (abs_pos.mpr (pow_ne_zero _ ht.ne')) ha
  exact hpos.trans_le (area_mono hsub (compact_sliceAt hcompact z))

/-- The integer layers carrying positive planar area form an interval. -/
lemma positiveSlices_ordConnected {C : Set Space} (hcompact : IsCompact C)
    (hconvex : Convex ℝ C) : (positiveSlices C).OrdConnected := by
  apply Set.ordConnected_of_Ioo
  intro a ha b hb hab z hz
  change 0 < area (sliceAt C a) at ha
  change 0 < area (sliceAt C b) at hb
  change 0 < area (sliceAt C z)
  apply area_sliceAt_pos_between hcompact hconvex (a := (a : ℝ)) (b := (b : ℝ))
      (by exact_mod_cast hz.1) (by exact_mod_cast hz.2) ha
  apply Set.nonempty_iff_ne_empty.mpr
  intro he
  have : 0 < area (∅ : Set Plane) := by simpa [he] using hb
  simp [area] at this

private lemma consecutive_of_ordConnected_ncard_three {s : Set ℤ}
    (hconn : s.OrdConnected) (hcard : s.ncard = 3) :
    ∃ k : ℤ, ∀ z : ℤ, z ∈ s ↔ ∃ i : Fin 3, z = k + (i : ℤ) := by
  obtain ⟨a, b, c, hab, hac, hbc, hs⟩ := Set.ncard_eq_three.mp hcard
  let k := min a (min b c)
  have hk : k ∈ s := by
    rw [hs]
    simp only [mem_insert_iff, mem_singleton_iff]
    dsimp [k]
    omega
  have hlow : ∀ z ∈ s, k ≤ z := by
    intro z hz
    rw [hs] at hz
    simp only [mem_insert_iff, mem_singleton_iff] at hz
    dsimp [k]
    omega
  have hhigh : ∀ z ∈ s, z ≤ k + 2 := by
    intro z hz
    by_contra hn
    have h1 := hconn.out hk hz (show k + 1 ∈ Icc k z by constructor <;> omega)
    have h2 := hconn.out hk hz (show k + 2 ∈ Icc k z by constructor <;> omega)
    have h3 := hconn.out hk hz (show k + 3 ∈ Icc k z by constructor <;> omega)
    rw [hs] at hk h1 h2 h3
    simp only [mem_insert_iff, mem_singleton_iff] at hk h1 h2 h3
    omega
  have h2 : k + 2 ∈ s := by
    have ha : a ∈ s := by simp [hs]
    have hb : b ∈ s := by simp [hs]
    have hc : c ∈ s := by simp [hs]
    have ha' := hlow a ha
    have hb' := hlow b hb
    have hc' := hlow c hc
    have ha'' := hhigh a ha
    have hb'' := hhigh b hb
    have hc'' := hhigh c hc
    rw [hs]
    simp only [mem_insert_iff, mem_singleton_iff]
    omega
  have h1 : k + 1 ∈ s :=
    hconn.out hk h2 (show k + 1 ∈ Icc k (k + 2) by constructor <;> omega)
  refine ⟨k, fun z => ⟨fun hz => ?_, fun hz => ?_⟩⟩
  · have hl := hlow z hz
    have hh := hhigh z hz
    rcases show z = k ∨ z = k + 1 ∨ z = k + 2 by omega with h | h | h
    · exact ⟨0, by simpa using h⟩
    · exact ⟨1, by simpa using h⟩
    · exact ⟨2, by simpa using h⟩
  · obtain ⟨i, rfl⟩ := hz
    fin_cases i
    · simpa using hk
    · simpa using h1
    · simpa using h2

/-- Exactly three positive-area integer slices of a compact convex body occur at
three consecutive integer layers; other, zero-area slices are allowed. -/
theorem positiveSlices_consecutive {C : Set Space} (hcompact : IsCompact C)
    (hconvex : Convex ℝ C) (hcard : (positiveSlices C).ncard = 3) :
    ∃ k : ℤ, ∀ z : ℤ,
      0 < area (sliceAt C z) ↔ ∃ i : Fin 3, z = k + (i : ℤ) := by
  exact consecutive_of_ordConnected_ncard_three
    (positiveSlices_ordConnected hcompact hconvex) hcard

end ThreeSlices
