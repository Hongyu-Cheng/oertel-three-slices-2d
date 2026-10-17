import ThreeSlices.Basic

open Set MeasureTheory Module

namespace ThreeSlices

/-- A point of a convex body that is maximal on its positive ray from the origin. -/
def IsRadialEndpoint (K : Set Plane) (v : Plane) : Prop :=
  v ∈ K ∧ ∀ t : ℝ, 1 < t → t • v ∉ K

/-- A point beyond the chord cannot have a nonpositive coefficient of either endpoint:
its segment to that endpoint would meet the opposite ray beyond its maximal point. -/
lemma coefficient_pos_of_radialEndpoint {K : Set Plane} (hK : Convex ℝ K)
    {u v : Plane} (hu : u ∈ K) (hv : IsRadialEndpoint K v)
    {a b : ℝ} (hx : a • u + b • v ∈ K) (hab : 1 < a + b) : 0 < a := by
  by_contra ha
  have ha : a ≤ 0 := le_of_not_gt ha
  have hd : 0 < 1 - a := by linarith
  have hweights : 1 / (1 - a) + -a / (1 - a) = 1 := by
    field_simp
    ring
  have hcomb := hK hx hu (div_nonneg zero_le_one hd.le)
    (div_nonneg (neg_nonneg.mpr ha) hd.le) hweights
  have he : (1 / (1 - a)) • (a • u + b • v) + (-a / (1 - a)) • u =
      (b / (1 - a)) • v := by
    match_scalars <;> field_simp
    all_goals ring
  rw [he] at hcomb
  exact hv.2 (b / (1 - a)) ((one_lt_div hd).2 (by linarith)) hcomb

/-- The closed cone between two independent radial endpoints. -/
def chordSector (e : Basis (Fin 2) ℝ Plane) : Set Plane :=
  {x | 0 ≤ e.repr x 0 ∧ 0 ≤ e.repr x 1}

/-- The interior of the cone between two independent radial endpoints. -/
def openChordSector (e : Basis (Fin 2) ℝ Plane) : Set Plane :=
  {x | 0 < e.repr x 0 ∧ 0 < e.repr x 1}

/-- The closed half-plane bounded by the endpoint chord and containing the origin. -/
def chordHalfplane (e : Basis (Fin 2) ℝ Plane) : Set Plane :=
  {x | e.repr x 0 + e.repr x 1 ≤ 1}

lemma basis_two_repr (e : Basis (Fin 2) ℝ Plane) (x : Plane) :
    e.repr x 0 • e 0 + e.repr x 1 • e 1 = x := by
  simpa only [Fin.sum_univ_two] using e.sum_repr x

/-- The part of the body outside an endpoint chord lies strictly between its two rays. -/
theorem beyond_chord_subset_openSector {K : Set Plane} (hK : Convex ℝ K)
    (e : Basis (Fin 2) ℝ Plane)
    (h₀ : IsRadialEndpoint K (e 0)) (h₁ : IsRadialEndpoint K (e 1)) :
    K \ chordHalfplane e ⊆ openChordSector e := by
  intro x hx
  have hh : 1 < e.repr x 0 + e.repr x 1 := lt_of_not_ge hx.2
  have hm : e.repr x 0 • e 0 + e.repr x 1 • e 1 ∈ K := by
    rw [basis_two_repr]
    exact hx.1
  exact ⟨coefficient_pos_of_radialEndpoint hK h₀.1 h₁ hm hh,
    coefficient_pos_of_radialEndpoint hK h₁.1 h₀ (by simpa [add_comm] using hm)
      (by linarith)⟩

/-- Convexity fills the triangle spanned by the origin and the two chord endpoints. -/
lemma endpoint_triangle_mem {K : Set Plane} (hK : Convex ℝ K)
    (hzero : (0 : Plane) ∈ K) {u v : Plane} (hu : u ∈ K) (hv : v ∈ K)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b ≤ 1) :
    a • u + b • v ∈ K := by
  have h := hK.sum_mem (t := Finset.univ) (w := ![a, b, 1 - a - b])
    (z := ![u, v, 0])
    (by intro i _; fin_cases i <;> simp <;> linarith)
    (by simp [Fin.sum_univ_succ])
    (by intro i _; fin_cases i <;> simp <;> assumption)
  simpa [Fin.sum_univ_succ] using h

/-- Within the numerator sector, the endpoint half-plane cuts out a triangle inside the body. -/
theorem chordHalfplane_inter_sector_subset {K : Set Plane} (hK : Convex ℝ K)
    (hzero : (0 : Plane) ∈ K) (e : Basis (Fin 2) ℝ Plane)
    (h₀ : e 0 ∈ K) (h₁ : e 1 ∈ K) :
    chordHalfplane e ∩ chordSector e ⊆ K := by
  intro x hx
  rw [← basis_two_repr e x]
  exact endpoint_triangle_mem hK hzero h₀ h₁ hx.2.1 hx.2.2 hx.1

/-- Outside the numerator sector, replacing the body's arc by its chord enlarges it. -/
theorem body_diff_openSector_subset_chordHalfplane {K : Set Plane}
    (hK : Convex ℝ K) (e : Basis (Fin 2) ℝ Plane)
    (h₀ : IsRadialEndpoint K (e 0)) (h₁ : IsRadialEndpoint K (e 1)) :
    K \ openChordSector e ⊆ chordHalfplane e := by
  intro x hx
  by_contra hh
  exact hx.2 (beyond_chord_subset_openSector hK e h₀ h₁ ⟨hx.1, hh⟩)

/-- The intersection of the endpoint half-planes used in the chord reduction. -/
def chordPolygon {ι : Type*} (e : ι → Basis (Fin 2) ℝ Plane) : Set Plane :=
  ⋂ i, chordHalfplane (e i)

lemma chordHalfplane_isClosed (e : Basis (Fin 2) ℝ Plane) :
    IsClosed (chordHalfplane e) := by
  exact isClosed_le
    ((e.coord 0).continuous_of_finiteDimensional.add
      (e.coord 1).continuous_of_finiteDimensional) continuous_const

lemma chordPolygon_isClosed {ι : Type*} (e : ι → Basis (Fin 2) ℝ Plane) :
    IsClosed (chordPolygon e) := isClosed_iInter fun i => chordHalfplane_isClosed (e i)

lemma chordPolygon_isCompact {ι : Type*} (e : ι → Basis (Fin 2) ℝ Plane)
    (hb : Bornology.IsBounded (chordPolygon e)) : IsCompact (chordPolygon e) :=
  Metric.isCompact_of_isClosed_isBounded (chordPolygon_isClosed e) hb

/-- Each numerator sector is reduced when all its endpoint chords are imposed. -/
theorem chordPolygon_inter_sector_subset {ι : Type*} {K : Set Plane}
    (hK : Convex ℝ K) (hzero : (0 : Plane) ∈ K)
    (e : ι → Basis (Fin 2) ℝ Plane)
    (hend : ∀ i, IsRadialEndpoint K (e i 0) ∧ IsRadialEndpoint K (e i 1)) (j : ι) :
    chordPolygon e ∩ chordSector (e j) ⊆ K ∩ chordSector (e j) := by
  intro x hx
  exact ⟨chordHalfplane_inter_sector_subset hK hzero (e j) (hend j).1.1 (hend j).2.1
    ⟨mem_iInter.mp hx.1 j, hx.2⟩, hx.2⟩

/-- In any region avoiding all open numerator sectors, the chord polygon contains the body. -/
theorem body_inter_subset_chordPolygon {ι : Type*} {K D : Set Plane}
    (hK : Convex ℝ K) (e : ι → Basis (Fin 2) ℝ Plane)
    (hend : ∀ i, IsRadialEndpoint K (e i 0) ∧ IsRadialEndpoint K (e i 1))
    (hD : D ⊆ (⋃ i, openChordSector (e i))ᶜ) :
    K ∩ D ⊆ chordPolygon e ∩ D := by
  intro x hx
  refine ⟨mem_iInter.mpr fun i => ?_, hx.2⟩
  apply body_diff_openSector_subset_chordHalfplane hK (e i) (hend i).1 (hend i).2
  exact ⟨hx.1, fun hi => hD hx.2 (mem_iUnion.mpr ⟨i, hi⟩)⟩

/-- The two containments give the area comparison. -/
theorem chordPolygon_sector_ratio_le {ι : Type*} {K D : Set Plane}
    (hK : IsCompact K) (hconv : Convex ℝ K) (hzero : (0 : Plane) ∈ K)
    (e : ι → Basis (Fin 2) ℝ Plane) (hP : IsCompact (chordPolygon e))
    (hend : ∀ i, IsRadialEndpoint K (e i 0) ∧ IsRadialEndpoint K (e i 1))
    (hD : D ⊆ (⋃ i, openChordSector (e i))ᶜ) (j : ι)
    (hden : 0 < area (K ∩ D)) :
    area (chordPolygon e ∩ chordSector (e j)) / area (chordPolygon e ∩ D) ≤
      area (K ∩ chordSector (e j)) / area (K ∩ D) := by
  have hn : area (chordPolygon e ∩ chordSector (e j)) ≤ area (K ∩ chordSector (e j)) :=
    measureReal_mono (chordPolygon_inter_sector_subset hconv hzero e hend j)
      (measure_ne_top_of_subset inter_subset_left (hK.measure_ne_top (μ := volume)))
  have hd : area (K ∩ D) ≤ area (chordPolygon e ∩ D) :=
    measureReal_mono (body_inter_subset_chordPolygon hconv e hend hD)
      (measure_ne_top_of_subset inter_subset_left (hP.measure_ne_top (μ := volume)))
  exact (div_le_div_of_nonneg_left (area_nonneg _) hden hd).trans
    (div_le_div_of_nonneg_right hn hden.le)

/-- Translating a set by any nonnegative multiple of a recession direction preserves it. -/
def IsRecessionDirection (P : Set Plane) (r : Plane) : Prop :=
  ∀ x ∈ P, ∀ t : ℝ, 0 ≤ t → x + t • r ∈ P

lemma zero_mem_chordPolygon {ι : Type*} (e : ι → Basis (Fin 2) ℝ Plane) :
    (0 : Plane) ∈ chordPolygon e := by
  simp [chordPolygon, chordHalfplane]

/-- A chord polygon's recession directions are exactly those not pointing beyond any chord. -/
theorem chordPolygon_recession_iff {ι : Type*} (e : ι → Basis (Fin 2) ℝ Plane) (r : Plane) :
    IsRecessionDirection (chordPolygon e) r ↔
      ∀ i, (e i).repr r 0 + (e i).repr r 1 ≤ 0 := by
  constructor
  · intro hr i
    by_contra hi
    have hs : 0 < (e i).repr r 0 + (e i).repr r 1 := lt_of_not_ge hi
    have hm := mem_iInter.mp
      (hr 0 (zero_mem_chordPolygon e)
        (2 / ((e i).repr r 0 + (e i).repr r 1)) (div_nonneg (by norm_num) hs.le)) i
    change (e i).repr (0 + (2 / ((e i).repr r 0 + (e i).repr r 1)) • r) 0 +
      (e i).repr (0 + (2 / ((e i).repr r 0 + (e i).repr r 1)) • r) 1 ≤ 1 at hm
    simp only [zero_add, map_smul, Finsupp.smul_apply, smul_eq_mul] at hm
    have he : (2 / ((e i).repr r 0 + (e i).repr r 1)) * (e i).repr r 0 +
        (2 / ((e i).repr r 0 + (e i).repr r 1)) * (e i).repr r 1 = 2 := by
      rw [← mul_add, div_mul_cancel₀ _ hs.ne']
    linarith
  · intro hr x hx t ht
    apply mem_iInter.mpr
    intro i
    have hi := mem_iInter.mp hx i
    change (e i).repr x 0 + (e i).repr x 1 ≤ 1 at hi
    change (e i).repr (x + t • r) 0 + (e i).repr (x + t • r) 1 ≤ 1
    simp only [map_add, map_smul, Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul]
    nlinarith [mul_nonpos_of_nonneg_of_nonpos ht (hr i)]

/-- A nonzero recession direction cannot lie even on the boundary of a numerator sector. -/
theorem recession_not_mem_sector {ι : Type*} (e : ι → Basis (Fin 2) ℝ Plane)
    {r : Plane} (hr : IsRecessionDirection (chordPolygon e) r) (hne : r ≠ 0) (i : ι) :
    r ∉ chordSector (e i) := by
  intro hs
  have hsum := (chordPolygon_recession_iff e r).1 hr i
  have h₀ : (e i).repr r 0 = 0 := by change 0 ≤ _ ∧ 0 ≤ _ at hs; linarith [hs.1, hs.2]
  have h₁ : (e i).repr r 1 = 0 := by change 0 ≤ _ ∧ 0 ≤ _ at hs; linarith [hs.1, hs.2]
  apply hne
  rw [← basis_two_repr (e i) r, h₀, h₁]
  simp

/-- An unbounded finite chord intersection has a nonzero recession direction. -/
theorem unbounded_chordPolygon_has_recession {ι : Type*} [Fintype ι]
    (e : ι → Basis (Fin 2) ℝ Plane) (hb : ¬ Bornology.IsBounded (chordPolygon e)) :
    ∃ r : Plane, r ≠ 0 ∧ IsRecessionDirection (chordPolygon e) r := by
  classical
  by_contra hn
  push Not at hn
  let g : Plane → ℝ := fun x => ∑ i, max ((e i).repr x 0 + (e i).repr x 1) 0
  have hg : Continuous g := by
    apply continuous_finsetSum
    intro i _
    exact (((e i).coord 0).continuous_of_finiteDimensional.add
      ((e i).coord 1).continuous_of_finiteDimensional).max continuous_const
  have hpos : ∀ r ∈ Metric.sphere (0 : Plane) 1, 0 < g r := by
    intro r hr
    have hnorm : ‖r‖ = 1 := by simpa [Metric.mem_sphere, dist_zero_right] using hr
    have hne : r ≠ 0 := by intro he; simp [he] at hnorm
    have hi : ∃ i, 0 < (e i).repr r 0 + (e i).repr r 1 := by
      by_contra hi
      push Not at hi
      exact hn r hne ((chordPolygon_recession_iff e r).2 hi)
    rcases hi with ⟨i, hi⟩
    exact (Finset.sum_pos_iff_of_nonneg (fun j _ => le_max_right _ _)).2
      ⟨i, Finset.mem_univ i, hi.trans_le (le_max_left _ _)⟩
  obtain ⟨r, hr, hmin⟩ := (isCompact_sphere (0 : Plane) 1).exists_isMinOn
    (NormedSpace.sphere_nonempty.mpr zero_le_one) hg.continuousOn
  have hm : 0 < g r := hpos r hr
  have hscale : ∀ t : ℝ, 0 ≤ t → ∀ x : Plane, g (t • x) = t * g x := by
    intro t ht x
    dsimp [g]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    simp only [map_smul, Finsupp.smul_apply, smul_eq_mul]
    rw [← mul_add, mul_max_of_nonneg _ _ ht, mul_zero]
  apply hb
  refine isBounded_iff_forall_norm_le.mpr ⟨(Fintype.card ι : ℝ) / g r, ?_⟩
  intro x hx
  by_cases hzero : x = 0
  · simp only [hzero, norm_zero]
    exact div_nonneg (Nat.cast_nonneg _) hm.le
  have hxnorm : 0 < ‖x‖ := norm_pos_iff.mpr hzero
  have hsphere : (‖x‖⁻¹ : ℝ) • x ∈ Metric.sphere (0 : Plane) 1 := by
    simp [norm_smul, hxnorm.ne']
  have hlow : g r ≤ g ((‖x‖⁻¹ : ℝ) • x) := hmin hsphere
  rw [hscale _ (inv_nonneg.mpr hxnorm.le)] at hlow
  have hupper : g x ≤ (Fintype.card ι : ℝ) := by
    calc
      g x ≤ ∑ _i : ι, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro i _
        exact max_le (mem_iInter.mp hx i) zero_le_one
      _ = (Fintype.card ι : ℝ) := by simp
  apply (le_div_iff₀ hm).2
  have hl : g r * ‖x‖ ≤ g x := by
    rw [inv_mul_eq_div] at hlow
    exact (le_div_iff₀ hxnorm).1 hlow
  simpa [mul_comm] using hl.trans hupper

end ThreeSlices
