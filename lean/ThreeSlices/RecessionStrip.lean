import ThreeSlices.AffineNormalization
import ThreeSlices.AffineArea
import ThreeSlices.SixRayConstruction
import ThreeSlices.StripInequality
import ThreeSlices.TsintsifasReduction

open Set Module

namespace ThreeSlices

/-- The recession ray becomes vertical and the third fan line becomes horizontal. -/
noncomputable def recessionStripEquiv (a b : ℝ) (r : Plane)
    (ha : 0 < a) (hb : 0 < b) (hr₀ : 0 < r 0) (hr₁ : 0 < r 1) :
    Plane ≃L[ℝ] Plane :=
  formCoordinatesEquiv
    (r 1 • EuclideanSpace.proj 0 - r 0 • EuclideanSpace.proj 1)
    (a • EuclideanSpace.proj 0 + b • EuclideanSpace.proj 1) (by
      rw [linearIndependent_fin2]
      constructor
      · intro he
        have h := congrArg (fun f : Plane →L[ℝ] ℝ => f (EuclideanSpace.single 0 1)) he
        simp at h
        exact ha.ne' h
      · intro c he
        have h₀ := congrArg (fun f : Plane →L[ℝ] ℝ => f (EuclideanSpace.single 0 1)) he
        have h₁ := congrArg (fun f : Plane →L[ℝ] ℝ => f (EuclideanSpace.single 1 1)) he
        simp at h₀ h₁
        have hpos : 0 < a * r 0 + b * r 1 := add_pos (mul_pos ha hr₀) (mul_pos hb hr₁)
        nlinarith)

@[simp] lemma recessionStripEquiv_apply_zero (a b : ℝ) (r : Plane)
    (ha : 0 < a) (hb : 0 < b) (hr₀ : 0 < r 0) (hr₁ : 0 < r 1) (x : Plane) :
    recessionStripEquiv a b r ha hb hr₀ hr₁ x 0 = r 1 * x 0 - r 0 * x 1 := rfl

@[simp] lemma recessionStripEquiv_apply_one (a b : ℝ) (r : Plane)
    (ha : 0 < a) (hb : 0 < b) (hr₀ : 0 < r 0) (hr₁ : 0 < r 1) (x : Plane) :
    recessionStripEquiv a b r ha hb hr₀ hr₁ x 1 = a * x 0 + b * x 1 := rfl

lemma IsRadialEndpoint.linear_image {K : Set Plane} {x : Plane}
    (hx : IsRadialEndpoint K x) (E : Plane ≃L[ℝ] Plane) :
    IsRadialEndpoint (E '' K) (E x) := by
  refine ⟨mem_image_of_mem E hx.1, ?_⟩
  intro t ht hm
  obtain ⟨y, hy, he⟩ := hm
  apply hx.2 t ht
  have hy' : y = t • x := E.injective (by simpa using he)
  rwa [hy'] at hy

lemma linear_image_sector_ratio (E : Plane ≃L[ℝ] Plane) (K N D : Set Plane) :
    area ((E '' K) ∩ (E '' N)) / area ((E '' K) ∩ (E '' D)) =
      area (K ∩ N) / area (K ∩ D) := by
  exact affine_image_sector_ratio E.toContinuousAffineEquiv K N D

private lemma linear_image_setOf (E : Plane ≃L[ℝ] Plane) (P Q : Plane → Prop)
    (h : ∀ x, Q (E x) ↔ P x) : E '' {x | P x} = {y | Q y} := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (h x).mpr hx
  · intro hy
    refine ⟨E.symm y, ?_, E.apply_symm_apply y⟩
    apply (h (E.symm y)).mp
    rwa [E.apply_symm_apply]

theorem recessionStripEquiv_sector_images (a b : ℝ) (r : Plane)
    (ha : 0 < a) (hb : 0 < b) (hr₀ : 0 < r 0) (hr₁ : 0 < r 1)
    (s t : ℝ) (hs : 0 < s) (ht : 0 < t) :
    let E := recessionStripEquiv a b r ha hb hr₀ hr₁
    E '' normalizedNumeratorSector a b 0 = stripNumeratorRight (s * r 1) (s * a) ∧
    E '' normalizedNumeratorSector a b 1 = stripNumeratorLeft (t * r 0) (t * b) ∧
    E '' normalizedDenominatorSector a b 0 = stripDenominatorLeft (s * r 1) (s * a) ∧
    E '' normalizedDenominatorSector a b 1 = stripDenominatorRight (t * r 0) (t * b) := by
  let E := recessionStripEquiv a b r ha hb hr₀ hr₁
  have hd : 0 < a * r 0 + b * r 1 := add_pos (mul_pos ha hr₀) (mul_pos hb hr₁)
  have hX_nonneg (x : Plane) (hy : 0 ≤ a * x 0 + b * x 1) (hx : x 1 ≤ 0) :
      0 ≤ r 1 * x 0 - r 0 * x 1 := by
    have hx₀ : 0 ≤ x 0 := by nlinarith [mul_nonpos_of_nonneg_of_nonpos hb.le hx]
    exact sub_nonneg.mpr (le_trans (mul_nonpos_of_nonneg_of_nonpos hr₀.le hx)
      (mul_nonneg hr₁.le hx₀))
  have hX_nonpos (x : Plane) (hy : 0 ≤ a * x 0 + b * x 1) (hx : x 0 ≤ 0) :
      r 1 * x 0 - r 0 * x 1 ≤ 0 := by
    have hx₁ : 0 ≤ x 1 := by nlinarith [mul_nonpos_of_nonneg_of_nonpos ha.le hx]
    exact sub_nonpos.mpr (le_trans (mul_nonpos_of_nonneg_of_nonpos hr₁.le hx)
      (mul_nonneg hr₀.le hx₁))
  have hright (x : Plane) :
      s * r 1 * (a * x 0 + b * x 1) - s * a * (r 1 * x 0 - r 0 * x 1) =
        (s * (a * r 0 + b * r 1)) * x 1 := by ring
  have hleft (x : Plane) :
      t * r 0 * (a * x 0 + b * x 1) - (-(t * b) * (r 1 * x 0 - r 0 * x 1)) =
        (t * (a * r 0 + b * r 1)) * x 0 := by ring
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply linear_image_setOf E
    intro x
    change (0 ≤ E x 0 ∧ 0 ≤ E x 1 ∧ s * r 1 * E x 1 ≤ s * a * E x 0) ↔
      (x 1 ≤ 0 ∧ 0 ≤ a * x 0 + b * x 1)
    simp only [E, recessionStripEquiv_apply_zero, recessionStripEquiv_apply_one]
    have hi : s * r 1 * (a * x 0 + b * x 1) ≤ s * a * (r 1 * x 0 - r 0 * x 1) ↔
        x 1 ≤ 0 := by
      rw [← sub_nonpos, hright]
      simpa only [mul_zero] using (mul_le_mul_iff_right₀ (mul_pos hs hd) :
        (s * (a * r 0 + b * r 1)) * x 1 ≤ (s * (a * r 0 + b * r 1)) * 0 ↔ x 1 ≤ 0)
    rw [hi]
    constructor
    · tauto
    · intro hx
      exact ⟨hX_nonneg x hx.2 hx.1, hx.2, hx.1⟩
  · apply linear_image_setOf E
    intro x
    change (E x 0 ≤ 0 ∧ 0 ≤ E x 1 ∧ t * r 0 * E x 1 ≤ -(t * b) * E x 0) ↔
      (x 0 ≤ 0 ∧ 0 ≤ a * x 0 + b * x 1)
    simp only [E, recessionStripEquiv_apply_zero, recessionStripEquiv_apply_one]
    have hi : t * r 0 * (a * x 0 + b * x 1) ≤ -(t * b) * (r 1 * x 0 - r 0 * x 1) ↔
        x 0 ≤ 0 := by
      rw [← sub_nonpos, hleft]
      simpa only [mul_zero] using (mul_le_mul_iff_right₀ (mul_pos ht hd) :
        (t * (a * r 0 + b * r 1)) * x 0 ≤ (t * (a * r 0 + b * r 1)) * 0 ↔ x 0 ≤ 0)
    rw [hi]
    constructor
    · tauto
    · intro hx
      exact ⟨hX_nonpos x hx.2 hx.1, hx.2, hx.1⟩
  · apply linear_image_setOf E
    intro x
    change (E x 0 ≤ 0 ∧ E x 1 ≤ 0 ∧ s * a * E x 0 ≤ s * r 1 * E x 1) ↔
      (0 ≤ x 1 ∧ a * x 0 + b * x 1 ≤ 0)
    simp only [E, recessionStripEquiv_apply_zero, recessionStripEquiv_apply_one]
    have hi : s * a * (r 1 * x 0 - r 0 * x 1) ≤ s * r 1 * (a * x 0 + b * x 1) ↔
        0 ≤ x 1 := by
      rw [← sub_nonneg, hright, mul_nonneg_iff_of_pos_left (mul_pos hs hd)]
    rw [hi]
    constructor
    · tauto
    · intro hx
      have hn := hX_nonneg (-x) (by simp only [PiLp.neg_apply]; linarith)
        (by simp only [PiLp.neg_apply]; linarith)
      refine ⟨?_, hx.2, hx.1⟩
      simp only [PiLp.neg_apply] at hn
      linarith
  · apply linear_image_setOf E
    intro x
    change (0 ≤ E x 0 ∧ E x 1 ≤ 0 ∧ -(t * b) * E x 0 ≤ t * r 0 * E x 1) ↔
      (0 ≤ x 0 ∧ a * x 0 + b * x 1 ≤ 0)
    simp only [E, recessionStripEquiv_apply_zero, recessionStripEquiv_apply_one]
    have hi : -(t * b) * (r 1 * x 0 - r 0 * x 1) ≤ t * r 0 * (a * x 0 + b * x 1) ↔
        0 ≤ x 0 := by
      rw [← sub_nonneg, hleft, mul_nonneg_iff_of_pos_left (mul_pos ht hd)]
    rw [hi]
    constructor
    · tauto
    · intro hx
      have hn := hX_nonpos (-x) (by simp only [PiLp.neg_apply]; linarith)
        (by simp only [PiLp.neg_apply]; linarith)
      refine ⟨?_, hx.2, hx.1⟩
      simp only [PiLp.neg_apply] at hn
      linarith

private lemma chord_recession_outward (e : Basis (Fin 2) ℝ Plane)
    (E : Plane ≃L[ℝ] Plane) (r : Plane)
    (hrec : e.repr r 0 + e.repr r 1 ≤ 0)
    (hr₀ : E r 0 = 0) (hr₁ : 0 < E r 1)
    (hP : E (e 1) 1 = 0) (hW : 0 < E (e 0) 1) :
    0 ≤ E (e 1) 0 * (E (e 0) 0 - E (e 1) 0) := by
  have hx := congrArg (fun x : Plane => E x 0) (basis_two_repr e r)
  have hy := congrArg (fun x : Plane => E x 1) (basis_two_repr e r)
  simp only [map_add, map_smul, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul] at hx hy
  rw [hr₀] at hx
  rw [hP, mul_zero, add_zero] at hy
  have hc : 0 < e.repr r 0 := (mul_pos_iff_of_pos_right hW).mp (hy.symm ▸ hr₁)
  apply (mul_nonneg_iff_of_pos_left hc).mp
  have hm := mul_nonpos_of_nonneg_of_nonpos (sq_nonneg (E (e 1) 0)) hrec
  have he := congrArg (fun z : ℝ => E (e 1) 0 * z) hx
  nlinarith only [hm, he]

/-- A first-quadrant recession direction yields the two-ratio strip bound. -/
theorem recession_firstQuadrant_two_ratio_bound {A : Set Plane} (hA : IsBody A)
    (hzero : (0 : Plane) ∈ interior A) {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (e : Fin 3 → Basis (Fin 2) ℝ Plane) (t : Fin 3 → Fin 2 → ℝ)
    (ht : ∀ i k, 0 < t i k)
    (he : ∀ i k, e i k = t i k • normalizedNumeratorRay a b i k)
    (hend : ∀ i k, IsRadialEndpoint A (e i k))
    (r : Plane) (hr : IsRecessionDirection (chordPolygon e) r)
    (hr₀ : 0 < r 0) (hr₁ : 0 < r 1) :
    2 ≤ area (A ∩ normalizedNumeratorSector a b 0) /
        area (A ∩ normalizedDenominatorSector a b 0) +
      area (A ∩ normalizedNumeratorSector a b 1) /
        area (A ∩ normalizedDenominatorSector a b 1) := by
  let E := recessionStripEquiv a b r ha hb hr₀ hr₁
  let d := a * r 0 + b * r 1
  let p := t 0 1 * d
  let q := t 1 1 * d
  let u := t 1 0 * r 0
  let v := t 1 0 * b
  let w := t 0 0 * r 1
  let z := t 0 0 * a
  have hd : 0 < d := add_pos (mul_pos ha hr₀) (mul_pos hb hr₁)
  have hp : 0 < p := mul_pos (ht 0 1) hd
  have hq : 0 < q := mul_pos (ht 1 1) hd
  have hu : 0 < u := mul_pos (ht 1 0) hr₀
  have hv : 0 < v := mul_pos (ht 1 0) hb
  have hw : 0 < w := mul_pos (ht 0 0) hr₁
  have hz : 0 < z := mul_pos (ht 0 0) ha
  have hP : E (e 0 1) = WithLp.toLp 2 ![p, 0] := by
    rw [he 0 1]
    ext i
    fin_cases i
    · change r 1 * (t 0 1 * b) - r 0 * (t 0 1 * -a) = p
      dsimp [p, d]
      ring
    · change a * (t 0 1 * b) + b * (t 0 1 * -a) = 0
      ring
  have hQ : E (e 1 1) = WithLp.toLp 2 ![-q, 0] := by
    rw [he 1 1]
    ext i
    fin_cases i
    · change r 1 * (t 1 1 * -b) - r 0 * (t 1 1 * a) = -q
      dsimp [q, d]
      ring
    · change a * (t 1 1 * -b) + b * (t 1 1 * a) = 0
      ring
  have hU : E (e 1 0) = WithLp.toLp 2 ![-u, v] := by
    rw [he 1 0]
    ext i
    fin_cases i <;> simp [E, normalizedNumeratorRay, u, v, PiLp.smul_apply]
  have hW : E (e 0 0) = WithLp.toLp 2 ![w, z] := by
    rw [he 0 0]
    ext i
    fin_cases i <;> simp [E, normalizedNumeratorRay, w, z, PiLp.smul_apply]
  have hEr : E r 0 = 0 := by simp [E]; ring
  have hEry : 0 < E r 1 := by change 0 < d; exact hd
  have hpw : p ≤ w := by
    have h := chord_recession_outward (e 0) E r
      ((chordPolygon_recession_iff e r).mp hr 0) hEr hEry
      (by rw [hP]; rfl) (by rw [hW]; exact hz)
    rw [hP, hW] at h
    change 0 ≤ p * (w - p) at h
    nlinarith
  have hqu : q ≤ u := by
    have h := chord_recession_outward (e 1) E r
      ((chordPolygon_recession_iff e r).mp hr 1) hEr hEry
      (by rw [hQ]; rfl) (by rw [hU]; exact hv)
    rw [hQ, hU] at h
    change 0 ≤ -q * (-u - -q) at h
    nlinarith
  have hB : IsBody (E '' A) := ⟨hA.1.image E.continuous,
    hA.2.1.linear_image E.toLinearMap, hA.2.2.image E⟩
  have hBzero : (0 : Plane) ∈ E '' A := by
    exact ⟨0, interior_subset hzero, map_zero E⟩
  obtain ⟨hN₀, hN₁, hD₀, hD₁⟩ :=
    recessionStripEquiv_sector_images a b r ha hb hr₀ hr₁
      (t 0 0) (t 1 0) (ht 0 0) (ht 1 0)
  change E '' normalizedNumeratorSector a b 0 = stripNumeratorRight w z at hN₀
  change E '' normalizedNumeratorSector a b 1 = stripNumeratorLeft u v at hN₁
  change E '' normalizedDenominatorSector a b 0 = stripDenominatorLeft w z at hD₀
  change E '' normalizedDenominatorSector a b 1 = stripDenominatorRight u v at hD₁
  have hden (i : Fin 3) : 0 < area ((E '' A) ∩ (E '' normalizedDenominatorSector a b i)) := by
    rw [← image_inter E.injective]
    change 0 < area (E.toContinuousAffineEquiv '' (A ∩ normalizedDenominatorSector a b i))
    rw [area_affine_image]
    exact mul_pos (affineAreaScale_pos _) (normalized_denominator_area_pos hA.1 hzero ha hb i)
  have hden₀ := hden 0
  have hden₁ := hden 1
  rw [hD₀] at hden₀
  rw [hD₁] at hden₁
  have hPrad : IsRadialEndpoint (E '' A) (WithLp.toLp 2 ![p, 0]) := by
    rw [← hP]
    exact (hend 0 1).linear_image E
  have hQrad : IsRadialEndpoint (E '' A) (WithLp.toLp 2 ![-q, 0]) := by
    rw [← hQ]
    exact (hend 1 1).linear_image E
  have hUmem : WithLp.toLp 2 ![-u, v] ∈ E '' A := by
    rw [← hU]
    exact mem_image_of_mem E (hend 1 0).1
  have hWmem : WithLp.toLp 2 ![w, z] ∈ E '' A := by
    rw [← hW]
    exact mem_image_of_mem E (hend 0 0).1
  have hbound := (strip_sector_area_ratios hB hBzero hp hq hu hv hw hz hqu hpw
    hPrad hQrad hUmem hWmem hden₀ hden₁).2
  rw [← hN₀, ← hN₁, ← hD₀, ← hD₁,
    linear_image_sector_ratio, linear_image_sector_ratio] at hbound
  exact hbound

theorem recession_firstQuadrant_ratio_sum {A : Set Plane} (hA : IsBody A)
    (hzero : (0 : Plane) ∈ interior A) {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (e : Fin 3 → Basis (Fin 2) ℝ Plane) (t : Fin 3 → Fin 2 → ℝ)
    (ht : ∀ i k, 0 < t i k)
    (he : ∀ i k, e i k = t i k • normalizedNumeratorRay a b i k)
    (hend : ∀ i k, IsRadialEndpoint A (e i k))
    (r : Plane) (hr : IsRecessionDirection (chordPolygon e) r)
    (hr₀ : 0 < r 0) (hr₁ : 0 < r 1) :
    2 ≤ normalizedSectorRatioSum A a b := by
  have h := recession_firstQuadrant_two_ratio_bound hA hzero ha hb e t ht he hend r hr hr₀ hr₁
  have hn := div_nonneg (area_nonneg (A ∩ normalizedNumeratorSector a b 2))
    (area_nonneg (A ∩ normalizedDenominatorSector a b 2))
  simp only [normalizedSectorRatioSum, Fin.sum_univ_three]
  linarith

end ThreeSlices
