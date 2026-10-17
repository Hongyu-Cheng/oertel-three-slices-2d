import ThreeSlices.AffineNormalization
import ThreeSlices.TsintsifasGeometry

open Set Module

namespace ThreeSlices

def normalizedChordTriangle (a b : ℝ) : Set Plane :=
  {x | x 0 ≤ 1 ∧ x 1 ≤ 1 ∧ -a * x 0 - b * x 1 ≤ 1}

def standardChordTriangle : Set Plane :=
  {x | 0 ≤ x 0 ∧ 0 ≤ x 1 ∧ x 0 + x 1 ≤ 1}

private noncomputable def diagonalPlaneEquiv (s : Fin 2 → ℝ)
    (hs : ∀ i, s i ≠ 0) : Plane ≃L[ℝ] Plane :=
  ((EuclideanSpace.equiv (Fin 2) ℝ).trans
    (ContinuousLinearEquiv.piCongrRight fun i =>
      (LinearEquiv.smulOfNeZero ℝ ℝ (s i) (hs i)).toContinuousLinearEquiv)).trans
    (EuclideanSpace.equiv (Fin 2) ℝ).symm

@[simp] private lemma diagonalPlaneEquiv_apply (s : Fin 2 → ℝ)
    (hs : ∀ i, s i ≠ 0) (x : Plane) (i : Fin 2) :
    diagonalPlaneEquiv s hs x i = s i * x i := by
  simp [diagonalPlaneEquiv]

/-- Diagonal scaling followed by translation sends the three chord lines to the unit simplex. -/
noncomputable def chordTriangleEquiv (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    Plane ≃ᴬ[ℝ] Plane :=
  (diagonalPlaneEquiv (fun i => -(![a, b] i) / (1 + a + b)) (by
    intro i
    have hd : 1 + a + b ≠ 0 := by linarith
    fin_cases i <;> simp [ha.ne', hb.ne', hd])).toContinuousAffineEquiv.trans
    (ContinuousAffineEquiv.constVAdd ℝ Plane
      ((EuclideanSpace.equiv (Fin 2) ℝ).symm (fun i => ![a, b] i / (1 + a + b))))

@[simp] lemma chordTriangleEquiv_apply (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (x : Plane) (i : Fin 2) :
    chordTriangleEquiv a b ha hb x i = ![a, b] i * (1 - x i) / (1 + a + b) := by
  change (((EuclideanSpace.equiv (Fin 2) ℝ).symm
      (fun i => ![a, b] i / (1 + a + b))) +
    diagonalPlaneEquiv (fun i => -(![a, b] i) / (1 + a + b)) _ x) i = _
  simp only [PiLp.add_apply, diagonalPlaneEquiv_apply]
  change ![a, b] i / (1 + a + b) + (-(![a, b] i) / (1 + a + b)) * x i = _
  ring

lemma chordTriangleEquiv_mem (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (x : Plane) :
    chordTriangleEquiv a b ha hb x ∈ standardChordTriangle ↔
      x ∈ normalizedChordTriangle a b := by
  have hd : 0 < 1 + a + b := by linarith
  change (0 ≤ chordTriangleEquiv a b ha hb x 0 ∧
    0 ≤ chordTriangleEquiv a b ha hb x 1 ∧
    chordTriangleEquiv a b ha hb x 0 + chordTriangleEquiv a b ha hb x 1 ≤ 1) ↔
    (x 0 ≤ 1 ∧ x 1 ≤ 1 ∧ -a * x 0 - b * x 1 ≤ 1)
  simp only [chordTriangleEquiv_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
  have h₀ : 0 ≤ a * (1 - x 0) / (1 + a + b) ↔ x 0 ≤ 1 := by
    rw [le_div_iff₀ hd]
    constructor <;> intro h <;> nlinarith
  have h₁ : 0 ≤ b * (1 - x 1) / (1 + a + b) ↔ x 1 ≤ 1 := by
    rw [le_div_iff₀ hd]
    constructor <;> intro h <;> nlinarith
  have h₂ : a * (1 - x 0) / (1 + a + b) +
      b * (1 - x 1) / (1 + a + b) ≤ 1 ↔ -a * x 0 - b * x 1 ≤ 1 := by
    rw [← add_div, div_le_iff₀ hd]
    constructor <;> intro h <;> nlinarith
  exact and_congr h₀ (and_congr h₁ h₂)

theorem chordTriangleEquiv_image (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    chordTriangleEquiv a b ha hb '' normalizedChordTriangle a b = standardChordTriangle := by
  change (chordTriangleEquiv a b ha hb).toEquiv '' normalizedChordTriangle a b = _
  rw [Equiv.image_eq_preimage_symm]
  ext y
  have hy := (chordTriangleEquiv_mem a b ha hb
    ((chordTriangleEquiv a b ha hb).symm y)).symm
  rw [(chordTriangleEquiv a b ha hb).apply_symm_apply] at hy
  exact hy

/-- A nonpositive coefficient leaves a coordinate ray inside the three halfplanes. -/
theorem normalizedChordTriangle_coefficients_pos (a b : ℝ)
    (hP : Bornology.IsBounded (normalizedChordTriangle a b)) : 0 < a ∧ 0 < b := by
  obtain ⟨M, hM⟩ := isBounded_iff_forall_norm_le.mp hP
  have ht : 0 < |M| + 1 := by positivity
  constructor
  · by_contra ha
    have ha : a ≤ 0 := le_of_not_gt ha
    let x : Plane := WithLp.toLp 2 ![-(|M| + 1), 0]
    have hx : x ∈ normalizedChordTriangle a b := by
      change -(|M| + 1) ≤ 1 ∧ 0 ≤ 1 ∧ -a * -(|M| + 1) - b * 0 ≤ 1
      have hm := mul_nonpos_of_nonpos_of_nonneg ha ht.le
      constructor
      · linarith
      · constructor
        · norm_num
        · nlinarith
    have hn : |M| + 1 ≤ ‖x‖ := by
      have hn := PiLp.norm_apply_le x 0
      change ‖-(|M| + 1)‖ ≤ ‖x‖ at hn
      rwa [norm_neg, Real.norm_eq_abs, abs_of_pos ht] at hn
    linarith [hM x hx, le_abs_self M]
  · by_contra hb
    have hb : b ≤ 0 := le_of_not_gt hb
    let x : Plane := WithLp.toLp 2 ![0, -(|M| + 1)]
    have hx : x ∈ normalizedChordTriangle a b := by
      change 0 ≤ 1 ∧ -(|M| + 1) ≤ 1 ∧ -a * 0 - b * -(|M| + 1) ≤ 1
      have hm := mul_nonpos_of_nonpos_of_nonneg hb ht.le
      constructor
      · norm_num
      · constructor
        · linarith
        · nlinarith
    have hn : |M| + 1 ≤ ‖x‖ := by
      have hn := PiLp.norm_apply_le x 1
      change ‖-(|M| + 1)‖ ≤ ‖x‖ at hn
      rwa [norm_neg, Real.norm_eq_abs, abs_of_pos ht] at hn
    linarith [hM x hx, le_abs_self M]

noncomputable def chordNormal (e : Basis (Fin 2) ℝ Plane) : Plane →L[ℝ] ℝ :=
  (e.coord 0 + e.coord 1).toContinuousLinearMap

@[simp] lemma chordNormal_apply (e : Basis (Fin 2) ℝ Plane) (x : Plane) :
    chordNormal e x = e.repr x 0 + e.repr x 1 := rfl

lemma bounded_chordPolygon_recession_eq_zero {ι : Type*}
    (e : ι → Basis (Fin 2) ℝ Plane) (hP : Bornology.IsBounded (chordPolygon e))
    {r : Plane} (hr : IsRecessionDirection (chordPolygon e) r) : r = 0 := by
  by_contra hne
  obtain ⟨M, hM⟩ := isBounded_iff_forall_norm_le.mp hP
  have hn : 0 < ‖r‖ := norm_pos_iff.mpr hne
  have ht : 0 < (|M| + 1) / ‖r‖ := div_pos (by positivity) hn
  have hx := hr 0 (zero_mem_chordPolygon e) ((|M| + 1) / ‖r‖) ht.le
  simp only [zero_add] at hx
  have hnorm : ‖((|M| + 1) / ‖r‖) • r‖ = |M| + 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht, div_mul_cancel₀ _ hn.ne']
  have hb := hM _ hx
  rw [hnorm] at hb
  linarith [le_abs_self M]

/-- Boundedness forbids parallel chord normals, since their common kernel gives a recession ray. -/
theorem bounded_chordPolygon_first_normals_independent
    (e : Fin 3 → Basis (Fin 2) ℝ Plane) (hP : Bornology.IsBounded (chordPolygon e)) :
    LinearIndependent ℝ ![chordNormal (e 0), chordNormal (e 1)] := by
  rw [linearIndependent_fin2]
  constructor
  · change chordNormal (e 1) ≠ 0
    intro he
    have h := congrArg (fun f : Plane →L[ℝ] ℝ => f (e 1 0)) he
    simp [chordNormal] at h
  · intro c he
    change c • chordNormal (e 1) = chordNormal (e 0) at he
    let r : Plane := e 1 0 - e 1 1
    have hrne : r ≠ 0 := by
      intro h
      have h' := congrArg ((e 1).coord 0) h
      simp [r] at h'
    have hr₁ : chordNormal (e 1) r = 0 := by simp [r]
    have hr₀ : chordNormal (e 0) r = 0 := by
      have h := congrArg (fun f : Plane →L[ℝ] ℝ => f r) he
      simpa [hr₁] using h.symm
    have hrec (v : Plane) (h₀ : chordNormal (e 0) v = 0)
        (h₁ : chordNormal (e 1) v = 0) (h₂ : chordNormal (e 2) v ≤ 0) :
        IsRecessionDirection (chordPolygon e) v := by
      apply (chordPolygon_recession_iff e v).mpr
      intro i
      change chordNormal (e i) v ≤ 0
      fin_cases i
      · exact h₀.le
      · exact h₁.le
      · exact h₂
    by_cases h₂ : chordNormal (e 2) r ≤ 0
    · exact hrne (bounded_chordPolygon_recession_eq_zero e hP (hrec r hr₀ hr₁ h₂))
    · have hneg : chordNormal (e 2) (-r) ≤ 0 := by simp only [map_neg]; linarith
      have hz := bounded_chordPolygon_recession_eq_zero e hP
        (hrec (-r) (by simp only [map_neg, hr₀, neg_zero])
          (by simp only [map_neg, hr₁, neg_zero]) hneg)
      exact hrne (neg_eq_zero.mp hz)

/-- The constructive bounded-chord normalization, retaining its normal weights and coordinates. -/
theorem bounded_chordPolygon_coordinate_data
    (e : Fin 3 → Basis (Fin 2) ℝ Plane) (hP : Bornology.IsBounded (chordPolygon e)) :
    ∃ A B : ℝ, 0 < A ∧ 0 < B ∧
      (∀ x, chordNormal (e 2) x = -A * chordNormal (e 0) x - B * chordNormal (e 1) x) ∧
      ∃ E : Plane ≃ᴬ[ℝ] Plane,
        E '' chordPolygon e = standardChordTriangle ∧
        (∀ x, E x 0 = A * (1 - chordNormal (e 0) x) / (1 + A + B)) ∧
        (∀ x, E x 1 = B * (1 - chordNormal (e 1) x) / (1 + A + B)) := by
  let C := formCoordinatesEquiv (chordNormal (e 0)) (chordNormal (e 1))
    (bounded_chordPolygon_first_normals_independent e hP)
  let k := (chordNormal (e 2)).comp C.symm.toContinuousLinearMap
  let A := -k (EuclideanSpace.single 0 1)
  let B := -k (EuclideanSpace.single 1 1)
  have hcoords (x : Plane) (i : Fin 2) :
      C x i = ![chordNormal (e 0), chordNormal (e 1)] i x := rfl
  have hthird (x : Plane) : -A * C x 0 - B * C x 1 = chordNormal (e 2) x := by
    have hk := linear_form_coordinate_expansion k (C x)
    change chordNormal (e 2) (C.symm (C x)) =
      k (EuclideanSpace.single 0 1) * C x 0 + k (EuclideanSpace.single 1 1) * C x 1 at hk
    rw [C.symm_apply_apply] at hk
    simpa only [A, B, neg_neg, neg_mul, sub_neg_eq_add] using hk.symm
  have hmem (x : Plane) : C x ∈ normalizedChordTriangle A B ↔ x ∈ chordPolygon e := by
    change (C x 0 ≤ 1 ∧ C x 1 ≤ 1 ∧ -A * C x 0 - B * C x 1 ≤ 1) ↔ _
    rw [hthird x, hcoords x 0, hcoords x 1]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    constructor
    · intro hx
      apply mem_iInter.mpr
      intro i
      fin_cases i
      · exact hx.1
      · exact hx.2.1
      · exact hx.2.2
    · intro hx
      exact ⟨mem_iInter.mp hx 0, mem_iInter.mp hx 1, mem_iInter.mp hx 2⟩
  have himage : C '' chordPolygon e = normalizedChordTriangle A B := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact (hmem x).mpr hx
    · intro hy
      refine ⟨C.symm y, ?_, C.apply_symm_apply y⟩
      apply (hmem (C.symm y)).mp
      rwa [C.apply_symm_apply]
  have hbdd : Bornology.IsBounded (normalizedChordTriangle A B) := by
    rw [← himage]
    exact C.toContinuousLinearMap.lipschitzWith.isBounded_image hP
  obtain ⟨hA, hB⟩ := normalizedChordTriangle_coefficients_pos A B hbdd
  refine ⟨A, B, hA, hB, ?_,
    C.toContinuousAffineEquiv.trans (chordTriangleEquiv A B hA hB), ?_, ?_, ?_⟩
  · intro x
    simpa only [hcoords, Matrix.cons_val_zero, Matrix.cons_val_one] using (hthird x).symm
  · change (chordTriangleEquiv A B hA hB ∘ C) '' chordPolygon e = _
    rw [Set.image_comp, himage]
    exact chordTriangleEquiv_image A B hA hB
  · intro x
    change chordTriangleEquiv A B hA hB (C x) 0 = _
    simp only [chordTriangleEquiv_apply, hcoords, Matrix.cons_val_zero]
  · intro x
    change chordTriangleEquiv A B hA hB (C x) 1 = _
    simp [chordTriangleEquiv_apply, hcoords]

end ThreeSlices
