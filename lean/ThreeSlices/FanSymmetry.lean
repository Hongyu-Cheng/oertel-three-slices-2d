import ThreeSlices.TsintsifasReduction
import ThreeSlices.AffineArea

open Set MeasureTheory

namespace ThreeSlices

/-- Positive diagonal normalization sends the slant `a*x+b*y=0` to `X+Y=0`. -/
noncomputable def fanDiagonal (a b : ℝ) (ha : 0 < a) (hb : 0 < b) : Plane ≃L[ℝ] Plane :=
  ({ toFun := fun x => WithLp.toLp 2 ![a * x 0, b * x 1]
     invFun := fun x => WithLp.toLp 2 ![x 0 / a, x 1 / b]
     left_inv := by intro x; ext i; fin_cases i <;> simp [ha.ne', hb.ne']
     right_inv := by intro x; ext i; fin_cases i <;> simp <;> field_simp
     map_add' := by intro x y; ext i; fin_cases i <;> simp [mul_add]
     map_smul' := by intro c x; ext i; fin_cases i <;> simp [mul_left_comm]
   } : Plane ≃ₗ[ℝ] Plane).toContinuousLinearEquiv

@[simp] lemma fanDiagonal_apply (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (x : Plane)
    (i : Fin 2) : fanDiagonal a b ha hb x i = ![a * x 0, b * x 1] i := rfl

@[simp] lemma fanDiagonal_symm_apply (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (x : Plane)
    (i : Fin 2) : (fanDiagonal a b ha hb).symm x i = ![x 0 / a, x 1 / b] i := rfl

/-- The order-three symmetry cycling the canonical concurrent fan. -/
noncomputable def fanCycle : Plane ≃L[ℝ] Plane :=
  ({ toFun := fun x => WithLp.toLp 2 ![x 1, -x 0 - x 1]
     invFun := fun x => WithLp.toLp 2 ![-x 0 - x 1, x 0]
     left_inv := by intro x; ext i; fin_cases i <;> simp [sub_eq_add_neg, add_assoc, add_comm]
     right_inv := by intro x; ext i; fin_cases i <;> simp [sub_eq_add_neg, add_left_comm, add_comm]
     map_add' := by intro x y; ext i; fin_cases i <;> simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
     map_smul' := by intro c x; ext i; fin_cases i <;> simp [sub_eq_add_neg, mul_add]
   } : Plane ≃ₗ[ℝ] Plane).toContinuousLinearEquiv

@[simp] lemma fanCycle_apply (x : Plane) (i : Fin 2) :
    fanCycle x i = ![x 1, -x 0 - x 1] i := rfl

@[simp] lemma fanCycle_symm_apply (x : Plane) (i : Fin 2) :
    fanCycle.symm x i = ![-x 0 - x 1, x 0] i := rfl

def fanCycleIndex : Equiv.Perm (Fin 3) where
  toFun i := ![2, 0, 1] i
  invFun i := ![1, 2, 0] i
  left_inv i := by fin_cases i <;> rfl
  right_inv i := by fin_cases i <;> rfl

/-- The ray permutation includes the endpoint swaps in the first two sectors. -/
def fanCycleRayIndex : Equiv.Perm (Fin 3 × Fin 2) where
  toFun p := (fanCycleIndex p.1, ![![1, 0], ![1, 0], ![0, 1]] p.1 p.2)
  invFun p := (fanCycleIndex.symm p.1, ![![1, 0], ![0, 1], ![1, 0]] p.1 p.2)
  left_inv p := by rcases p with ⟨i, k⟩; fin_cases i <;> fin_cases k <;> rfl
  right_inv p := by rcases p with ⟨i, k⟩; fin_cases i <;> fin_cases k <;> rfl

def fanDiagonalRayFactor (a b : ℝ) : Fin 3 → Fin 2 → ℝ :=
  ![![a, a * b], ![b, a * b], ![a, b]]

lemma fanDiagonalRayFactor_pos {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (i : Fin 3) (k : Fin 2) : 0 < fanDiagonalRayFactor a b i k := by
  fin_cases i <;> fin_cases k <;> simp [fanDiagonalRayFactor] <;> positivity

lemma fanDiagonal_ray (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (i : Fin 3) (k : Fin 2) :
    fanDiagonal a b ha hb (normalizedNumeratorRay a b i k) =
      fanDiagonalRayFactor a b i k • normalizedNumeratorRay 1 1 i k := by
  ext j
  fin_cases i <;> fin_cases k <;> fin_cases j <;>
    simp [normalizedNumeratorRay, fanDiagonalRayFactor, PiLp.smul_apply] <;> ring

lemma fanCycle_ray (i : Fin 3) (k : Fin 2) :
    fanCycle (normalizedNumeratorRay 1 1 i k) =
      normalizedNumeratorRay 1 1 (fanCycleRayIndex (i, k)).1 (fanCycleRayIndex (i, k)).2 := by
  ext j
  fin_cases i <;> fin_cases k <;> fin_cases j <;>
    simp [normalizedNumeratorRay, fanCycleRayIndex, fanCycleIndex]

private lemma image_eq_of_mem_iff (e : Plane ≃L[ℝ] Plane) (S T : Set Plane)
    (h : ∀ x, e x ∈ T ↔ x ∈ S) : e '' S = T := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (h x).2 hx
  · intro hy
    refine ⟨e.symm y, ?_, e.apply_symm_apply y⟩
    apply (h (e.symm y)).1
    simpa only [e.apply_symm_apply] using hy

private lemma positive_mul_le_zero {c t : ℝ} (hc : 0 < c) : c * t ≤ 0 ↔ t ≤ 0 := by
  simpa only [mul_zero] using (mul_le_mul_iff_of_pos_left hc : c * t ≤ c * 0 ↔ t ≤ 0)

lemma fanDiagonal_image_numerator (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (i : Fin 3) :
    fanDiagonal a b ha hb '' normalizedNumeratorSector a b i = normalizedNumeratorSector 1 1 i := by
  apply image_eq_of_mem_iff
  intro x
  fin_cases i <;> simp [normalizedNumeratorSector, positive_mul_le_zero ha,
    positive_mul_le_zero hb]

lemma fanDiagonal_image_denominator (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (i : Fin 3) :
    fanDiagonal a b ha hb '' normalizedDenominatorSector a b i =
      normalizedDenominatorSector 1 1 i := by
  apply image_eq_of_mem_iff
  intro x
  fin_cases i <;> simp [normalizedDenominatorSector, mul_nonneg_iff_of_pos_left ha,
    mul_nonneg_iff_of_pos_left hb]

lemma fanCycle_image_numerator (i : Fin 3) :
    fanCycle '' normalizedNumeratorSector 1 1 i =
      normalizedNumeratorSector 1 1 (fanCycleIndex i) := by
  apply image_eq_of_mem_iff
  intro x
  fin_cases i
  · change (x 1 ≤ 0 ∧ -x 0 - x 1 ≤ 0) ↔ (x 1 ≤ 0 ∧ 0 ≤ 1 * x 0 + 1 * x 1)
    simp only [one_mul]
    constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith
  · change (-x 0 - x 1 ≤ 0 ∧ 0 ≤ 1 * x 1 + 1 * (-x 0 - x 1)) ↔
      (x 0 ≤ 0 ∧ 0 ≤ 1 * x 0 + 1 * x 1)
    simp only [one_mul]
    constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith
  · change (x 1 ≤ 0 ∧ 0 ≤ 1 * x 1 + 1 * (-x 0 - x 1)) ↔ (x 0 ≤ 0 ∧ x 1 ≤ 0)
    simp only [one_mul]
    constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith

lemma fanCycle_image_denominator (i : Fin 3) :
    fanCycle '' normalizedDenominatorSector 1 1 i =
      normalizedDenominatorSector 1 1 (fanCycleIndex i) := by
  apply image_eq_of_mem_iff
  intro x
  fin_cases i
  · change (0 ≤ x 1 ∧ 0 ≤ -x 0 - x 1) ↔ (0 ≤ x 1 ∧ 1 * x 0 + 1 * x 1 ≤ 0)
    simp only [one_mul]
    constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith
  · change (0 ≤ -x 0 - x 1 ∧ 1 * x 1 + 1 * (-x 0 - x 1) ≤ 0) ↔
      (0 ≤ x 0 ∧ 1 * x 0 + 1 * x 1 ≤ 0)
    simp only [one_mul]
    constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith
  · change (0 ≤ x 1 ∧ 1 * x 1 + 1 * (-x 0 - x 1) ≤ 0) ↔ (0 ≤ x 0 ∧ 0 ≤ x 1)
    simp only [one_mul]
    constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith

/-- The common area factor cancels in sector ratios. -/
private lemma linear_area_ratio_image (e : Plane ≃L[ℝ] Plane) (A S T : Set Plane) :
    area (e '' (A ∩ S)) / area (e '' (A ∩ T)) = area (A ∩ S) / area (A ∩ T) := by
  rw [image_inter e.injective, image_inter e.injective]
  exact affine_image_sector_ratio e.toContinuousAffineEquiv A S T

theorem normalizedSectorRatioSum_diagonal (A : Set Plane) (a b : ℝ)
    (ha : 0 < a) (hb : 0 < b) :
    normalizedSectorRatioSum (fanDiagonal a b ha hb '' A) 1 1 =
      normalizedSectorRatioSum A a b := by
  unfold normalizedSectorRatioSum
  apply Finset.sum_congr rfl
  intro i _
  rw [← fanDiagonal_image_numerator a b ha hb i, ← fanDiagonal_image_denominator a b ha hb i,
    ← image_inter (fanDiagonal a b ha hb).injective, ← image_inter (fanDiagonal a b ha hb).injective]
  exact linear_area_ratio_image (fanDiagonal a b ha hb) A _ _

private lemma fanCycle_area_ratio (A : Set Plane) (i : Fin 3) :
    area ((fanCycle '' A) ∩ normalizedNumeratorSector 1 1 (fanCycleIndex i)) /
      area ((fanCycle '' A) ∩ normalizedDenominatorSector 1 1 (fanCycleIndex i)) =
    area (A ∩ normalizedNumeratorSector 1 1 i) / area (A ∩ normalizedDenominatorSector 1 1 i) := by
  rw [← fanCycle_image_numerator i, ← fanCycle_image_denominator i,
    ← image_inter fanCycle.injective, ← image_inter fanCycle.injective]
  exact linear_area_ratio_image fanCycle A _ _

theorem normalizedSectorRatioSum_cycle (A : Set Plane) :
    normalizedSectorRatioSum (fanCycle '' A) 1 1 = normalizedSectorRatioSum A 1 1 := by
  have h₀ := fanCycle_area_ratio A 0
  have h₁ := fanCycle_area_ratio A 1
  have h₂ := fanCycle_area_ratio A 2
  simp [fanCycleIndex] at h₀ h₁ h₂
  simp only [normalizedSectorRatioSum, Fin.sum_univ_three]
  linarith only [h₀, h₁, h₂]

lemma fanCycle_denominator_zero_to_two {r : Plane}
    (hy : 0 < r 1) (hs : r 0 + r 1 < 0) :
    0 < fanCycle r 0 ∧ 0 < fanCycle r 1 := by
  simp only [fanCycle_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
  constructor <;> linarith

end ThreeSlices
