import ThreeSlices.TsintsifasGeometry
import ThreeSlices.RadialEndpoints

open Set Module

namespace ThreeSlices

/-- The endpoint ray pairs of the three alternating numerator sectors. -/
def normalizedNumeratorRay (a b : ℝ) : Fin 3 → Fin 2 → Plane :=
  ![![WithLp.toLp 2 ![1, 0], WithLp.toLp 2 ![b, -a]],
    ![WithLp.toLp 2 ![0, 1], WithLp.toLp 2 ![-b, a]],
    ![WithLp.toLp 2 ![-1, 0], WithLp.toLp 2 ![0, -1]]]

/-- The closed numerator cones in the normalized concurrent fan. -/
def normalizedNumeratorSector (a b : ℝ) : Fin 3 → Set Plane :=
  ![{x | x 1 ≤ 0 ∧ 0 ≤ a * x 0 + b * x 1},
    {x | x 0 ≤ 0 ∧ 0 ≤ a * x 0 + b * x 1},
    {x | x 0 ≤ 0 ∧ x 1 ≤ 0}]

/-- The open numerator cones in the normalized concurrent fan. -/
def normalizedOpenNumeratorSector (a b : ℝ) : Fin 3 → Set Plane :=
  ![{x | x 1 < 0 ∧ 0 < a * x 0 + b * x 1},
    {x | x 0 < 0 ∧ 0 < a * x 0 + b * x 1},
    {x | x 0 < 0 ∧ x 1 < 0}]

lemma normalizedNumeratorRay_ne_zero {a b : ℝ} (_ha : 0 < a) (hb : 0 < b)
    (i : Fin 3) (k : Fin 2) : normalizedNumeratorRay a b i k ≠ 0 := by
  intro he
  have h₀ := congrArg (fun x : Plane => x 0) he
  have h₁ := congrArg (fun x : Plane => x 1) he
  fin_cases i <;> fin_cases k <;>
    simp [normalizedNumeratorRay] at h₀ h₁ <;> linarith

lemma scaled_normalizedNumeratorRay_linearIndependent {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b) (i : Fin 3) (t : Fin 2 → ℝ) (ht : ∀ k, 0 < t k) :
    LinearIndependent ℝ (fun k => t k • normalizedNumeratorRay a b i k) := by
  rw [linearIndependent_fin2]
  constructor
  · exact smul_ne_zero (ht 1).ne' (normalizedNumeratorRay_ne_zero ha hb i 1)
  · intro s he
    have h₀ := congrArg (fun x : Plane => x 0) he
    have h₁ := congrArg (fun x : Plane => x 1) he
    fin_cases i
    · simp [normalizedNumeratorRay, PiLp.smul_apply] at h₀ h₁
      have hs : s = 0 := by
        rcases h₁ with hs | hs | hs
        · exact hs
        · exact False.elim ((ht 1).ne' hs)
        · exact False.elim (ha.ne' hs)
      simp [hs] at h₀
      linarith [ht 0]
    · simp [normalizedNumeratorRay, PiLp.smul_apply] at h₀ h₁
      have hs : s = 0 := by
        rcases h₀ with hs | hs | hs
        · exact hs
        · exact False.elim ((ht 1).ne' hs)
        · exact False.elim (hb.ne' hs)
      simp [hs] at h₁
      linarith [ht 0]
    · simp [normalizedNumeratorRay, PiLp.smul_apply] at h₀
      linarith [ht 0]

/-- All six positive rays have maximal endpoints, and each alternating pair is a basis. -/
theorem exists_six_radial_bases {A : Set Plane} (hA : IsBody A)
    (hzero : (0 : Plane) ∈ interior A) {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    ∃ (e : Fin 3 → Basis (Fin 2) ℝ Plane) (t : Fin 3 → Fin 2 → ℝ),
      (∀ i k, 0 < t i k) ∧
      (∀ i k, e i k = t i k • normalizedNumeratorRay a b i k) ∧
      (∀ i k, IsRadialEndpoint A (e i k)) := by
  classical
  have hr : ∀ i : Fin 3, ∀ k : Fin 2, ∃ t : ℝ,
      0 < t ∧ t • normalizedNumeratorRay a b i k ∈ A ∧
      ∀ s : ℝ, s • normalizedNumeratorRay a b i k ∈ A → s ≤ t :=
    fun i k => exists_radial_endpoint hA hzero (normalizedNumeratorRay_ne_zero ha hb i k)
  choose t ht hmem hmax using hr
  let e : Fin 3 → Basis (Fin 2) ℝ Plane := fun i =>
    basisOfLinearIndependentOfCardEqFinrank
      (scaled_normalizedNumeratorRay_linearIndependent ha hb i (t i) (ht i))
      (by simp [Plane])
  have he : ∀ i k, e i k = t i k • normalizedNumeratorRay a b i k := by
    intro i k
    exact congrFun (coe_basisOfLinearIndependentOfCardEqFinrank _ _) k
  refine ⟨e, t, ht, he, fun i k => ?_⟩
  rw [he]
  refine ⟨hmem i k, fun s hs hsmem => ?_⟩
  rw [smul_smul] at hsmem
  have hle := hmax i k (s * t i k) hsmem
  have hgt := mul_lt_mul_of_pos_right hs (ht i k)
  linarith

private def normalizedConeCoordinates (a b : ℝ) (i : Fin 3) (x : Plane) : Fin 2 → ℝ :=
  ![![a * x 0 + b * x 1, -x 1],
    ![a * x 0 + b * x 1, -x 0], ![-x 0, -x 1]] i

private def normalizedConeFactor (a b : ℝ) : Fin 3 → ℝ := ![a, b, 1]

private lemma normalizedConeFactor_pos {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (i : Fin 3) :
    0 < normalizedConeFactor a b i := by
  fin_cases i
  · simpa [normalizedConeFactor] using ha
  · simpa [normalizedConeFactor] using hb
  · norm_num [normalizedConeFactor]

private lemma scaled_basis_cone_coordinates (a b : ℝ) (i : Fin 3)
    (e : Basis (Fin 2) ℝ Plane) (t : Fin 2 → ℝ)
    (he : ∀ k, e k = t k • normalizedNumeratorRay a b i k) (x : Plane) (k : Fin 2) :
    normalizedConeCoordinates a b i x k =
      (normalizedConeFactor a b i * t k) * e.repr x k := by
  have h₀ := congrArg (fun y : Plane => y 0) (basis_two_repr e x)
  have h₁ := congrArg (fun y : Plane => y 1) (basis_two_repr e x)
  simp only [PiLp.add_apply, PiLp.smul_apply] at h₀ h₁
  rw [he 0, he 1] at h₀ h₁
  simp only [PiLp.smul_apply] at h₀ h₁
  fin_cases i <;> fin_cases k <;>
    simp [normalizedNumeratorRay, normalizedConeCoordinates, normalizedConeFactor] at h₀ h₁ ⊢
  · linear_combination -a * h₀ - b * h₁
  · linear_combination h₁
  · linear_combination -a * h₀ - b * h₁
  · linear_combination h₀
  · linear_combination h₀
  · linear_combination h₁

private lemma normalized_sector_iff_coordinates (a b : ℝ) (i : Fin 3) (x : Plane) :
    x ∈ normalizedNumeratorSector a b i ↔
      0 ≤ normalizedConeCoordinates a b i x 0 ∧ 0 ≤ normalizedConeCoordinates a b i x 1 := by
  fin_cases i <;> simp [normalizedNumeratorSector, normalizedConeCoordinates] <;> tauto

private lemma normalized_openSector_iff_coordinates (a b : ℝ) (i : Fin 3) (x : Plane) :
    x ∈ normalizedOpenNumeratorSector a b i ↔
      0 < normalizedConeCoordinates a b i x 0 ∧ 0 < normalizedConeCoordinates a b i x 1 := by
  fin_cases i <;> simp [normalizedOpenNumeratorSector, normalizedConeCoordinates] <;> tauto

/-- Positive rescaling of the endpoint rays gives exactly the prescribed closed sector. -/
theorem chordSector_eq_normalized {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (i : Fin 3)
    (e : Basis (Fin 2) ℝ Plane) (t : Fin 2 → ℝ) (ht : ∀ k, 0 < t k)
    (he : ∀ k, e k = t k • normalizedNumeratorRay a b i k) :
    chordSector e = normalizedNumeratorSector a b i := by
  ext x
  rw [normalized_sector_iff_coordinates,
    scaled_basis_cone_coordinates a b i e t he x 0,
    scaled_basis_cone_coordinates a b i e t he x 1,
    mul_nonneg_iff_of_pos_left (mul_pos (normalizedConeFactor_pos ha hb i) (ht 0)),
    mul_nonneg_iff_of_pos_left (mul_pos (normalizedConeFactor_pos ha hb i) (ht 1))]
  rfl

/-- Positive rescaling of the endpoint rays also preserves the open sector. -/
theorem openChordSector_eq_normalized {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (i : Fin 3)
    (e : Basis (Fin 2) ℝ Plane) (t : Fin 2 → ℝ) (ht : ∀ k, 0 < t k)
    (he : ∀ k, e k = t k • normalizedNumeratorRay a b i k) :
    openChordSector e = normalizedOpenNumeratorSector a b i := by
  ext x
  rw [normalized_openSector_iff_coordinates,
    scaled_basis_cone_coordinates a b i e t he x 0,
    scaled_basis_cone_coordinates a b i e t he x 1,
    mul_pos_iff_of_pos_left (mul_pos (normalizedConeFactor_pos ha hb i) (ht 0)),
    mul_pos_iff_of_pos_left (mul_pos (normalizedConeFactor_pos ha hb i) (ht 1))]
  rfl

/-- The closed denominator cones opposite the three alternating numerator cones. -/
def normalizedDenominatorSector (a b : ℝ) : Fin 3 → Set Plane :=
  ![{x | 0 ≤ x 1 ∧ a * x 0 + b * x 1 ≤ 0},
    {x | 0 ≤ x 0 ∧ a * x 0 + b * x 1 ≤ 0},
    {x | 0 ≤ x 0 ∧ 0 ≤ x 1}]

lemma normalizedDenominatorSector_eq_opposite (a b : ℝ) (i : Fin 3) :
    normalizedDenominatorSector a b i = {x | -x ∈ normalizedNumeratorSector a b i} := by
  ext x
  fin_cases i <;> simp [normalizedDenominatorSector, normalizedNumeratorSector,
    PiLp.neg_apply] <;> intro _ <;> constructor <;> intro h <;> linarith

/-- Every closed denominator cone avoids all open numerator cones, including their boundaries. -/
theorem normalizedDenominatorSector_avoids_openNumerators (a b : ℝ) (j : Fin 3) :
    normalizedDenominatorSector a b j ⊆ (⋃ i, normalizedOpenNumeratorSector a b i)ᶜ := by
  intro x hx hh
  rcases mem_iUnion.mp hh with ⟨i, hi⟩
  fin_cases j <;> fin_cases i <;>
    simp [normalizedDenominatorSector] at hx <;>
    simp [normalizedOpenNumeratorSector] at hi <;> linarith

/-- Every nonzero recession direction of the normalized fan lies in an open denominator cone. -/
theorem recession_mem_open_normalized_denominator (a b : ℝ)
    (e : Fin 3 → Basis (Fin 2) ℝ Plane)
    (hsector : ∀ i, chordSector (e i) = normalizedNumeratorSector a b i)
    {r : Plane} (hr : IsRecessionDirection (chordPolygon e) r) (hne : r ≠ 0) :
    (0 < r 1 ∧ a * r 0 + b * r 1 < 0) ∨
      (0 < r 0 ∧ a * r 0 + b * r 1 < 0) ∨ (0 < r 0 ∧ 0 < r 1) := by
  have hn : ∀ i, r ∉ normalizedNumeratorSector a b i := by
    intro i
    rw [← hsector i]
    exact recession_not_mem_sector e hr hne i
  by_cases hx : r 0 ≤ 0
  · have hy : 0 < r 1 := lt_of_not_ge fun hy => hn 2 ⟨hx, hy⟩
    have hs : a * r 0 + b * r 1 < 0 := lt_of_not_ge fun hs => hn 1 ⟨hx, hs⟩
    exact Or.inl ⟨hy, hs⟩
  · have hx' : 0 < r 0 := lt_of_not_ge hx
    by_cases hy : r 1 ≤ 0
    · have hs : a * r 0 + b * r 1 < 0 := lt_of_not_ge fun hs => hn 0 ⟨hy, hs⟩
      exact Or.inr (Or.inl ⟨hx', hs⟩)
    · exact Or.inr (Or.inr ⟨hx', lt_of_not_ge hy⟩)

end ThreeSlices
