import ThreeSlices.Boundary

open Set
open scoped BigOperators

namespace ThreeSlices

private def point (x y : ℝ) : Plane := WithLp.toLp 2 ![x, y]

private lemma point_zero (x y : ℝ) : point x y 0 = x := by rfl
private lemma point_one (x y : ℝ) : point x y 1 = y := by rfl

/-- The slant in a normalized plane cover has positive coefficients if neither
coordinate halfplane together with it covers the body. -/
theorem normalized_cover_coefficients {A : Set Plane} {a b c : ℝ}
    (hcover : ∀ x : Plane, x 0 < 0 ∨ x 1 < 0 ∨ 0 < a * x 0 + b * x 1 + c)
    (hleft : ∃ x ∈ A, 0 ≤ x 0 ∧ a * x 0 + b * x 1 + c ≤ 0)
    (hbelow : ∃ x ∈ A, 0 ≤ x 1 ∧ a * x 0 + b * x 1 + c ≤ 0) :
    0 < a ∧ 0 < b ∧ 0 < c := by
  have hc : 0 < c := by simpa using hcover 0
  have ha : 0 ≤ a := by
    by_contra h
    have ha' : a < 0 := lt_of_not_ge h
    have hx : 0 ≤ -c / a := div_nonneg_of_nonpos
      (neg_nonpos.mpr hc.le) ha'.le
    have hv := hcover (point (-c / a) 0)
    simp [point_zero, point_one] at hv
    have he : a * (-c / a) = -c := by field_simp [ha'.ne]
    rw [he] at hv
    rcases hv with hv | hv <;> linarith
  have hb : 0 ≤ b := by
    by_contra h
    have hb' : b < 0 := lt_of_not_ge h
    have hy : 0 ≤ -c / b := div_nonneg_of_nonpos
      (neg_nonpos.mpr hc.le) hb'.le
    have hv := hcover (point 0 (-c / b))
    simp [point_zero, point_one] at hv
    have he : b * (-c / b) = -c := by field_simp [hb'.ne]
    rw [he] at hv
    rcases hv with hv | hv <;> linarith
  have ha' : 0 < a := by
    rcases hbelow with ⟨x, _, hx, hv⟩
    have hp := mul_nonneg hb hx
    by_contra h
    have haz : a = 0 := le_antisymm (le_of_not_gt h) ha
    rw [haz, zero_mul, zero_add] at hv
    linarith
  have hb' : 0 < b := by
    rcases hleft with ⟨x, _, hx, hv⟩
    have hp := mul_nonneg ha hx
    by_contra h
    have hbz : b = 0 := le_antisymm (le_of_not_gt h) hb
    rw [hbz, zero_mul, add_zero] at hv
    linarith
  exact ⟨ha', hb', hc⟩

/-- Moving the slant boundary to the origin shrinks it and preserves coverage. -/
theorem normalized_closed_shrink {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hc : 0 < c) :
    {x : Plane | 0 ≤ a * x 0 + b * x 1} ⊆
      {x : Plane | 0 < a * x 0 + b * x 1 + c} ∧
    (∀ x : Plane, x 0 < 0 ∨ x 1 < 0 ∨ 0 ≤ a * x 0 + b * x 1) := by
  constructor
  · intro x hx
    change 0 < a * x 0 + b * x 1 + c
    change 0 ≤ a * x 0 + b * x 1 at hx
    linarith
  · intro x
    by_cases hx : x 0 < 0
    · exact Or.inl hx
    by_cases hy : x 1 < 0
    · exact Or.inr (Or.inl hy)
    exact Or.inr (Or.inr (add_nonneg (mul_nonneg ha (le_of_not_gt hx))
      (mul_nonneg hb (le_of_not_gt hy))))

/-- The three concurrent halfplanes are measurable and never overlap triply. -/
theorem normalized_sector_sets {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    MeasurableSet {x : Plane | x 0 < 0} ∧
    MeasurableSet {x : Plane | x 1 < 0} ∧
    MeasurableSet {x : Plane | 0 ≤ a * x 0 + b * x 1} ∧
    ({x : Plane | x 0 < 0} ∩ {x : Plane | x 1 < 0} ∩
      {x : Plane | 0 ≤ a * x 0 + b * x 1}) = ∅ := by
  have hc₀ : Continuous (fun x : Plane => x 0) := by fun_prop
  have hc₁ : Continuous (fun x : Plane => x 1) := by fun_prop
  refine ⟨(isOpen_lt hc₀ continuous_const).measurableSet,
    (isOpen_lt hc₁ continuous_const).measurableSet, ?_, ?_⟩
  · exact (isClosed_le continuous_const
      ((continuous_const.mul hc₀).add (continuous_const.mul hc₁))).measurableSet
  · apply eq_empty_iff_forall_notMem.mpr
    intro x hx
    rcases hx with ⟨⟨hx₀, hx₁⟩, hxS⟩
    have hax := mul_neg_of_pos_of_neg ha hx₀
    have hbx := mul_neg_of_pos_of_neg hb hx₁
    change 0 ≤ a * x 0 + b * x 1 at hxS
    linarith

private def det (x y : Plane) : ℝ := x 0 * y 1 - y 0 * x 1

/-- Three cyclically positive determinants give a neighborhood of the origin
inside any convex set containing the three vertices. -/
theorem origin_mem_interior_of_determinants {A : Set Plane} (hA : Convex ℝ A)
    {p q r : Plane} (hp : p ∈ A) (hq : q ∈ A) (hr : r ∈ A)
    (hpq : 0 < p 0 * q 1 - q 0 * p 1)
    (hqr : 0 < q 0 * r 1 - r 0 * q 1)
    (hrp : 0 < r 0 * p 1 - p 0 * r 1) : (0 : Plane) ∈ interior A := by
  let D := det p q + det q r + det r p
  have hD : 0 < D := by dsimp [D, det]; linarith
  let n₁ : Plane → ℝ := fun x => det (q - x) (r - x)
  let n₂ : Plane → ℝ := fun x => det (r - x) (p - x)
  let n₃ : Plane → ℝ := fun x => det (p - x) (q - x)
  let U : Set Plane := {x | 0 < n₁ x ∧ 0 < n₂ x ∧ 0 < n₃ x}
  have hc₁ : Continuous n₁ := by
    dsimp [n₁, det]
    fun_prop
  have hc₂ : Continuous n₂ := by
    dsimp [n₂, det]
    fun_prop
  have hc₃ : Continuous n₃ := by
    dsimp [n₃, det]
    fun_prop
  have hU : IsOpen U := (isOpen_lt continuous_const hc₁).inter
    ((isOpen_lt continuous_const hc₂).inter (isOpen_lt continuous_const hc₃))
  have h0 : (0 : Plane) ∈ U := by
    simpa [U, n₁, n₂, n₃, det] using And.intro hqr (And.intro hrp hpq)
  have hUA : U ⊆ A := by
    intro x hx
    rcases hx with ⟨hx₁, hx₂, hx₃⟩
    let w : Fin 3 → ℝ := ![n₁ x / D, n₂ x / D, n₃ x / D]
    let z : Fin 3 → Plane := ![p, q, r]
    have hw : ∀ i ∈ (Finset.univ : Finset (Fin 3)), 0 ≤ w i := by
      intro i _
      fin_cases i <;> dsimp [w] <;> positivity
    have hsum : ∑ i : Fin 3, w i = 1 := by
      rw [Fin.sum_univ_three]
      dsimp [w]
      field_simp [hD.ne']
      dsimp [n₁, n₂, n₃, D, det]
      ring
    have hz : ∀ i ∈ (Finset.univ : Finset (Fin 3)), z i ∈ A := by
      intro i _
      fin_cases i <;> assumption
    have hv := hA.sum_mem hw hsum hz
    have heq : (∑ i : Fin 3, w i • z i) = x := by
      rw [Fin.sum_univ_three]
      apply PiLp.ext
      intro i
      fin_cases i <;> simp only [PiLp.add_apply, PiLp.smul_apply]
      · dsimp [w, z]
        field_simp [hD.ne']
        dsimp [n₁, n₂, n₃, D, det]
        ring
      · dsimp [w, z]
        field_simp [hD.ne']
        dsimp [n₁, n₂, n₃, D, det]
        ring
    rwa [heq] at hv
  apply interior_mono hUA
  rwa [hU.interior_eq]

/-- The three pair-cover witnesses in the normalized configuration place the
concurrent point strictly inside the body. -/
theorem origin_mem_interior_of_normalized_witnesses {A : Set Plane}
    (hA : Convex ℝ A) {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    {p q r : Plane} (hp : p ∈ A) (hq : q ∈ A) (hr : r ∈ A)
    (hp₀ : p 0 < 0) (hp₁ : 0 < p 1) (hq₀ : 0 < q 0) (hq₁ : q 1 < 0)
    (hr₀ : 0 < r 0) (hr₁ : 0 < r 1)
    (hpS : a * p 0 + b * p 1 < 0) (hqS : a * q 0 + b * q 1 < 0) :
    (0 : Plane) ∈ interior A := by
  apply origin_mem_interior_of_determinants hA hp hq hr
  · have h₁ : b * p 1 < -(a * p 0) := by linarith
    have h₂ : a * q 0 < -(b * q 1) := by linarith
    have hB : 0 < -(b * q 1) := neg_pos.mpr (mul_neg_of_pos_of_neg hb hq₁)
    have hprod := (mul_lt_mul_of_pos_left h₂ (mul_pos hb hp₁)).trans
      (mul_lt_mul_of_pos_right h₁ hB)
    have hdet : 0 < (a * b) * (p 0 * q 1 - q 0 * p 1) := by
      nlinarith [hprod]
    exact (mul_pos_iff_of_pos_left (mul_pos ha hb)).mp hdet
  · have h₁ := mul_pos hq₀ hr₁
    have h₂ := mul_neg_of_pos_of_neg hr₀ hq₁
    linarith
  · have h₁ := mul_pos hr₀ hp₁
    have h₂ := mul_neg_of_neg_of_pos hp₀ hr₁
    linarith

/-- Positive areas left uncovered by the three pairs provide the
witnesses needed for the concurrent point to lie inside the body. -/
theorem normalized_cover_origin_interior {A : Set Plane} (hA : Convex ℝ A)
    {a b c : ℝ}
    (hcover : ∀ x : Plane, x 0 < 0 ∨ x 1 < 0 ∨ 0 < a * x 0 + b * x 1 + c)
    (hUV : 0 < area (A \ ({x : Plane | x 0 < 0} ∪ {x : Plane | x 1 < 0})))
    (hUW : 0 < area (A \ ({x : Plane | x 0 < 0} ∪
      {x : Plane | 0 < a * x 0 + b * x 1 + c})))
    (hVW : 0 < area (A \ ({x : Plane | x 1 < 0} ∪
      {x : Plane | 0 < a * x 0 + b * x 1 + c}))) :
    0 < a ∧ 0 < b ∧ 0 < c ∧ (0 : Plane) ∈ interior A := by
  obtain ⟨r, hr, hr₀, hr₁⟩ := exists_mem_ne_zero_coordinates hUV
  obtain ⟨q, hq, hq₀, hq₁⟩ := exists_mem_ne_zero_coordinates hUW
  obtain ⟨p, hp, hp₀, hp₁⟩ := exists_mem_ne_zero_coordinates hVW
  have hrA : r ∈ A := hr.1
  have hqA : q ∈ A := hq.1
  have hpA : p ∈ A := hp.1
  have hr₀' : 0 < r 0 := by
    have : 0 ≤ r 0 := not_lt.mp (fun h => hr.2 (Or.inl h))
    exact lt_of_le_of_ne this hr₀.symm
  have hr₁' : 0 < r 1 := by
    have : 0 ≤ r 1 := not_lt.mp (fun h => hr.2 (Or.inr h))
    exact lt_of_le_of_ne this hr₁.symm
  have hq₀' : 0 < q 0 := by
    have : 0 ≤ q 0 := not_lt.mp (fun h => hq.2 (Or.inl h))
    exact lt_of_le_of_ne this hq₀.symm
  have hp₁' : 0 < p 1 := by
    have : 0 ≤ p 1 := not_lt.mp (fun h => hp.2 (Or.inl h))
    exact lt_of_le_of_ne this hp₁.symm
  have hqS : a * q 0 + b * q 1 + c ≤ 0 :=
    not_lt.mp (fun h => hq.2 (Or.inr h))
  have hpS : a * p 0 + b * p 1 + c ≤ 0 :=
    not_lt.mp (fun h => hp.2 (Or.inr h))
  obtain ⟨ha, hb, hc⟩ := normalized_cover_coefficients hcover
    ⟨q, hqA, hq₀'.le, hqS⟩ ⟨p, hpA, hp₁'.le, hpS⟩
  have hp₀' : p 0 < 0 := by
    rcases hcover p with h | h | h
    · exact h
    · exact False.elim (hp.2 (Or.inl h))
    · exact False.elim (hp.2 (Or.inr h))
  have hq₁' : q 1 < 0 := by
    rcases hcover q with h | h | h
    · exact False.elim (hq.2 (Or.inl h))
    · exact h
    · exact False.elim (hq.2 (Or.inr h))
  refine ⟨ha, hb, hc, origin_mem_interior_of_normalized_witnesses hA ha hb
    hpA hqA hrA hp₀' hp₁' hq₀' hq₁' hr₀' hr₁' ?_ ?_⟩ <;> linarith

end ThreeSlices
