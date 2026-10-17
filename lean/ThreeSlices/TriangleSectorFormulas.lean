import ThreeSlices.ChordTriangle
import ThreeSlices.SectorArea
import ThreeSlices.AffineArea
import ThreeSlices.Boundary
import ThreeSlices.TsintsifasAlgebra
import ThreeSlices.FanSymmetry

open Set MeasureTheory

namespace ThreeSlices

def triangleBarycentric (q : Plane) : Fin 3 → ℝ := ![1 - q 0 - q 1, q 0, q 1]

def barycentricNumeratorSector (x l : Fin 3 → ℝ) (i : Fin 3) : Set Plane :=
  {q | x (i + 1) + (1 - l (i + 1)) * (x i - triangleBarycentric q i) ≤
      triangleBarycentric q (i + 1) ∧
    triangleBarycentric q (i + 1) ≤
      x (i + 1) + (x i - triangleBarycentric q i) / l (i + 2)}

def barycentricDenominatorSector (x l : Fin 3 → ℝ) (i : Fin 3) : Set Plane :=
  {q | x (i + 1) + (x i - triangleBarycentric q i) / l (i + 2) ≤
      triangleBarycentric q (i + 1) ∧
    triangleBarycentric q (i + 1) ≤
      x (i + 1) + (1 - l (i + 1)) * (x i - triangleBarycentric q i)}

/-- The sector opposite the distinguished vertex `(1,0)`, with concurrent point `(x,y)`. -/
def triangleNumerator (x y l m : ℝ) : Set Plane :=
  {q | y + (1 - l) * (x - q 0) ≤ q 1 ∧ q 1 ≤ y + (x - q 0) / m}

/-- The opposite sector, containing the distinguished vertex `(1,0)`. -/
def triangleDenominator (x y l m : ℝ) : Set Plane :=
  {q | y + (x - q 0) / m ≤ q 1 ∧ q 1 ≤ y + (1 - l) * (x - q 0)}

/-- The numerator cuts a triangle from the unit simplex. -/
lemma triangleNumerator_inter_eq_region {x y z l m : ℝ}
    (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (hm : 0 < m)
    (hsum : x + y + z = 1)
    (hc : 0 < l + 1 / m - 1)
    (hedge₁ : l * x ≤ 1 - z) (hedge₂ : x ≤ m * (1 - y)) :
    standardChordTriangle ∩ triangleNumerator x y l m =
      {q : Plane | q 0 ∈ Icc 0 x ∧
        q 1 ∈ Icc (y + (1 - l) * (x - q 0)) (y + (x - q 0) / m)} := by
  have hbase : 0 ≤ y + (1 - l) * x := by nlinarith
  have hgap : 0 ≤ 1 - y - x / m := by
    have h : x / m ≤ 1 - y := (div_le_iff₀ hm).mpr (by nlinarith)
    linarith
  ext q
  constructor
  · intro hq
    have hp : 0 ≤ (x - q 0) * (l + 1 / m - 1) := by
      convert sub_nonneg.mpr (hq.2.1.trans hq.2.2) using 1
      ring
    have hs : q 0 ≤ x := by
      have h := (mul_nonneg_iff_of_pos_right hc).mp hp
      linarith
    exact ⟨⟨hq.1.1, hs⟩, hq.2⟩
  · intro hq
    have hs : 0 ≤ x - q 0 := sub_nonneg.mpr hq.1.2
    have hlow : 0 ≤ y + (1 - l) * (x - q 0) := by
      have h := add_nonneg (mul_nonneg hs hbase) (mul_nonneg hq.1.1 hy.le)
      have he : (x - q 0) * (y + (1 - l) * x) + q 0 * y =
          x * (y + (1 - l) * (x - q 0)) := by ring
      rw [he] at h
      exact (mul_nonneg_iff_of_pos_left hx).mp h
    have hhigh : y + (x - q 0) / m ≤ 1 - q 0 := by
      have h := add_nonneg (mul_nonneg hs hgap) (mul_nonneg hq.1.1 hz.le)
      have he : (x - q 0) * (1 - y - x / m) + q 0 * z =
          x * (1 - q 0 - (y + (x - q 0) / m)) := by
        rw [show z = 1 - x - y by linarith]
        ring
      rw [he] at h
      have h' := (mul_nonneg_iff_of_pos_left hx).mp h
      linarith
    exact ⟨⟨hq.1.1, hlow.trans hq.2.1, by linarith [hq.2.2]⟩, hq.2⟩

/-- The first of the six geometric area formulas, proved by Fubini. -/
theorem area_triangleNumerator {x y z l m : ℝ}
    (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (hm : 0 < m)
    (hsum : x + y + z = 1)
    (hc : 0 < l + 1 / m - 1)
    (hedge₁ : l * x ≤ 1 - z) (hedge₂ : x ≤ m * (1 - y)) :
    area (standardChordTriangle ∩ triangleNumerator x y l m) =
      x ^ 2 * (l + 1 / m - 1) / 2 := by
  rw [triangleNumerator_inter_eq_region hx hy hz hm hsum hc hedge₁ hedge₂]
  rw [area_between_graphs (f := fun s => y + (1 - l) * (x - s))
    (g := fun s => y + (x - s) / m) (by fun_prop) (by fun_prop) (by
      intro s hs
      apply sub_nonneg.mp
      convert mul_nonneg (sub_nonneg.mpr hs.2) hc.le using 1
      ring)]
  have he : (fun s : ℝ => y + (x - s) / m - (y + (1 - l) * (x - s))) =
      fun s => (l + 1 / m - 1) * x - (l + 1 / m - 1) * s := by
    funext s
    ring
  rw [he, integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hx.le,
    intervalIntegral.integral_sub (f := fun _ : ℝ => (l + 1 / m - 1) * x)
      (g := fun s => (l + 1 / m - 1) * s) intervalIntegrable_const
      ((continuous_const.mul continuous_id).intervalIntegrable _ _),
    intervalIntegral.integral_const, intervalIntegral.integral_const_mul, integral_id]
  simp only [sub_zero, zero_pow, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    smul_eq_mul]
  ring

lemma standardChordTriangle_eq_region : standardChordTriangle =
    {q : Plane | q 0 ∈ Icc (0 : ℝ) 1 ∧ q 1 ∈ Icc 0 (1 - q 0)} := by
  ext q
  change (0 ≤ q 0 ∧ 0 ≤ q 1 ∧ q 0 + q 1 ≤ 1) ↔
    ((0 ≤ q 0 ∧ q 0 ≤ 1) ∧ 0 ≤ q 1 ∧ q 1 ≤ 1 - q 0)
  constructor
  · rintro ⟨h₀, h₁, hsum⟩
    exact ⟨⟨h₀, by linarith⟩, h₁, by linarith⟩
  · rintro ⟨⟨h₀, _⟩, h₁, hsum⟩
    exact ⟨h₀, h₁, by linarith⟩

lemma area_standardChordTriangle : area standardChordTriangle = 1 / 2 := by
  rw [standardChordTriangle_eq_region, area_standardTriangle]

private lemma volume_ne_top_of_area_pos {S : Set Plane} (hS : 0 < area S) :
    volume S ≠ ⊤ := by
  intro h
  simp [area, Measure.real, h] at hS

lemma volume_standardChordTriangle_ne_top : volume standardChordTriangle ≠ ⊤ :=
  volume_ne_top_of_area_pos (by rw [area_standardChordTriangle]; norm_num)

private lemma measurableSet_coordinateRegion (f g : ℝ → ℝ) (a b : ℝ)
    (hf : Continuous f) (hg : Continuous g) :
    MeasurableSet {q : Plane | q 0 ∈ Icc a b ∧ q 1 ∈ Icc (f (q 0)) (g (q 0))} :=
  (measurableSet_region_between_cc hf.measurable hg.measurable
    measurableSet_Icc).preimage measurePreserving_coordinates.measurable

private lemma volume_affine_graph (a b : ℝ) :
    volume {q : Plane | q 1 = a * q 0 + b} = 0 := by
  let f : Plane →L[ℝ] ℝ := EuclideanSpace.proj 1 - a • EuclideanSpace.proj 0
  have hf : f ≠ 0 := by
    intro h
    have he := congrArg (fun g : Plane →L[ℝ] ℝ => g (EuclideanSpace.single 1 1)) h
    simp [f] at he
  have he : {q : Plane | q 1 = a * q 0 + b} = {q | f q = b} := by
    ext q
    simp only [mem_ofPred_eq]
    change (q 1 = a * q 0 + b) ↔ q 1 - a * q 0 = b
    constructor <;> intro h <;> linarith
  rw [he]
  exact volume_linear_levelSet f hf b

private def triangleCorner (x : ℝ) : Set Plane :=
  {q | q 0 ∈ Icc x 1 ∧ q 1 ∈ Icc 0 (1 - q 0)}

private def triangleLowerCut (x y m : ℝ) : Set Plane :=
  {q | q 0 ∈ Icc x (x + m * y) ∧ q 1 ∈ Icc 0 (y + (x - q 0) / m)}

private def triangleUpperCut (x y z l : ℝ) : Set Plane :=
  {q | q 0 ∈ Icc x (x + z / l) ∧
    q 1 ∈ Icc (y + (1 - l) * (x - q 0)) (1 - q 0)}

private lemma area_triangleCorner {x : ℝ} (hx : x ≤ 1) :
    area (triangleCorner x) = (1 - x) ^ 2 / 2 := by
  rw [triangleCorner, area_between_graphs (f := fun _ => 0) (g := fun s => 1 - s)
    continuous_const (continuous_const.sub continuous_id)
    (by intro s hs; linarith [hs.2])]
  simp only [sub_zero]
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hx,
    intervalIntegral.integral_sub (f := fun _ : ℝ => 1) (g := fun s : ℝ => s)
      intervalIntegrable_const (continuous_id.intervalIntegrable _ _),
    intervalIntegral.integral_const, integral_id]
  simp only [one_pow, smul_eq_mul]
  ring

private lemma area_triangleLowerCut {x y m : ℝ} (hy : 0 ≤ y) (hm : 0 < m) :
    area (triangleLowerCut x y m) = m * y ^ 2 / 2 := by
  rw [triangleLowerCut, area_between_graphs (f := fun _ => 0)
    (g := fun s => y + (x - s) / m) continuous_const (by fun_prop) (by
      intro s hs
      have h : -y ≤ (x - s) / m := (le_div_iff₀ hm).mpr (by nlinarith [hs.2])
      linarith)]
  have he : (fun s : ℝ => y + (x - s) / m - 0) =
      fun s => (y + x / m) - (1 / m) * s := by funext s; ring
  rw [he, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by nlinarith : x ≤ x + m * y),
    intervalIntegral.integral_sub (f := fun _ : ℝ => y + x / m)
      (g := fun s => (1 / m) * s) intervalIntegrable_const
      ((continuous_const.mul continuous_id).intervalIntegrable _ _),
    intervalIntegral.integral_const, intervalIntegral.integral_const_mul, integral_id]
  simp only [smul_eq_mul]
  field_simp
  ring

private lemma area_triangleUpperCut {x y z l : ℝ} (hz : 0 ≤ z) (hl : 0 < l)
    (hsum : x + y + z = 1) :
    area (triangleUpperCut x y z l) = z ^ 2 / (2 * l) := by
  rw [triangleUpperCut, area_between_graphs
    (f := fun s => y + (1 - l) * (x - s)) (g := fun s => 1 - s)
    (by fun_prop) (by fun_prop) (by
      intro s hs
      have h := mul_le_mul_of_nonneg_left hs.2 hl.le
      rw [mul_add, mul_div_cancel₀ _ hl.ne'] at h
      nlinarith)]
  have he : (fun s : ℝ => 1 - s - (y + (1 - l) * (x - s))) =
      fun s => (z + l * x) - l * s := by
    funext s
    rw [show z = 1 - x - y by linarith]
    ring
  rw [he, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (le_add_of_nonneg_right (div_nonneg hz hl.le)),
    intervalIntegral.integral_sub (f := fun _ : ℝ => z + l * x)
      (g := fun s => l * s) intervalIntegrable_const
      ((continuous_const.mul continuous_id).intervalIntegrable _ _),
    intervalIntegral.integral_const, intervalIntegral.integral_const_mul, integral_id]
  simp only [smul_eq_mul]
  field_simp
  ring

private lemma triangleLowerCut_subset_corner {x y z m : ℝ}
    (hy : 0 < y) (hm : 0 < m) (hsum : x + y + z = 1)
    (hz : 0 ≤ z) (hupper : m * y ≤ 1 - x) :
    triangleLowerCut x y m ⊆ triangleCorner x := by
  intro q hq
  refine ⟨⟨hq.1.1, hq.1.2.trans (by linarith)⟩, hq.2.1, ?_⟩
  have h := add_nonneg
    (mul_nonneg (sub_nonneg.mpr hq.1.2) hz)
    (mul_nonneg (sub_nonneg.mpr hq.1.1) (by linarith : 0 ≤ 1 - x - m * y))
  have he : (x + m * y - q 0) * z + (q 0 - x) * (1 - x - m * y) =
      (m * y) * (1 - q 0 - (y + (x - q 0) / m)) := by
    rw [show z = 1 - x - y by linarith]
    field_simp
    ring
  rw [he] at h
  have hgap := (mul_nonneg_iff_of_pos_left (mul_pos hm hy)).mp h
  linarith [hq.2.2]

private lemma triangleUpperCut_subset_corner {x y z l : ℝ}
    (hy : 0 ≤ y) (hz : 0 < z) (hl : 0 < l) (hsum : x + y + z = 1)
    (hlower : z ≤ l * (1 - x)) :
    triangleUpperCut x y z l ⊆ triangleCorner x := by
  intro q hq
  have hend : z / l ≤ 1 - x := (div_le_iff₀ hl).mpr (by simpa [mul_comm] using hlower)
  refine ⟨⟨hq.1.1, hq.1.2.trans (by linarith)⟩, ?_, hq.2.2⟩
  have h := add_nonneg (mul_nonneg (sub_nonneg.mpr hq.1.2) hy)
    (mul_nonneg (sub_nonneg.mpr hq.1.1) (by linarith : 0 ≤ 1 - x - z / l))
  have he : (x + z / l - q 0) * y + (q 0 - x) * (1 - x - z / l) =
      (z / l) * (y + (1 - l) * (x - q 0)) := by
    rw [show z = 1 - x - y by linarith]
    field_simp
    ring
  rw [he] at h
  exact ((mul_nonneg_iff_of_pos_left (div_pos hz hl)).mp h).trans hq.2.1

private lemma triangleDenominator_subset_corner {x y l m : ℝ}
    (hc : 0 < l + 1 / m - 1) :
    standardChordTriangle ∩ triangleDenominator x y l m ⊆ triangleCorner x := by
  intro q hq
  have h : 0 ≤ (q 0 - x) * (l + 1 / m - 1) := by
    convert sub_nonneg.mpr (hq.2.1.trans hq.2.2) using 1
    ring
  have hs := (mul_nonneg_iff_of_pos_right hc).mp h
  exact ⟨⟨by linarith, by linarith [hq.1.2.1, hq.1.2.2]⟩,
    hq.1.2.1, by linarith [hq.1.2.2]⟩

private lemma triangleCorner_partition {x y z l m : ℝ}
    (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (hl : 0 < l) (hm : 0 < m)
    (hsum : x + y + z = 1) (hc : 0 < l + 1 / m - 1)
    (hlower : z ≤ l * (1 - x)) (hupper : m * y ≤ 1 - x) :
    ((standardChordTriangle ∩ triangleDenominator x y l m) ∪ triangleLowerCut x y m) ∪
        triangleUpperCut x y z l = triangleCorner x := by
  have hD := triangleDenominator_subset_corner (x := x) (y := y) hc
  have hL := triangleLowerCut_subset_corner hy hm hsum hz.le hupper
  have hU := triangleUpperCut_subset_corner hy.le hz hl hsum hlower
  ext q
  constructor
  · rintro ((hq | hq) | hq)
    · exact hD hq
    · exact hL hq
    · exact hU hq
  · intro hq
    have hT : q ∈ standardChordTriangle :=
      ⟨by linarith [hq.1.1], hq.2.1, by linarith [hq.2.2]⟩
    by_cases hlow : y + (x - q 0) / m ≤ q 1
    · by_cases hhigh : q 1 ≤ y + (1 - l) * (x - q 0)
      · exact Or.inl (Or.inl ⟨hT, hlow, hhigh⟩)
      · right
        have h : l * (q 0 - x) ≤ z := by
          nlinarith [lt_of_not_ge hhigh, hq.2.2]
        have hs : q 0 - x ≤ z / l :=
          (le_div_iff₀ hl).mpr (by simpa [mul_comm] using h)
        exact ⟨⟨hq.1.1, by linarith⟩, (lt_of_not_ge hhigh).le, hq.2.2⟩
    · left
      right
      have h : -y ≤ (x - q 0) / m := by linarith [hq.2.1, lt_of_not_ge hlow]
      have hs := (le_div_iff₀ hm).mp h
      exact ⟨⟨hq.1.1, by nlinarith⟩, hq.2.1, (lt_of_not_ge hlow).le⟩

private lemma area_union_of_null_inter {S T : Set Plane}
    (hS : volume S ≠ ⊤) (hT : volume T ≠ ⊤) (hm : MeasurableSet T)
    (hn : volume (S ∩ T) = 0) : area (S ∪ T) = area S + area T := by
  have h := measureReal_union_add_inter (μ := volume) hm hS hT
  change area (S ∪ T) + area (S ∩ T) = area S + area T at h
  have hz : area (S ∩ T) = 0 := by simp [area, Measure.real, hn]
  rwa [hz, add_zero] at h

/-- The denominator is the corner triangle with its two boundary triangles removed. -/
theorem area_triangleDenominator {x y z l m : ℝ}
    (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (hl : 0 < l) (hm : 0 < m)
    (hsum : x + y + z = 1) (hc : 0 < l + 1 / m - 1)
    (hlower : z ≤ l * (1 - x)) (hupper : m * y ≤ 1 - x) :
    area (standardChordTriangle ∩ triangleDenominator x y l m) =
      ((1 - x) ^ 2 - m * y ^ 2 - z ^ 2 / l) / 2 := by
  let D := standardChordTriangle ∩ triangleDenominator x y l m
  let L := triangleLowerCut x y m
  let U := triangleUpperCut x y z l
  have hD : volume D ≠ ⊤ := measure_ne_top_of_subset inter_subset_left
    volume_standardChordTriangle_ne_top
  have hL : volume L ≠ ⊤ := volume_ne_top_of_area_pos (by
    dsimp [L]
    rw [area_triangleLowerCut hy.le hm]
    positivity)
  have hU : volume U ≠ ⊤ := volume_ne_top_of_area_pos (by
    dsimp [U]
    rw [area_triangleUpperCut hz.le hl hsum]
    positivity)
  have hmL : MeasurableSet L := by
    exact measurableSet_coordinateRegion (fun _ => 0) (fun s => y + (x - s) / m)
      x (x + m * y) continuous_const (by fun_prop)
  have hmU : MeasurableSet U := by
    exact measurableSet_coordinateRegion (fun s => y + (1 - l) * (x - s))
      (fun s => 1 - s) x (x + z / l) (by fun_prop) (by fun_prop)
  have hDL : volume (D ∩ L) = 0 := by
    apply measure_mono_null _ (volume_affine_graph (-(1 / m)) (y + x / m))
    intro q hq
    change q 1 = -(1 / m) * q 0 + (y + x / m)
    have he : y + (x - q 0) / m = -(1 / m) * q 0 + (y + x / m) := by ring
    rw [← he]
    exact le_antisymm hq.2.2.2 hq.1.2.1
  have hDU : volume (D ∩ U) = 0 := by
    apply measure_mono_null _ (volume_affine_graph (l - 1) (y + (1 - l) * x))
    intro q hq
    change q 1 = (l - 1) * q 0 + (y + (1 - l) * x)
    have he : y + (1 - l) * (x - q 0) =
        (l - 1) * q 0 + (y + (1 - l) * x) := by ring
    rw [← he]
    exact le_antisymm hq.1.2.2 hq.2.2.1
  have hLU : volume (L ∩ U) = 0 := by
    apply measure_mono_null _ (volume_coordinate_levelSet 0 x)
    intro q hq
    have hp : 0 ≤ (x - q 0) * (l + 1 / m - 1) := by
      convert sub_nonneg.mpr (hq.2.2.1.trans hq.1.2.2) using 1
      ring
    have hs := (mul_nonneg_iff_of_pos_right hc).mp hp
    exact le_antisymm (by linarith) hq.1.1.1
  have hDLU : volume ((D ∪ L) ∩ U) = 0 := by
    rw [union_inter_distrib_right]
    exact measure_union_null hDU hLU
  have hDLfinite : volume (D ∪ L) ≠ ⊤ := (measure_union_lt_top hD.lt_top hL.lt_top).ne
  have hsumarea := area_union_of_null_inter hDLfinite hU hmU hDLU
  rw [area_union_of_null_inter hD hL hmL hDL] at hsumarea
  change area ((D ∪ L) ∪ U) = area D + area L + area U at hsumarea
  have hpartition : (D ∪ L) ∪ U = triangleCorner x :=
    triangleCorner_partition hx hy hz hl hm hsum hc hlower hupper
  rw [hpartition, area_triangleCorner (by linarith : x ≤ 1)] at hsumarea
  dsimp [L, U] at hsumarea
  rw [area_triangleLowerCut hy.le hm, area_triangleUpperCut hz.le hl hsum] at hsumarea
  have he : z ^ 2 / (2 * l) = (z ^ 2 / l) / 2 := by ring
  rw [he] at hsumarea
  dsimp [D] at hsumarea
  linarith

private noncomputable def triangleCycle : Plane ≃ᴬ[ℝ] Plane :=
  fanCycle.toContinuousAffineEquiv.trans
    (ContinuousAffineEquiv.constVAdd ℝ Plane (WithLp.toLp 2 ![0, 1]))

@[simp] private lemma triangleCycle_apply_zero (q : Plane) : triangleCycle q 0 = q 1 := by
  change ((WithLp.toLp 2 ![0, 1] : Plane) + fanCycle q) 0 = q 1
  simp

@[simp] private lemma triangleCycle_apply_one (q : Plane) :
    triangleCycle q 1 = 1 - q 0 - q 1 := by
  change ((WithLp.toLp 2 ![0, 1] : Plane) + fanCycle q) 1 = 1 - q 0 - q 1
  simp
  ring

private lemma triangleCycle_areaScale : affineAreaScale triangleCycle = 1 := by
  let B := (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis
  have hlinear (q : Plane) : triangleCycle.toAffineEquiv.linear q =
      WithLp.toLp 2 ![q 1, -q 0 - q 1] := by
    have h : triangleCycle q = triangleCycle.toAffineEquiv.linear q + triangleCycle 0 := by
      simpa using triangleCycle.toAffineEquiv.map_vadd (0 : Plane) q
    apply PiLp.ext
    intro i
    fin_cases i
    · have h' := congrArg (fun r : Plane => r 0) h
      simp only [PiLp.add_apply, triangleCycle_apply_zero, PiLp.zero_apply] at h'
      simpa using h'.symm
    · have h' := congrArg (fun r : Plane => r 1) h
      simp only [PiLp.add_apply, triangleCycle_apply_one, PiLp.zero_apply] at h'
      change triangleCycle.toAffineEquiv.linear q 1 = -q 0 - q 1
      linarith
  have hM : LinearMap.toMatrix B B (triangleCycle.toAffineEquiv.linear : Plane →ₗ[ℝ] Plane) =
      !![0, 1; -1, -1] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [B, LinearMap.toMatrix_apply, hlinear]
  rw [affineAreaScale, ← LinearMap.det_toMatrix B, hM, Matrix.det_fin_two]
  norm_num

private lemma area_triangleCycle_image (S : Set Plane) : area (triangleCycle '' S) = area S := by
  rw [area_affine_image, triangleCycle_areaScale, one_mul]

private lemma triangleCycle_mem (q : Plane) :
    triangleCycle q ∈ standardChordTriangle ↔ q ∈ standardChordTriangle := by
  simp only [standardChordTriangle, mem_ofPred_eq,
    triangleCycle_apply_zero, triangleCycle_apply_one]
  constructor <;> rintro ⟨h₀, h₁, h₂⟩ <;> refine ⟨?_, ?_, ?_⟩ <;> linarith

private noncomputable def triangleCoordinates (i : Fin 3) : Plane ≃ᴬ[ℝ] Plane :=
  ![triangleCycle.trans triangleCycle, ContinuousAffineEquiv.refl ℝ Plane, triangleCycle] i

private lemma triangleCoordinates_apply (i : Fin 3) (q : Plane) :
    triangleCoordinates i q 0 = triangleBarycentric q i ∧
      triangleCoordinates i q 1 = triangleBarycentric q (i + 1) := by
  fin_cases i <;> simp [triangleCoordinates, triangleBarycentric]

private lemma area_triangleCoordinates_image (i : Fin 3) (S : Set Plane) :
    area (triangleCoordinates i '' S) = area S := by
  fin_cases i
  · change area ((triangleCycle ∘ triangleCycle) '' S) = area S
    rw [Set.image_comp, area_triangleCycle_image, area_triangleCycle_image]
  · simp [triangleCoordinates]
  · exact area_triangleCycle_image S

private lemma triangleCoordinates_mem (i : Fin 3) (q : Plane) :
    triangleCoordinates i q ∈ standardChordTriangle ↔ q ∈ standardChordTriangle := by
  fin_cases i <;> simp [triangleCoordinates, triangleCycle_mem]

private lemma area_triangleCoordinates_inter_eq (i : Fin 3) (S R : Set Plane)
    (h : ∀ q, triangleCoordinates i q ∈ R ↔ q ∈ S) :
    area (standardChordTriangle ∩ S) = area (standardChordTriangle ∩ R) := by
  let E := triangleCoordinates i
  have he : E '' (standardChordTriangle ∩ S) = standardChordTriangle ∩ R := by
    ext q
    constructor
    · rintro ⟨p, hp, rfl⟩
      exact ⟨(triangleCoordinates_mem i p).mpr hp.1, (h p).mpr hp.2⟩
    · intro hq
      refine ⟨E.symm q, ⟨?_, ?_⟩, E.apply_symm_apply q⟩
      · apply (triangleCoordinates_mem i _).mp
        change E (E.symm q) ∈ standardChordTriangle
        rw [E.apply_symm_apply]
        exact hq.1
      · apply (h _).mp
        change E (E.symm q) ∈ R
        rw [E.apply_symm_apply]
        exact hq.2
  rw [← he]
  exact (area_triangleCoordinates_image i _).symm

private lemma area_barycentricNumerator_eq_scalar (x l : Fin 3 → ℝ) (i : Fin 3) :
    area (standardChordTriangle ∩ barycentricNumeratorSector x l i) =
      area (standardChordTriangle ∩ triangleNumerator (x i) (x (i + 1))
        (l (i + 1)) (l (i + 2))) := by
  apply area_triangleCoordinates_inter_eq i
  intro q
  simp only [triangleNumerator, barycentricNumeratorSector, mem_ofPred_eq]
  rw [(triangleCoordinates_apply i q).1, (triangleCoordinates_apply i q).2]

private lemma area_barycentricDenominator_eq_scalar (x l : Fin 3 → ℝ) (i : Fin 3) :
    area (standardChordTriangle ∩ barycentricDenominatorSector x l i) =
      area (standardChordTriangle ∩ triangleDenominator (x i) (x (i + 1))
        (l (i + 1)) (l (i + 2))) := by
  apply area_triangleCoordinates_inter_eq i
  intro q
  simp only [triangleDenominator, barycentricDenominatorSector, mem_ofPred_eq]
  rw [(triangleCoordinates_apply i q).1, (triangleCoordinates_apply i q).2]

theorem area_barycentricNumerator (x l : Fin 3 → ℝ) (i : Fin 3)
    (hx : ∀ j, 0 < x j) (hl : ∀ j, 0 < l j) (hsum : ∑ j, x j = 1)
    (hwidth : ∀ j, 0 < l (j + 1) + 1 / l (j + 2) - 1)
    (hvertexLower : ∀ j, x (j + 2) ≤ l (j + 1) * (1 - x j))
    (hvertexUpper : ∀ j, l (j + 2) * x (j + 1) ≤ 1 - x j) :
    area (standardChordTriangle ∩ barycentricNumeratorSector x l i) =
      x i ^ 2 * (l (i + 1) + 1 / l (i + 2) - 1) / 2 := by
  have hsum' : x i + x (i + 1) + x (i + 2) = 1 := by
    fin_cases i <;> simp [Fin.sum_univ_succ] at hsum ⊢ <;> linarith
  have he₁ : l (i + 1) * x i ≤ 1 - x (i + 2) := by
    have h := hvertexUpper (i + 2)
    fin_cases i <;> simpa using h
  have he₂ : x i ≤ l (i + 2) * (1 - x (i + 1)) := by
    have h := hvertexLower (i + 1)
    fin_cases i <;> simpa using h
  rw [area_barycentricNumerator_eq_scalar]
  exact area_triangleNumerator (hx i) (hx (i + 1)) (hx (i + 2)) (hl (i + 2))
    hsum' (hwidth i) he₁ he₂

theorem area_barycentricDenominator (x l : Fin 3 → ℝ) (i : Fin 3)
    (hx : ∀ j, 0 < x j) (hl : ∀ j, 0 < l j) (hsum : ∑ j, x j = 1)
    (hwidth : ∀ j, 0 < l (j + 1) + 1 / l (j + 2) - 1)
    (hvertexLower : ∀ j, x (j + 2) ≤ l (j + 1) * (1 - x j))
    (hvertexUpper : ∀ j, l (j + 2) * x (j + 1) ≤ 1 - x j) :
    area (standardChordTriangle ∩ barycentricDenominatorSector x l i) =
      ((1 - x i) ^ 2 - l (i + 2) * x (i + 1) ^ 2 - x (i + 2) ^ 2 / l (i + 1)) / 2 := by
  have hsum' : x i + x (i + 1) + x (i + 2) = 1 := by
    fin_cases i <;> simp [Fin.sum_univ_succ] at hsum ⊢ <;> linarith
  rw [area_barycentricDenominator_eq_scalar]
  exact area_triangleDenominator (hx i) (hx (i + 1)) (hx (i + 2))
    (hl (i + 1)) (hl (i + 2)) hsum' (hwidth i) (hvertexLower i) (hvertexUpper i)

/-- Tsintsifas's bounded branch for sector intersections of the unit triangle. -/
theorem barycentric_triangle_ratio_sum (x l : Fin 3 → ℝ)
    (hx : ∀ i, 0 < x i) (hsum : ∑ i, x i = 1) (hl : ∀ i, 0 < l i)
    (hwidth : ∀ i, 0 < l (i + 1) + 1 / l (i + 2) - 1)
    (hvertexLower : ∀ i, x (i + 2) ≤ l (i + 1) * (1 - x i))
    (hvertexUpper : ∀ i, l (i + 2) * x (i + 1) ≤ 1 - x i)
    (hdenpos : ∀ i, 0 < area (standardChordTriangle ∩ barycentricDenominatorSector x l i)) :
    (3 / 2 : ℝ) ≤ ∑ i,
      area (standardChordTriangle ∩ barycentricNumeratorSector x l i) /
        area (standardChordTriangle ∩ barycentricDenominatorSector x l i) := by
  let A : Fin 3 → ℝ := fun i => 2 * area (standardChordTriangle ∩ barycentricNumeratorSector x l i)
  let B : Fin 3 → ℝ := fun i => 2 * area (standardChordTriangle ∩ barycentricDenominatorSector x l i)
  have hA (i : Fin 3) : A i = x i ^ 2 * (l (i + 1) + 1 / l (i + 2) - 1) := by
    dsimp [A]
    rw [area_barycentricNumerator x l i hx hl hsum hwidth hvertexLower hvertexUpper]
    ring
  have hB (i : Fin 3) : B i =
      (1 - x i) ^ 2 - l (i + 2) * x (i + 1) ^ 2 - x (i + 2) ^ 2 / l (i + 1) := by
    dsimp [B]
    rw [area_barycentricDenominator x l i hx hl hsum hwidth hvertexLower hvertexUpper]
    ring
  have hb (i : Fin 3) : 0 < B i := mul_pos (by norm_num) (hdenpos i)
  have hratio (i : Fin 3) : A i / B i =
      area (standardChordTriangle ∩ barycentricNumeratorSector x l i) /
        area (standardChordTriangle ∩ barycentricDenominatorSector x l i) := by
    dsimp [A, B]
    exact mul_div_mul_left _ _ (by norm_num : (2 : ℝ) ≠ 0)
  have h := tsintsifas_algebra (x 0) (x 1) (x 2) (l 0) (l 1) (l 2)
    (A 0) (A 1) (A 2) (B 0) (B 1) (B 2) (hx 0) (hx 1) (hx 2)
    (by simpa [Fin.sum_univ_succ, add_assoc] using hsum)
    (hl 0) (hl 1) (hl 2) (hb 0) (hb 1) (hb 2)
    (hA 0) (hA 1) (hA 2) (hB 0) (hB 1) (hB 2)
  simpa [hratio, Fin.sum_univ_succ, add_assoc] using h

end ThreeSlices
