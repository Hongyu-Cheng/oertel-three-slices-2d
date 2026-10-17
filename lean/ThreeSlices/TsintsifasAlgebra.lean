import Mathlib

namespace ThreeSlices

/-- The two-term weighted square inequality used in Tsintsifas's proof. -/
theorem tsintsifas_weighted_squares (l u v : ℝ) (hl : 0 < l) :
    2 * u * v ≤ l * u ^ 2 + (1 / l) * v ^ 2 := by
  have h := div_nonneg (sq_nonneg (l * u - v)) hl.le
  have hid : (l * u - v) ^ 2 / l = l * u ^ 2 + (1 / l) * v ^ 2 - 2 * u * v := by
    field_simp
    ring
  rw [hid] at h
  linarith

/-- The product bound for the normalized barycentric ratios. -/
theorem tsintsifas_normalized_product (x y z : ℝ)
    (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (hsum : x + y + z = 1) :
    (x / (1 - x)) * (y / (1 - y)) * (z / (1 - z)) ≤ 1 / 8 := by
  have hdx : 0 < 1 - x := by linarith
  have hdy : 0 < 1 - y := by linarith
  have hdz : 0 < 1 - z := by linarith
  have hprod : 8 * (x * y * z) ≤ (1 - x) * (1 - y) * (1 - z) := by
    have h₁ := mul_nonneg hx.le (sq_nonneg (y - z))
    have h₂ := mul_nonneg hy.le (sq_nonneg (z - x))
    have h₃ := mul_nonneg hz.le (sq_nonneg (x - y))
    have heq : (1 - x) * (1 - y) * (1 - z) - 8 * (x * y * z) =
        x * (y - z) ^ 2 + y * (z - x) ^ 2 + z * (x - y) ^ 2 := by
      have hx' : 1 - x = y + z := by linarith
      have hy' : 1 - y = z + x := by linarith
      have hz' : 1 - z = x + y := by linarith
      rw [hx', hy', hz']
      ring
    linarith
  rw [← mul_div_mul_comm, ← mul_div_mul_comm]
  apply (div_le_iff₀ (mul_pos (mul_pos hdx hdy) hdz)).2
  nlinarith

/-- Clearing the three normalized denominators gives the exact pair-product identity. -/
theorem tsintsifas_normalized_identity (x y z : ℝ)
    (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (hsum : x + y + z = 1) :
    (x / (1 - x)) * (y / (1 - y)) +
      (y / (1 - y)) * (z / (1 - z)) +
      (z / (1 - z)) * (x / (1 - x)) +
      2 * ((x / (1 - x)) * (y / (1 - y)) * (z / (1 - z))) = 1 := by
  have hdx : 1 - x ≠ 0 := by linarith
  have hdy : 1 - y ≠ 0 := by linarith
  have hdz : 1 - z ≠ 0 := by linarith
  field_simp
  nlinarith

/-- A single scalar area ratio dominates its weighted normalized square. -/
theorem tsintsifas_one_ratio (x y z l m b : ℝ)
    (hy : 0 < y) (hz : 0 < z) (hl : 0 < l) (hm : 0 < m)
    (hsum : x + y + z = 1) (hb : 0 < b)
    (hformula : b = (1 - x) ^ 2 - m * y ^ 2 - z ^ 2 / l) :
    (l + 1 / m) * (x / (1 - x)) ^ 2 ≤ x ^ 2 * (l + 1 / m - 1) / b := by
  have hdx : 0 < 1 - x := by linarith
  have hweighted := tsintsifas_weighted_squares (l * m) y z (mul_pos hl hm)
  have hid : (l + 1 / m - 1) * (1 - x) ^ 2 - (l + 1 / m) * b =
      l * m * y ^ 2 + (1 / (l * m)) * z ^ 2 - 2 * y * z := by
    rw [hformula, show 1 - x = y + z by linarith]
    field_simp
    ring
  have hnonneg : 0 ≤ (l + 1 / m - 1) * (1 - x) ^ 2 - (l + 1 / m) * b := by
    rw [hid]
    linarith
  rw [div_pow, ← mul_div_assoc]
  apply (div_le_div_iff₀ (sq_pos_of_pos hdx) hb).2
  nlinarith only [mul_nonneg (sq_nonneg x) hnonneg]

/-- The exact scalar core of Tsintsifas's bounded-sector inequality.
The three area formulas and positivity of their denominators are explicit hypotheses. -/
theorem tsintsifas_algebra (x₁ x₂ x₃ l₁ l₂ l₃ a₁ a₂ a₃ b₁ b₂ b₃ : ℝ)
    (hx₁ : 0 < x₁) (hx₂ : 0 < x₂) (hx₃ : 0 < x₃)
    (hsum : x₁ + x₂ + x₃ = 1)
    (hl₁ : 0 < l₁) (hl₂ : 0 < l₂) (hl₃ : 0 < l₃)
    (hb₁ : 0 < b₁) (hb₂ : 0 < b₂) (hb₃ : 0 < b₃)
    (ha₁ : a₁ = x₁ ^ 2 * (l₂ + 1 / l₃ - 1))
    (ha₂ : a₂ = x₂ ^ 2 * (l₃ + 1 / l₁ - 1))
    (ha₃ : a₃ = x₃ ^ 2 * (l₁ + 1 / l₂ - 1))
    (hformula₁ : b₁ = (1 - x₁) ^ 2 - l₃ * x₂ ^ 2 - x₃ ^ 2 / l₂)
    (hformula₂ : b₂ = (1 - x₂) ^ 2 - l₁ * x₃ ^ 2 - x₁ ^ 2 / l₃)
    (hformula₃ : b₃ = (1 - x₃) ^ 2 - l₂ * x₁ ^ 2 - x₂ ^ 2 / l₁) :
    (3 / 2 : ℝ) ≤ a₁ / b₁ + a₂ / b₂ + a₃ / b₃ := by
  have hr₁ := tsintsifas_one_ratio x₁ x₂ x₃ l₂ l₃ b₁
    hx₂ hx₃ hl₂ hl₃ hsum hb₁ hformula₁
  have hr₂ := tsintsifas_one_ratio x₂ x₃ x₁ l₃ l₁ b₂
    hx₃ hx₁ hl₃ hl₁ (by linarith) hb₂ hformula₂
  have hr₃ := tsintsifas_one_ratio x₃ x₁ x₂ l₁ l₂ b₃
    hx₁ hx₂ hl₁ hl₂ (by linarith) hb₃ hformula₃
  rw [← ha₁] at hr₁
  rw [← ha₂] at hr₂
  rw [← ha₃] at hr₃
  have hw₁ := tsintsifas_weighted_squares l₁ (x₃ / (1 - x₃)) (x₂ / (1 - x₂)) hl₁
  have hw₂ := tsintsifas_weighted_squares l₂ (x₁ / (1 - x₁)) (x₃ / (1 - x₃)) hl₂
  have hw₃ := tsintsifas_weighted_squares l₃ (x₂ / (1 - x₂)) (x₁ / (1 - x₁)) hl₃
  have hp := tsintsifas_normalized_product x₁ x₂ x₃ hx₁ hx₂ hx₃ hsum
  have hi := tsintsifas_normalized_identity x₁ x₂ x₃ hx₁ hx₂ hx₃ hsum
  nlinarith only [hr₁, hr₂, hr₃, hw₁, hw₂, hw₃, hp, hi]

/-- The scalar conclusion in the unbounded-sector case. -/
theorem tsintsifas_unbounded (r s t : ℝ)
    (hr : 0 ≤ r) (hs : 0 ≤ s) (ht : 0 ≤ t) (hprod : 1 ≤ r * s) :
    2 ≤ r + s + t := by
  have hsum : 2 ≤ r + s := by
    by_contra h
    have hlt : r + s < 2 := lt_of_not_ge h
    nlinarith [sq_nonneg (r - s)]
  linarith

end ThreeSlices
