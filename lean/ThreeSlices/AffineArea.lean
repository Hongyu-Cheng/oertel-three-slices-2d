import ThreeSlices.Basic

open Set MeasureTheory

namespace ThreeSlices

noncomputable def affineAreaScale (e : Plane ≃ᴬ[ℝ] Plane) : ℝ :=
  |LinearMap.det (e.toAffineEquiv.linear : Plane →ₗ[ℝ] Plane)|

lemma affineAreaScale_pos (e : Plane ≃ᴬ[ℝ] Plane) : 0 < affineAreaScale e :=
  abs_pos.mpr e.toAffineEquiv.linear.isUnit_det'.ne_zero

/-- Affine changes of coordinates multiply all sector areas by the same positive factor. -/
theorem area_affine_image (e : Plane ≃ᴬ[ℝ] Plane) (S : Set Plane) :
    area (e '' S) = affineAreaScale e * area S := by
  have he (x : Plane) : e x = e.toAffineEquiv.linear x + e 0 := by
    simpa using e.toAffineEquiv.map_vadd 0 x
  have hs : e '' S = (fun x => x + e 0) '' (e.toAffineEquiv.linear '' S) := by
    rw [← image_comp]
    congr 1
    funext x
    exact he x
  unfold area Measure.real
  rw [hs]
  simp only [image_add_right, measure_preimage_add_right]
  have hvol := volume.addHaar_image_linearMap
    (e.toAffineEquiv.linear : Plane →ₗ[ℝ] Plane) S
  change volume (e.toAffineEquiv.linear '' S) = _ at hvol
  rw [hvol, ENNReal.toReal_mul, ENNReal.toReal_ofReal (abs_nonneg _)]
  rfl

/-- The quadratic covering inequality is invariant when its cap-area bound is rescaled. -/
theorem affine_pair_bound_iff (e : Plane ≃ᴬ[ℝ] Plane) (A U V : Set Plane) (β : ℝ) :
    area ((e '' A) \ ((e '' U) ∪ (e '' V))) ^ 2 ≤
      (affineAreaScale e * β) * area ((e '' A) ∩ (e '' U) ∩ (e '' V)) ↔
    area (A \ (U ∪ V)) ^ 2 ≤ β * area (A ∩ U ∩ V) := by
  rw [← image_union, ← image_sdiff e.injective,
    ← image_inter e.injective, ← image_inter e.injective,
    area_affine_image, area_affine_image]
  have heq : (affineAreaScale e * β) *
      (affineAreaScale e * area (A ∩ U ∩ V)) =
      affineAreaScale e ^ 2 * (β * area (A ∩ U ∩ V)) := by ring
  rw [heq, mul_pow, mul_le_mul_iff_right₀ (sq_pos_of_pos (affineAreaScale_pos e))]

lemma affine_image_sector_ratio (E : Plane ≃ᴬ[ℝ] Plane) (K N D : Set Plane) :
    area ((E '' K) ∩ (E '' N)) / area ((E '' K) ∩ (E '' D)) =
      area (K ∩ N) / area (K ∩ D) := by
  rw [← image_inter E.injective, ← image_inter E.injective,
    area_affine_image, area_affine_image]
  exact mul_div_mul_left _ _ (affineAreaScale_pos E).ne'

end ThreeSlices
