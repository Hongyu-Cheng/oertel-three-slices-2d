import ThreeSlices.Theorem
import ThreeSlices.FanSymmetry

open Set MeasureTheory
open scoped Pointwise

namespace ThreeSlices

def linearImageBodies (E : Plane ≃L[ℝ] Plane) (A : Bodies) : Bodies :=
  fun i => E '' A i

def Halfspace.linearImage (H : Halfspace) (E : Plane ≃L[ℝ] Plane) : Halfspace :=
  ⟨H.height, H.planar.comp E.symm.toContinuousLinearMap, H.threshold⟩

@[simp] lemma Halfspace.linearImage_closedCap (H : Halfspace) (E : Plane ≃L[ℝ] Plane)
    (i : Fin 3) : (H.linearImage E).closedCap i = E '' H.closedCap i := by
  rw [ContinuousLinearEquiv.image_eq_preimage_symm]
  rfl

@[simp] lemma Halfspace.mem_linearImage_closedCap (H : Halfspace)
    (E : Plane ≃L[ℝ] Plane) (i : Fin 3) (x : Plane) :
    E x ∈ (H.linearImage E).closedCap i ↔ x ∈ H.closedCap i := by
  simp [Halfspace.linearImage, Halfspace.closedCap]

lemma linearImageBodies_isBody (E : Plane ≃L[ℝ] Plane) (A : Bodies)
    (hA : ∀ i, IsBody (A i)) : ∀ i, IsBody (linearImageBodies E A i) :=
  fun i => (hA i).linear_image E

lemma linearImageBodies_compatible (E : Plane ≃L[ℝ] Plane) (A : Bodies)
    (hA : Compatible A) : Compatible (linearImageBodies E A) := by
  rintro _ ⟨y, hy, z, hz, rfl⟩
  rcases hy with ⟨y, ⟨u, hu, rfl⟩, rfl⟩
  rcases hz with ⟨z, ⟨v, hv, rfl⟩, rfl⟩
  refine ⟨(1 / 2 : ℝ) • u + (1 / 2 : ℝ) • v, ?_, ?_⟩
  · exact hA ⟨(1 / 2 : ℝ) • u, ⟨u, hu, rfl⟩,
      (1 / 2 : ℝ) • v, ⟨v, hv, rfl⟩, rfl⟩
  · simp

lemma totalArea_linearImageBodies (E : Plane ≃L[ℝ] Plane) (A : Bodies) :
    totalArea (linearImageBodies E A) =
      affineAreaScale E.toContinuousAffineEquiv * totalArea A := by
  unfold totalArea linearImageBodies
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  exact area_affine_image E.toContinuousAffineEquiv (A i)

lemma closedMass_linearImageBodies (E : Plane ≃L[ℝ] Plane) (A : Bodies) (H : Halfspace) :
    closedMass (linearImageBodies E A) (H.linearImage E) =
      affineAreaScale E.toContinuousAffineEquiv * closedMass A H := by
  unfold closedMass linearImageBodies
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [H.linearImage_closedCap, ← image_inter E.injective]
  exact area_affine_image E.toContinuousAffineEquiv (A i ∩ H.closedCap i)

lemma fanDiagonal_areaScale (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    affineAreaScale (fanDiagonal a b ha hb).toContinuousAffineEquiv = a * b := by
  unfold affineAreaScale
  change |LinearMap.det (fanDiagonal a b ha hb).toLinearMap| = a * b
  rw [← LinearMap.det_toMatrix (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis,
    Matrix.det_fin_two]
  simp [LinearMap.toMatrix_apply, EuclideanSpace.basisFun_apply,
    EuclideanSpace.basisFun_repr, fanDiagonal_apply, abs_of_pos (mul_pos ha hb)]

/-- Divide the first planar coordinate by the positive total area. -/
noncomputable def normalizationEquiv (A : Bodies) (hpos : 0 < totalArea A) :
    Plane ≃L[ℝ] Plane :=
  fanDiagonal (totalArea A)⁻¹ 1 (inv_pos.mpr hpos) (by norm_num)

noncomputable def areaNormalize (A : Bodies) (hpos : 0 < totalArea A) : Bodies :=
  linearImageBodies (normalizationEquiv A hpos) A

lemma normalizationEquiv_areaScale (A : Bodies) (hpos : 0 < totalArea A) :
    affineAreaScale (normalizationEquiv A hpos).toContinuousAffineEquiv =
      (totalArea A)⁻¹ := by
  simp [normalizationEquiv, fanDiagonal_areaScale]

lemma areaNormalize_isBody (A : Bodies) (hA : ∀ i, IsBody (A i))
    (hpos : 0 < totalArea A) : ∀ i, IsBody (areaNormalize A hpos i) :=
  linearImageBodies_isBody (normalizationEquiv A hpos) A hA

lemma areaNormalize_compatible (A : Bodies) (hpos : 0 < totalArea A)
    (hA : Compatible A) : Compatible (areaNormalize A hpos) :=
  linearImageBodies_compatible (normalizationEquiv A hpos) A hA

@[simp] lemma totalArea_areaNormalize (A : Bodies) (hpos : 0 < totalArea A) :
    totalArea (areaNormalize A hpos) = 1 := by
  rw [areaNormalize, totalArea_linearImageBodies, normalizationEquiv_areaScale]
  exact inv_mul_cancel₀ hpos.ne'

/-- The three-body centerpoint theorem with arbitrary total area, including zero. -/
theorem centerpoint_unnormalized (A : Bodies) (hA : ∀ i, IsBody (A i))
    (hcomp : Compatible A) :
    ∃ i : Fin 3, ∃ x ∈ A i, ∀ H : Halfspace,
      x ∈ H.closedCap i → (2 / 9 : ℝ) * totalArea A ≤ closedMass A H := by
  by_cases hpos : 0 < totalArea A
  · obtain ⟨i, y, hy, hcenter⟩ := centerpoint (areaNormalize A hpos)
      (areaNormalize_isBody A hA hpos) (totalArea_areaNormalize A hpos)
      (areaNormalize_compatible A hpos hcomp)
    rcases hy with ⟨x, hx, rfl⟩
    refine ⟨i, x, hx, ?_⟩
    intro H hH
    have h := hcenter (H.linearImage (normalizationEquiv A hpos))
      ((H.mem_linearImage_closedCap (normalizationEquiv A hpos) i x).2 hH)
    rw [areaNormalize, closedMass_linearImageBodies, normalizationEquiv_areaScale] at h
    calc
      (2 / 9 : ℝ) * totalArea A = totalArea A * (2 / 9 : ℝ) := mul_comm _ _
      _ ≤ totalArea A * ((totalArea A)⁻¹ * closedMass A H) :=
        mul_le_mul_of_nonneg_left h hpos.le
      _ = closedMass A H := by rw [← mul_assoc, mul_inv_cancel₀ hpos.ne', one_mul]
  · obtain ⟨x, hx⟩ := (hA 0).2.2
    refine ⟨0, x, hx, fun H _ => ?_⟩
    exact (mul_nonpos_of_nonneg_of_nonpos (by norm_num) (le_of_not_gt hpos)).trans
      (closedMass_nonneg A H)

end ThreeSlices
