import ThreeSlices.Basic

open Set

namespace ThreeSlices

noncomputable def formCoordinates (f g : Plane →L[ℝ] ℝ) : Plane →L[ℝ] Plane :=
  (EuclideanSpace.equiv (Fin 2) ℝ).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi ![f, g])

@[simp] lemma formCoordinates_apply (f g : Plane →L[ℝ] ℝ) (x : Plane) (i : Fin 2) :
    formCoordinates f g x i = ![f, g] i x := rfl

lemma formCoordinates_injective (f g : Plane →L[ℝ] ℝ)
    (hfg : LinearIndependent ℝ ![f, g]) : Function.Injective (formCoordinates f g) := by
  intro x y hxy
  have hi (i : Fin 2) : ![f, g] i x = ![f, g] i y := by
    simpa using congrArg (fun z : Plane => z i) hxy
  have hdim : Fintype.card (Fin 2) = Module.finrank ℝ (Plane →L[ℝ] ℝ) := by
    rw [← (LinearMap.toContinuousLinearMap :
      (Plane →ₗ[ℝ] ℝ) ≃ₗ[ℝ] (Plane →L[ℝ] ℝ)).finrank_eq]
    change Fintype.card (Fin 2) = Module.finrank ℝ (Module.Dual ℝ Plane)
    simp [Plane]
  have hspan := hfg.span_eq_top_of_card_eq_finrank hdim
  apply (SeparatingDual.eq_iff_forall_dual_eq (R := ℝ)).mpr
  intro φ
  have hφ : φ ∈ Submodule.span ℝ (Set.range ![f, g]) := by
    rw [hspan]
    trivial
  refine Submodule.span_induction (p := fun φ _ => φ x = φ y) ?_ ?_ ?_ ?_ hφ
  · rintro _ ⟨i, rfl⟩
    exact hi i
  · simp
  · intro φ ψ _ _ hφ hψ
    simp [hφ, hψ]
  · intro a φ _ hφ
    simp [hφ]

/-- Coordinates defined by independent forms, with inverse constructed from injectivity. -/
noncomputable def formCoordinatesEquiv (f g : Plane →L[ℝ] ℝ)
    (hfg : LinearIndependent ℝ ![f, g]) : Plane ≃L[ℝ] Plane :=
  (LinearEquiv.ofInjectiveEndo (formCoordinates f g).toLinearMap
    (formCoordinates_injective f g hfg)).toContinuousLinearEquiv

@[simp] lemma formCoordinatesEquiv_apply (f g : Plane →L[ℝ] ℝ)
    (hfg : LinearIndependent ℝ ![f, g]) (x : Plane) (i : Fin 2) :
    formCoordinatesEquiv f g hfg x i = ![f, g] i x := rfl

/-- Translate the two prescribed boundary lines to the coordinate axes. -/
noncomputable def normalizedCoordinates (f g : Plane →L[ℝ] ℝ)
    (hfg : LinearIndependent ℝ ![f, g]) (s t : ℝ) : Plane ≃ᴬ[ℝ] Plane :=
  (formCoordinatesEquiv f g hfg).toContinuousAffineEquiv.trans
    (ContinuousAffineEquiv.constVAdd ℝ Plane
      (-(EuclideanSpace.equiv (Fin 2) ℝ).symm ![s, t]))

@[simp] lemma normalizedCoordinates_apply (f g : Plane →L[ℝ] ℝ)
    (hfg : LinearIndependent ℝ ![f, g]) (s t : ℝ) (x : Plane) (i : Fin 2) :
    normalizedCoordinates f g hfg s t x i = ![f, g] i x - ![s, t] i := by
  change (-((EuclideanSpace.equiv (Fin 2) ℝ).symm ![s, t]) +
    formCoordinatesEquiv f g hfg x) i = _
  simp [sub_eq_add_neg, add_comm]

lemma normalizedCoordinates_symm_apply (f g : Plane →L[ℝ] ℝ)
    (hfg : LinearIndependent ℝ ![f, g]) (s t : ℝ) (y : Plane) (i : Fin 2) :
    ![f, g] i ((normalizedCoordinates f g hfg s t).symm y) = y i + ![s, t] i := by
  have hi := congrArg (fun z : Plane => z i)
    ((normalizedCoordinates f g hfg s t).apply_symm_apply y)
  rw [normalizedCoordinates_apply] at hi
  linarith

lemma normalizedCoordinates_first_halfplane (f g : Plane →L[ℝ] ℝ)
    (hfg : LinearIndependent ℝ ![f, g]) (s t : ℝ) (y : Plane) :
    f ((normalizedCoordinates f g hfg s t).symm y) < s ↔ y 0 < 0 := by
  have hi := normalizedCoordinates_symm_apply f g hfg s t y 0
  simp only [Matrix.cons_val_zero] at hi
  rw [hi]
  constructor <;> intro h <;> linarith

lemma normalizedCoordinates_second_halfplane (f g : Plane →L[ℝ] ℝ)
    (hfg : LinearIndependent ℝ ![f, g]) (s t : ℝ) (y : Plane) :
    g ((normalizedCoordinates f g hfg s t).symm y) < t ↔ y 1 < 0 := by
  have hi := normalizedCoordinates_symm_apply f g hfg s t y 1
  simp only [Matrix.cons_val_one, Matrix.cons_val_zero] at hi
  rw [hi]
  constructor <;> intro h <;> linarith

lemma normalizedCoordinates_image_first_halfplane (f g : Plane →L[ℝ] ℝ)
    (hfg : LinearIndependent ℝ ![f, g]) (s t : ℝ) :
    normalizedCoordinates f g hfg s t '' {x | f x < s} = {y | y 0 < 0} := by
  change (normalizedCoordinates f g hfg s t).toEquiv '' {x | f x < s} = _
  rw [Equiv.image_eq_preimage_symm]
  ext y
  exact normalizedCoordinates_first_halfplane f g hfg s t y

lemma normalizedCoordinates_image_second_halfplane (f g : Plane →L[ℝ] ℝ)
    (hfg : LinearIndependent ℝ ![f, g]) (s t : ℝ) :
    normalizedCoordinates f g hfg s t '' {x | g x < t} = {y | y 1 < 0} := by
  change (normalizedCoordinates f g hfg s t).toEquiv '' {x | g x < t} = _
  rw [Equiv.image_eq_preimage_symm]
  ext y
  exact normalizedCoordinates_second_halfplane f g hfg s t y

lemma linear_form_coordinate_expansion (h : Plane →L[ℝ] ℝ) (y : Plane) :
    h y = h (EuclideanSpace.single 0 1) * y 0 +
      h (EuclideanSpace.single 1 1) * y 1 := by
  have hy : y = y 0 • EuclideanSpace.single 0 1 + y 1 • EuclideanSpace.single 1 1 := by
    ext i
    fin_cases i <;> simp
  calc
    h y = h (y 0 • EuclideanSpace.single 0 1 + y 1 • EuclideanSpace.single 1 1) :=
      congrArg h hy
    _ = _ := by simp [mul_comm]

/-- A linear form becomes an affine expression after any affine coordinate change. -/
theorem affine_form_coordinate_expansion (e : Plane ≃ᴬ[ℝ] Plane)
    (h : Plane →L[ℝ] ℝ) :
    ∃ a b c : ℝ, ∀ y : Plane, h (e.symm y) = a * y 0 + b * y 1 + c := by
  let k := h.comp e.symm.toAffineEquiv.linear.toLinearMap.toContinuousLinearMap
  refine ⟨k (EuclideanSpace.single 0 1), k (EuclideanSpace.single 1 1),
    h (e.symm 0), ?_⟩
  intro y
  have hy : e.symm y = e.symm.toAffineEquiv.linear y + e.symm 0 := by
    simpa using e.symm.toAffineEquiv.map_vadd (0 : Plane) y
  rw [hy, map_add]
  exact congrArg (fun z : ℝ => z + h (e.symm 0))
    (linear_form_coordinate_expansion k y)

/-- Halfplanes retain an explicit affine inequality in any affine coordinates. -/
theorem affine_image_halfplane_coordinates (e : Plane ≃ᴬ[ℝ] Plane)
    (h : Plane →L[ℝ] ℝ) (q : ℝ) :
    ∃ a b c : ℝ,
      e '' {x | h x < q} = {y | 0 < a * y 0 + b * y 1 + c} := by
  obtain ⟨a, b, c, hc⟩ := affine_form_coordinate_expansion e h
  refine ⟨-a, -b, q - c, ?_⟩
  change e.toEquiv '' {x | h x < q} = _
  rw [Equiv.image_eq_preimage_symm]
  ext y
  change h (e.symm y) < q ↔ 0 < -a * y 0 + -b * y 1 + (q - c)
  rw [hc]
  constructor <;> intro hy <;> nlinarith

end ThreeSlices
