import ThreeSlices.AffineArea
import ThreeSlices.AffineNormalization
import ThreeSlices.CoverReduction
import ThreeSlices.Nonparallel
import ThreeSlices.NormalizedCovering

open Set MeasureTheory

namespace ThreeSlices

/-- The full geometry of Lemma 2 for a proper covering triple, using only the
normalized six-sector inequality as its input. -/
theorem triple_covering_of_tsintsifas (hts : NormalizedTsintsifasStatement)
    (A : Set Plane) (hA : IsBody A) (H K L : Halfspace) (hH : H.planar ≠ 0)
    (hcover : H.openCap 1 ∪ K.openCap 1 ∪ L.openCap 1 = univ)
    (hHK : 0 < area (A \ (H.openCap 1 ∪ K.openCap 1)))
    (hHL : 0 < area (A \ (H.openCap 1 ∪ L.openCap 1)))
    (hKL : 0 < area (A \ (K.openCap 1 ∪ L.openCap 1)))
    (β : ℝ) (hβ : 0 < β) (hcapH : area (A ∩ H.openCap 1) ≤ β)
    (hcapK : area (A ∩ K.openCap 1) ≤ β) (hcapL : area (A ∩ L.openCap 1) ≤ β) :
    area (A \ (K.openCap 1 ∪ L.openCap 1)) ^ 2 ≤ β * area (A ∩ K.openCap 1 ∩ L.openCap 1) ∨
    area (A \ (L.openCap 1 ∪ H.openCap 1)) ^ 2 ≤ β * area (A ∩ L.openCap 1 ∩ H.openCap 1) ∨
    area (A \ (H.openCap 1 ∪ K.openCap 1)) ^ 2 ≤ β * area (A ∩ H.openCap 1 ∩ K.openCap 1) := by
  have hn {U V : Set Plane} (hp : 0 < area (A \ (U ∪ V))) : U ∪ V ≠ univ := by
    intro he
    simp [he, area] at hp
  have hfg := H.normals_independent_of_proper_triple K L hH hcover (hn hHK) (hn hHL) (hn hKL)
  let e := normalizedCoordinates H.planar K.planar hfg
    (H.threshold - H.height) (K.threshold - K.height)
  have heH : e '' H.openCap 1 = {x : Plane | x 0 < 0} := by
    simpa [e, Halfspace.openCap] using normalizedCoordinates_image_first_halfplane
      H.planar K.planar hfg (H.threshold - H.height) (K.threshold - K.height)
  have heK : e '' K.openCap 1 = {x : Plane | x 1 < 0} := by
    simpa [e, Halfspace.openCap] using normalizedCoordinates_image_second_halfplane
      H.planar K.planar hfg (H.threshold - H.height) (K.threshold - K.height)
  obtain ⟨a, b, c, hthird⟩ := affine_image_halfplane_coordinates e L.planar
    (L.threshold - L.height)
  have heL : e '' L.openCap 1 = {x : Plane | 0 < a * x 0 + b * x 1 + c} := by
    simpa [Halfspace.openCap] using hthird
  have hB : IsBody (e '' A) := ⟨hA.1.image e.continuous,
    hA.2.1.affine_image e.toAffineEquiv.toAffineMap, hA.2.2.image e⟩
  have hcov : ∀ x : Plane, x 0 < 0 ∨ x 1 < 0 ∨ 0 < a * x 0 + b * x 1 + c := by
    have he := congrArg (fun S : Set Plane => e '' S) hcover
    rw [image_union, image_union, heH, heK, heL, image_univ_of_surjective e.surjective] at he
    intro x
    have hx := he.symm ▸ (mem_univ x)
    change (x 0 < 0 ∨ x 1 < 0) ∨ 0 < a * x 0 + b * x 1 + c at hx
    tauto
  have hpos (U V : Set Plane) (hp : 0 < area (A \ (U ∪ V))) :
      0 < area ((e '' A) \ ((e '' U) ∪ (e '' V))) := by
    rw [← image_union, ← image_sdiff e.injective, area_affine_image]
    exact mul_pos (affineAreaScale_pos e) hp
  obtain ⟨ha, hb, hc, hzero⟩ := normalized_cover_origin_interior hB.2.1 hcov
    (by simpa [heH, heK] using hpos _ _ hHK)
    (by simpa [heH, heL] using hpos _ _ hHL)
    (by simpa [heK, heL] using hpos _ _ hKL)
  have hcap (U : Set Plane) (hu : area (A ∩ U) ≤ β) :
      area ((e '' A) ∩ (e '' U)) ≤ affineAreaScale e * β := by
    rw [← image_inter e.injective, area_affine_image]
    exact mul_le_mul_of_nonneg_left hu (affineAreaScale_pos e).le
  have hpair := normalized_covering_of_tsintsifas hts hB hzero a b c
    (affineAreaScale e * β) ha hb hc (mul_pos (affineAreaScale_pos e) hβ)
    (by simpa [heH] using hcap _ hcapH)
    (by simpa [heK] using hcap _ hcapK)
    (by simpa [heL] using hcap _ hcapL)
  rcases hpair with hp | hp | hp
  · left
    apply (affine_pair_bound_iff e A (K.openCap 1) (L.openCap 1) β).mp
    simpa [heK, heL] using hp
  · right; left
    apply (affine_pair_bound_iff e A (L.openCap 1) (H.openCap 1) β).mp
    simpa [heL, heH] using hp
  · right; right
    apply (affine_pair_bound_iff e A (H.openCap 1) (K.openCap 1) β).mp
    simpa [heH, heK] using hp

/-- Lemma 2 follows from the normalized Tsintsifas inequality. -/
theorem planar_covering_of_tsintsifas (hts : NormalizedTsintsifasStatement) :
    PlanarCoveringStatement := by
  intro A hA β hβ ι _ G hG hcover hcap
  rcases cover_zero_area_pair_or_three A hA.2.1 hA.2.2 G hcover with
    ⟨r, s, hz⟩ | ⟨r, s, t, _, _, _, hplane, hpositive⟩
  · exact ⟨r, s, pair_cover_bound_of_area_zero A (G r) (G s) β hβ.le hz⟩
  · rcases triple_covering_of_tsintsifas hts A hA (G r) (G s) (G t) (hG r) hplane
      (hpositive r s) (hpositive r t) (hpositive s t) β hβ (hcap r) (hcap s) (hcap t)
      with hp | hp | hp
    · exact ⟨s, t, hp⟩
    · exact ⟨t, r, hp⟩
    · exact ⟨r, s, hp⟩

end ThreeSlices
