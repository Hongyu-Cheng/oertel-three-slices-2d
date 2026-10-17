import ThreeSlices.Basic

open Set MeasureTheory

namespace ThreeSlices

lemma volume_linear_levelSet (f : Plane →L[ℝ] ℝ) (hf : f ≠ 0) (c : ℝ) :
    volume {x | f x = c} = 0 := by
  let L : AffineSubspace ℝ Plane :=
    ({c} : AffineSubspace ℝ ℝ).comap f.toLinearMap.toAffineMap
  have hL : L ≠ ⊤ := by
    intro htop
    have hall : ∀ x : Plane, f x = c := by
      intro x
      have hx : x ∈ L := by rw [htop]; trivial
      simpa [L, AffineSubspace.mem_comap] using hx
    have hc : c = 0 := by simpa using (hall 0).symm
    apply hf
    ext x
    simpa [hc] using hall x
  simpa [L, AffineSubspace.coe_comap, Set.preimage] using
    Measure.addHaar_affineSubspace volume L hL

lemma exists_mem_ne_linear_levels {S : Set Plane} (hS : 0 < area S)
    (f g : Plane →L[ℝ] ℝ) (hf : f ≠ 0) (hg : g ≠ 0) (c d : ℝ) :
    ∃ x ∈ S, f x ≠ c ∧ g x ≠ d := by
  classical
  by_contra h
  have hsub : S ⊆ {x | f x = c} ∪ {x | g x = d} := by
    intro x hx
    by_cases hfx : f x = c
    · exact Or.inl hfx
    · right
      by_contra hgx
      exact h ⟨x, hx, hfx, hgx⟩
  have hz : volume S = 0 := measure_mono_null hsub
    (measure_union_null (volume_linear_levelSet f hf c) (volume_linear_levelSet g hg d))
  simp [area, Measure.real, hz] at hS

lemma coordinate_proj_ne_zero (i : Fin 2) : EuclideanSpace.proj (𝕜 := ℝ) i ≠ 0 := by
  intro h
  have he := congrArg (fun f : Plane →L[ℝ] ℝ => f (EuclideanSpace.single i 1)) h
  simp at he

lemma volume_coordinate_levelSet (i : Fin 2) (c : ℝ) :
    volume {x : Plane | x i = c} = 0 := by
  simpa using volume_linear_levelSet (EuclideanSpace.proj (𝕜 := ℝ) i)
    (coordinate_proj_ne_zero i) c

lemma exists_mem_ne_zero_coordinates {S : Set Plane} (hS : 0 < area S) :
    ∃ x ∈ S, x 0 ≠ 0 ∧ x 1 ≠ 0 := by
  simpa using exists_mem_ne_linear_levels hS
    (EuclideanSpace.proj (𝕜 := ℝ) 0) (EuclideanSpace.proj (𝕜 := ℝ) 1)
    (coordinate_proj_ne_zero 0) (coordinate_proj_ne_zero 1) 0 0

end ThreeSlices
