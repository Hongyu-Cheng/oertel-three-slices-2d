import ThreeSlices.Boundary

open Set MeasureTheory

namespace ThreeSlices

theorem normalized_sector_areas_eq_closed {A : Set Plane} {a b : ℝ}
    (ha : 0 < a) (_hb : 0 < b) :
    let U : Set Plane := {x | x 0 < 0}
    let V : Set Plane := {x | x 1 < 0}
    let W : Set Plane := {x | 0 ≤ a * x 0 + b * x 1}
    area (A ∩ V ∩ W) = area (A ∩ {x | x 1 ≤ 0 ∧ 0 ≤ a * x 0 + b * x 1}) ∧
    area (A ∩ W ∩ U) = area (A ∩ {x | x 0 ≤ 0 ∧ 0 ≤ a * x 0 + b * x 1}) ∧
    area (A ∩ U ∩ V) = area (A ∩ {x | x 0 ≤ 0 ∧ x 1 ≤ 0}) ∧
    area (A \ (V ∪ W)) = area (A ∩ {x | 0 ≤ x 1 ∧ a * x 0 + b * x 1 ≤ 0}) ∧
    area (A \ (W ∪ U)) = area (A ∩ {x | 0 ≤ x 0 ∧ a * x 0 + b * x 1 ≤ 0}) ∧
    area (A \ (U ∪ V)) = area (A ∩ {x | 0 ≤ x 0 ∧ 0 ≤ x 1}) := by
  let l : Plane →L[ℝ] ℝ := a • EuclideanSpace.proj 0 + b • EuclideanSpace.proj 1
  have hl : l ≠ 0 := by
    intro h
    have he := congrArg (fun f : Plane →L[ℝ] ℝ => f (EuclideanSpace.single 0 1)) h
    simp [l] at he
    exact ha.ne' he
  have hzero : volume {x : Plane | a * x 0 + b * x 1 = 0} = 0 := by
    simpa [l] using volume_linear_levelSet l hl 0
  have h₀ : ∀ᵐ x : Plane ∂volume, x 0 ≠ 0 := by
    simpa only [ae_iff, not_ne_iff] using volume_coordinate_levelSet 0 0
  have h₁ : ∀ᵐ x : Plane ∂volume, x 1 ≠ 0 := by
    simpa only [ae_iff, not_ne_iff] using volume_coordinate_levelSet 1 0
  have h₂ : ∀ᵐ x : Plane ∂volume, a * x 0 + b * x 1 ≠ 0 := by
    simpa only [ae_iff, not_ne_iff] using hzero
  have heq {S T : Set Plane}
      (h : ∀ x : Plane, x 0 ≠ 0 → x 1 ≠ 0 → a * x 0 + b * x 1 ≠ 0 →
        (x ∈ S ↔ x ∈ T)) : area S = area T := by
    apply measureReal_congr
    filter_upwards [h₀, h₁, h₂] with x hx hy hl
    exact propext (h x hx hy hl)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals
    apply heq
    intro x hx hy hl
    simp [le_iff_lt_or_eq, hx, hy, hl, Ne.symm hx, Ne.symm hy, Ne.symm hl,
      and_assoc, and_comm, and_left_comm]

end ThreeSlices
