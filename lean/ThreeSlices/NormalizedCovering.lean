import ThreeSlices.SectorGeometry
import ThreeSlices.TripleGeometry

open Set MeasureTheory

namespace ThreeSlices

/-- The geometric Tsintsifas inequality in normalized coordinates. -/
def NormalizedTsintsifasStatement : Prop :=
  ∀ (A : Set Plane), IsBody A → (0 : Plane) ∈ interior A →
    ∀ a b : ℝ, 0 < a → 0 < b →
      let U : Set Plane := {x | x 0 < 0}
      let V : Set Plane := {x | x 1 < 0}
      let W : Set Plane := {x | 0 ≤ a * x 0 + b * x 1}
      (3 / 2 : ℝ) ≤ area (A ∩ V ∩ W) / area (A \ (V ∪ W)) +
        area (A ∩ W ∩ U) / area (A \ (W ∪ U)) +
        area (A ∩ U ∩ V) / area (A \ (U ∪ V))

/-- Tsintsifas's concurrent-sector inequality gives Lemma 2 for a normalized cover. -/
theorem normalized_covering_of_tsintsifas (htsint : NormalizedTsintsifasStatement)
    {A : Set Plane} (hA : IsBody A) (hzero : (0 : Plane) ∈ interior A)
    (a b c β : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hβ : 0 < β)
    (hu : area (A ∩ {x : Plane | x 0 < 0}) ≤ β)
    (hv : area (A ∩ {x : Plane | x 1 < 0}) ≤ β)
    (hz : area (A ∩ {x : Plane | 0 < a * x 0 + b * x 1 + c}) ≤ β) :
    let U : Set Plane := {x | x 0 < 0}
    let V : Set Plane := {x | x 1 < 0}
    let Z : Set Plane := {x | 0 < a * x 0 + b * x 1 + c}
    area (A \ (V ∪ Z)) ^ 2 ≤ β * area (A ∩ V ∩ Z) ∨
      area (A \ (Z ∪ U)) ^ 2 ≤ β * area (A ∩ Z ∩ U) ∨
      area (A \ (U ∪ V)) ^ 2 ≤ β * area (A ∩ U ∩ V) := by
  let U : Set Plane := {x | x 0 < 0}
  let V : Set Plane := {x | x 1 < 0}
  let W : Set Plane := {x | 0 ≤ a * x 0 + b * x 1}
  let Z : Set Plane := {x | 0 < a * x 0 + b * x 1 + c}
  change area (A ∩ U) ≤ β at hu
  change area (A ∩ V) ≤ β at hv
  change area (A ∩ Z) ≤ β at hz
  change area (A \ (V ∪ Z)) ^ 2 ≤ β * area (A ∩ V ∩ Z) ∨
    area (A \ (Z ∪ U)) ^ 2 ≤ β * area (A ∩ Z ∩ U) ∨
    area (A \ (U ∪ V)) ^ 2 ≤ β * area (A ∩ U ∩ V)
  obtain ⟨hU, hV, hW, htriple⟩ := normalized_sector_sets ha hb
  obtain ⟨hshrink, hplane⟩ := normalized_closed_shrink ha.le hb.le hc
  have hcover : A ⊆ U ∪ V ∪ W := by
    intro x _
    rcases hplane x with hx | hx | hx
    · exact Or.inl (Or.inl hx)
    · exact Or.inl (Or.inr hx)
    · exact Or.inr hx
  have htripleA : A ∩ U ∩ V ∩ W = ∅ := by
    simpa only [inter_assoc, inter_empty] using
      congrArg (fun S : Set Plane => A ∩ S) htriple
  have hw : area (A ∩ W) ≤ β := by
    apply le_trans _ hz
    exact measureReal_mono (inter_subset_inter subset_rfl hshrink)
      (measure_ne_top_of_subset inter_subset_left (hA.1.measure_ne_top (μ := volume)))
  have hratio := htsint A hA hzero a b ha hb
  have hselect := sector_pair_of_ratio hA.1 hU hV hW hcover htripleA
    β hβ hu hv hw hratio
  rcases hselect with h | h | h
  · exact Or.inl (pair_bound_of_enlargement hA.1 subset_rfl hshrink hβ.le h)
  · exact Or.inr (Or.inl (pair_bound_of_enlargement hA.1 hshrink subset_rfl hβ.le h))
  · exact Or.inr (Or.inr h)

end ThreeSlices
