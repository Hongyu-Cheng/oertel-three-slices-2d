import ThreeSlices.Trimming
import Mathlib.Analysis.Convex.Radon

open Set

namespace ThreeSlices

def coverConstraint {ι : Type} (A : Set Plane) (G : ι → Halfspace) : Option ι → Set Plane
  | none => A
  | some k => ((G k).openCap 1)ᶜ

/-- Helly's reduction of a planar halfplane cover to at most three convex constraints. -/
theorem cover_helly_witness {ι : Type} [Fintype ι]
    (A : Set Plane) (hA : Convex ℝ A) (G : ι → Halfspace)
    (hcover : A ⊆ ⋃ j, (G j).openCap 1) :
    ∃ T : Finset (Option ι), T.card ≤ 3 ∧
      (⋂ j ∈ T, coverConstraint A G j) = ∅ := by
  classical
  let F := coverConstraint A G
  have hc : ∀ j, Convex ℝ (F j) := by
    intro j
    cases j with
    | none => exact hA
    | some k => exact (G k).convex_compl_openCap 1
  have hempty : ¬ (⋂ j, F j).Nonempty := by
    rintro ⟨x, hx⟩
    have hxA : x ∈ A := mem_iInter.mp hx none
    obtain ⟨j, hj⟩ := mem_iUnion.mp (hcover hxA)
    have hn : x ∉ (G j).openCap 1 := mem_iInter.mp hx (some j)
    exact hn hj
  by_contra h
  push Not at h
  have hall : (⋂ j ∈ Finset.univ, F j).Nonempty := by
    apply Convex.helly_theorem' (𝕜 := ℝ) (fun j _ => hc j)
    intro I _hI hcard
    have hi : I.card ≤ 3 := by simpa [Plane] using hcard
    simpa only [F] using h I hi
  exact hempty (by simpa using hall)

end ThreeSlices
