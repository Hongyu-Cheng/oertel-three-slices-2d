import ThreeSlices.Trimming
import Grunbaum.Main

open Set MeasureTheory

namespace ThreeSlices

/-- The volume centroid of a planar set. -/
noncomputable def planarCentroid (A : Set Plane) : Plane := ⨍ x in A, x ∂volume

lemma planarCentroid_mem {A : Set Plane} (hA : IsBody A) (hp : 0 < area A) :
    planarCentroid A ∈ A := by
  have hv : volume A ≠ 0 := by
    intro hz
    simp [area, Measure.real, hz] at hp
  exact hA.2.1.set_average_mem hA.1.isClosed hv hA.1.measure_lt_top.ne
    (ae_restrict_mem hA.1.measurableSet)
    (continuous_id.continuousOn.integrableOn_compact hA.1)

/-- Every closed cap containing the centroid has at least 4/9 of a positive-area body's area. -/
theorem planarCentroid_closedCap_lower {A : Set Plane} (hA : IsBody A)
    (hp : 0 < area A) (H : Halfspace) (i : Fin 3)
    (hcentroid : planarCentroid A ∈ H.closedCap i) :
    (4 / 9 : ℝ) * area A ≤ area (A ∩ H.closedCap i) := by
  by_cases hflat : H.planar = 0
  · have he : H.closedCap i = univ := by
      ext y
      simpa [Halfspace.closedCap, hflat] using hcentroid
    rw [he, inter_univ]
    linarith
  let C : Grunbaum.FullDimensionalConvexBody 1 :=
    ⟨A, hA.2.1, hA.1, positive_area_interior hA.2.1 hp⟩
  have hb := Grunbaum.grunbaum_centroid_halfspace_functional C H.planar hflat
    (H.threshold - H.height * (i : ℝ)) hcentroid
  have hratio : (4 / 9 : ℝ) ≤ area (A ∩ H.closedCap i) / area A := by
    norm_num [Grunbaum.grunbaumConstant, Grunbaum.halfspaceVolumeRatio,
      Grunbaum.closedHalfspace, Halfspace.closedCap, C, area, Measure.real,
      ENNReal.toReal_div] at hb ⊢
    exact hb
  exact (le_div_iff₀ hp).mp hratio

end ThreeSlices
