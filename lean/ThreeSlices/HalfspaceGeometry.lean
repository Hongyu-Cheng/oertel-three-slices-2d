import ThreeSlices.MixedIntegerBasic

open Set

namespace ThreeSlices

def Halfspace.Proper (H : Halfspace) : Prop := H.height ≠ 0 ∨ H.planar ≠ 0

noncomputable def Halfspace.normal (H : Halfspace) : Space →L[ℝ] ℝ :=
  H.height • ContinuousLinearMap.fst ℝ ℝ Plane +
    H.planar.comp (ContinuousLinearMap.snd ℝ ℝ Plane)

def Halfspace.ofFunctional (f : Space →L[ℝ] ℝ) (b : ℝ) : Halfspace :=
  ⟨f (1, 0), f.comp (ContinuousLinearMap.inr ℝ ℝ Plane), b⟩

lemma Halfspace.closedSet_eq (H : Halfspace) :
    H.closedSet = {p | H.normal p ≤ H.threshold} := by
  ext p
  simp [Halfspace.closedSet, Halfspace.normal, le_sub_iff_add_le, add_comm]

lemma Halfspace.ofFunctional_normal (f : Space →L[ℝ] ℝ) (b : ℝ) :
    (Halfspace.ofFunctional f b).normal = f := by
  apply ContinuousLinearMap.ext
  intro p
  have hp : p = p.1 • (1, (0 : Plane)) + (0, p.2) := by ext <;> simp
  change f (1, 0) * p.1 + f (0, p.2) = f p
  conv_rhs => rw [hp, map_add, map_smul]
  simp [smul_eq_mul, mul_comm]

lemma Halfspace.proper_iff_normal_ne_zero (H : Halfspace) : H.Proper ↔ H.normal ≠ 0 := by
  constructor
  · intro h hn
    have hh := congrArg (fun f : Space →L[ℝ] ℝ => f (1, 0)) hn
    have hh₀ : H.height = 0 := by simpa [Halfspace.normal] using hh
    have hp₀ : H.planar = 0 := by
      apply ContinuousLinearMap.ext
      intro x
      have hp := congrArg (fun f : Space →L[ℝ] ℝ => f (0, x)) hn
      simpa [Halfspace.normal] using hp
    exact h.elim (fun h => h hh₀) (fun h => h hp₀)
  · intro hn
    by_contra h
    simp only [Halfspace.Proper, not_or, not_not] at h
    apply hn
    simp [Halfspace.normal, h.1, h.2]

lemma Halfspace.ofFunctional_proper {f : Space →L[ℝ] ℝ} (hf : f ≠ 0) (b : ℝ) :
    (Halfspace.ofFunctional f b).Proper := by
  rw [Halfspace.proper_iff_normal_ne_zero, Halfspace.ofFunctional_normal]
  exact hf

lemma Halfspace.ofFunctional_closedSet (f : Space →L[ℝ] ℝ) (b : ℝ) :
    (Halfspace.ofFunctional f b).closedSet = {p | f p ≤ b} := by
  rw [Halfspace.closedSet_eq, Halfspace.ofFunctional_normal]
  rfl

end ThreeSlices
