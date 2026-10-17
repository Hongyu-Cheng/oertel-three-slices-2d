import ThreeSlices.HalfspaceGeometry
import ThreeSlices.SliceUnionMass
import ThreeSlices.MixedIntegerSharpness

open Set

namespace ThreeSlices

def halfspaceMasses (C : Set Space) (p : Space) : Set ℝ :=
  {m | ∃ H : Halfspace, H.Proper ∧ p ∈ H.closedSet ∧ m = mixedArea (C ∩ H.closedSet)}

/-- The infimum of masses over closed halfspaces with nonzero normal containing the point. -/
noncomputable def halfspaceDepth (C : Set Space) (p : Space) : ℝ :=
  sInf (halfspaceMasses C p)

lemma halfspaceMasses_nonempty (C : Set Space) (p : Space) :
    (halfspaceMasses C p).Nonempty := by
  let H : Halfspace := ⟨1, 0, p.1⟩
  refine ⟨mixedArea (C ∩ H.closedSet), H, Or.inl (by norm_num [H]), ?_, rfl⟩
  simp [H, Halfspace.closedSet]

lemma halfspaceMasses_bddBelow (C : Set Space) (p : Space) :
    BddBelow (halfspaceMasses C p) := by
  refine ⟨0, ?_⟩
  rintro _ ⟨H, _, _, rfl⟩
  exact ENNReal.toReal_nonneg

/-- The coordinate halfspace representation ranges over every nonzero continuous linear normal. -/
lemma halfspaceMasses_eq_functionals (C : Set Space) (p : Space) :
    halfspaceMasses C p = {m | ∃ f : Space →L[ℝ] ℝ, ∃ b : ℝ,
      f ≠ 0 ∧ f p ≤ b ∧ m = mixedArea (C ∩ {q | f q ≤ b})} := by
  ext m
  constructor
  · rintro ⟨H, hproper, hp, rfl⟩
    refine ⟨H.normal, H.threshold, H.proper_iff_normal_ne_zero.mp hproper, ?_, ?_⟩
    · simpa [H.closedSet_eq] using hp
    · rw [H.closedSet_eq]
  · rintro ⟨f, b, hf, hp, rfl⟩
    refine ⟨Halfspace.ofFunctional f b, Halfspace.ofFunctional_proper hf b, ?_, ?_⟩
    · simpa [Halfspace.ofFunctional_closedSet] using hp
    · rw [Halfspace.ofFunctional_closedSet]

lemma le_halfspaceDepth_iff (C : Set Space) (p : Space) (a : ℝ) :
    a ≤ halfspaceDepth C p ↔ ∀ H : Halfspace, H.Proper → p ∈ H.closedSet →
      a ≤ mixedArea (C ∩ H.closedSet) := by
  constructor
  · intro ha H hproper hp
    exact ha.trans (csInf_le (halfspaceMasses_bddBelow C p) ⟨H, hproper, hp, rfl⟩)
  · intro h
    apply le_csInf (halfspaceMasses_nonempty C p)
    rintro _ ⟨H, hproper, hp, rfl⟩
    exact h H hproper hp

lemma halfspaceDepth_le_mass (C : Set Space) (p : Space) (H : Halfspace)
    (hproper : H.Proper) (hp : p ∈ H.closedSet) :
    halfspaceDepth C p ≤ mixedArea (C ∩ H.closedSet) :=
  csInf_le (halfspaceMasses_bddBelow C p) ⟨H, hproper, hp, rfl⟩

/-- The abstract's relative depth bound, including triples of total area zero. -/
theorem paper_centerpoint_unnormalized (A : Bodies) (hA : ∀ i, IsBody (A i))
    (hcomp : Compatible A) :
    ∃ p ∈ sliceUnion A, (2 / 9 : ℝ) * totalArea A ≤ halfspaceDepth (sliceUnion A) p := by
  obtain ⟨i, x, hx, hpoint⟩ := centerpoint_unnormalized A hA hcomp
  refine ⟨((i : ℝ), x), mem_iUnion.mpr ⟨i, by simpa using hx⟩, ?_⟩
  rw [le_halfspaceDepth_iff]
  intro H _ hp
  rw [mixedArea_sliceUnion_inter_closedSet A (fun i => (hA i).1)]
  exact hpoint H hp

/-- The first assertion of Theorem 1, using the paper's slice union, mass and infimum depth. -/
theorem paper_centerpoint (A : Bodies) (hA : ∀ i, IsBody (A i))
    (hnorm : totalArea A = 1) (hcomp : Compatible A) :
    ∃ p ∈ sliceUnion A, (2 / 9 : ℝ) ≤ halfspaceDepth (sliceUnion A) p := by
  simpa only [hnorm, mul_one] using paper_centerpoint_unnormalized A hA hcomp

/-- The second assertion of Theorem 1, expressed with the same infimum depth. -/
theorem paper_mixed_integer_centerpoint (C : Set Space) (hC : IsCompact C)
    (hconvex : Convex ℝ C) (hthree : (positiveSlices C).ncard = 3) :
    ∃ z : ℤ, ∃ x : Plane, ((z : ℝ), x) ∈ C ∧
      (2 / 9 : ℝ) * mixedArea C ≤ halfspaceDepth C ((z : ℝ), x) := by
  obtain ⟨z, x, hx, hpoint⟩ := mixed_integer_centerpoint C hC hconvex hthree
  exact ⟨z, x, hx, (le_halfspaceDepth_iff C _ _).mpr (fun H _ hp => hpoint H hp)⟩

/-- Every proposed improvement of two ninths fails for a normalized triple's depth. -/
theorem paper_sharpness (c : ℝ) (hc : (2 / 9 : ℝ) < c) :
    ∃ A : Bodies, (∀ i, IsBody (A i)) ∧ totalArea A = 1 ∧ Compatible A ∧
      ∀ p ∈ sliceUnion A, halfspaceDepth (sliceUnion A) p < c := by
  obtain ⟨A, hA, hnorm, hcomp, hsharp⟩ := sharpness_normalized c hc
  refine ⟨A, hA, hnorm, hcomp, ?_⟩
  intro p hp
  obtain ⟨i, hi⟩ := mem_iUnion.mp hp
  have hz : p.1 = (i : ℝ) := hi.1
  obtain ⟨H, hproper, hmem, hmass⟩ := hsharp i p.2 hi.2
  have hpH : p ∈ H.closedSet := by
    simpa [Halfspace.closedCap, Halfspace.closedSet, hz] using hmem
  apply (halfspaceDepth_le_mass (sliceUnion A) p H hproper hpH).trans_lt
  rwa [mixedArea_sliceUnion_inter_closedSet A (fun i => (hA i).1)]

/-- Mixed-integer sharpness in terms of halfspace depth. -/
theorem paper_mixed_integer_sharpness (c : ℝ) (hc : (2 / 9 : ℝ) < c) :
    ∃ C : Set Space, IsCompact C ∧ Convex ℝ C ∧ (positiveSlices C).ncard = 3 ∧
      0 < mixedArea C ∧ ∀ z : ℤ, ∀ x : Plane, ((z : ℝ), x) ∈ C →
        halfspaceDepth C ((z : ℝ), x) < c * mixedArea C := by
  obtain ⟨C, hC, hconvex, hthree, hpos, hsharp⟩ := mixed_integer_sharpness c hc
  refine ⟨C, hC, hconvex, hthree, hpos, ?_⟩
  intro z x hx
  obtain ⟨H, hproper, hp, hmass⟩ := hsharp z x hx
  exact (halfspaceDepth_le_mass C _ H hproper hp).trans_lt hmass

end ThreeSlices
