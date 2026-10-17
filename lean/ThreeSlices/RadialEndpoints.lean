import ThreeSlices.Basic

open Set

namespace ThreeSlices

/-- A nonzero ray from an interior origin has a positive maximal scalar in the body. -/
theorem exists_radial_endpoint {K : Set Plane} (hK : IsBody K)
    (hzero : (0 : Plane) ∈ interior K) {v : Plane} (hv : v ≠ 0) :
    ∃ t : ℝ, 0 < t ∧ t • v ∈ K ∧ ∀ s : ℝ, s • v ∈ K → s ≤ t := by
  have hcont : Continuous (fun s : ℝ => s • v) := continuous_id.smul continuous_const
  have hopen : IsOpen ((fun s : ℝ => s • v) ⁻¹' interior K) :=
    isOpen_interior.preimage hcont
  have hzero' : (0 : ℝ) ∈ (fun s : ℝ => s • v) ⁻¹' interior K := by
    simpa using hzero
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hopen 0 hzero'
  have hhalf : (ε / 2) • v ∈ K := by
    apply interior_subset
    apply hball
    simp only [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs,
      abs_of_pos (by linarith : 0 < ε / 2)]
    linarith
  have hcompact : IsCompact ((fun s : ℝ => s • v) ⁻¹' K) :=
    (isClosedEmbedding_smul_left (𝕜 := ℝ) hv).isCompact_preimage hK.1
  obtain ⟨t, ht, hmax⟩ := hcompact.exists_isGreatest ⟨ε / 2, hhalf⟩
  refine ⟨t, ?_, ht, fun s hs => hmax hs⟩
  have := hmax hhalf
  linarith

end ThreeSlices
