import ThreeSlices.Basic

open Set MeasureTheory

namespace ThreeSlices

lemma area_inter_open_pos {A U : Set Plane} (hA : IsCompact A) (hU : IsOpen U)
    (hne : (interior A ∩ U).Nonempty) : 0 < area (A ∩ U) := by
  have hp : 0 < volume (interior A ∩ U) :=
    (isOpen_interior.inter hU).measure_pos volume hne
  have hm : 0 < volume (A ∩ U) := hp.trans_le
    (measure_mono (inter_subset_inter_left U interior_subset))
  exact ENNReal.toReal_pos hm.ne'
    (measure_ne_top_of_subset inter_subset_left (hA.measure_ne_top (μ := volume)))

lemma interior_inter_cone_nonempty {A U : Set Plane} (h0 : (0 : Plane) ∈ interior A)
    (hscale : ∀ t : ℝ, 0 < t → ∀ x ∈ U, t • x ∈ U) (hne : U.Nonempty) :
    (interior A ∩ U).Nonempty := by
  obtain ⟨x, hx⟩ := hne
  have hc : Continuous (fun t : ℝ => t • x) := continuous_id.smul continuous_const
  have hn : {t : ℝ | t • x ∈ interior A} ∈ nhds 0 := by
    exact hc.continuousAt.preimage_mem_nhds (by simpa using isOpen_interior.mem_nhds h0)
  obtain ⟨ε, hε, hb⟩ := Metric.mem_nhds_iff.mp hn
  have ht : ε / 2 ∈ Metric.ball (0 : ℝ) ε := by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos (by positivity : 0 < ε / 2)]
    linarith
  exact ⟨(ε / 2) • x, hb ht, hscale (ε / 2) (by positivity) x hx⟩

lemma area_inter_strict_linear_sector_pos {A : Set Plane} (hA : IsCompact A)
    (h0 : (0 : Plane) ∈ interior A) (f g : Plane →L[ℝ] ℝ)
    {v : Plane} (hf : 0 < f v) (hg : 0 < g v) :
    0 < area (A ∩ {x | 0 < f x ∧ 0 < g x}) := by
  apply area_inter_open_pos hA
    ((isOpen_lt continuous_const f.continuous).inter
      (isOpen_lt continuous_const g.continuous))
  apply interior_inter_cone_nonempty (U := {x | 0 < f x ∧ 0 < g x}) h0 _ ⟨v, hf, hg⟩
  intro t ht x hx
  exact ⟨by simpa using mul_pos ht hx.1, by simpa using mul_pos ht hx.2⟩

theorem normalized_strict_sector_areas_pos {A : Set Plane} (hA : IsCompact A)
    (h0 : (0 : Plane) ∈ interior A) {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    0 < area (A ∩ {x | x 0 < 0 ∧ x 1 < 0}) ∧
    0 < area (A ∩ {x | 0 < x 0 ∧ 0 < x 1}) ∧
    0 < area (A ∩ {x | 0 < x 0 ∧ a * x 0 + b * x 1 < 0}) ∧
    0 < area (A ∩ {x | 0 < x 1 ∧ a * x 0 + b * x 1 < 0}) ∧
    0 < area (A ∩ {x | x 0 < 0 ∧ 0 < a * x 0 + b * x 1}) ∧
    0 < area (A ∩ {x | x 1 < 0 ∧ 0 < a * x 0 + b * x 1}) := by
  let p : Plane →L[ℝ] ℝ := EuclideanSpace.proj 0
  let q : Plane →L[ℝ] ℝ := EuclideanSpace.proj 1
  let s : Plane →L[ℝ] ℝ := a • p + b • q
  have hab : 0 < a * b := mul_pos ha hb
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [p, q, neg_pos] using area_inter_strict_linear_sector_pos hA h0 (-p) (-q)
      (v := WithLp.toLp 2 ![-1, -1]) (by norm_num [p]) (by norm_num [q])
  · simpa [p, q] using area_inter_strict_linear_sector_pos hA h0 p q
      (v := WithLp.toLp 2 ![1, 1]) (by norm_num [p]) (by norm_num [q])
  · simpa only [p, q, s, neg_apply, add_apply, smul_apply,
      EuclideanSpace.coe_proj, smul_eq_mul, neg_pos] using
      area_inter_strict_linear_sector_pos hA h0 p (-s)
      (v := WithLp.toLp 2 ![b, -2 * a]) (by simpa [p] using hb)
      (by simp [s, p, q]; nlinarith)
  · simpa only [p, q, s, neg_apply, add_apply, smul_apply,
      EuclideanSpace.coe_proj, smul_eq_mul, neg_pos] using
      area_inter_strict_linear_sector_pos hA h0 q (-s)
      (v := WithLp.toLp 2 ![-2 * b, a]) (by simpa [q] using ha)
      (by simp [s, p, q]; nlinarith)
  · simpa only [p, q, s, neg_apply, add_apply, smul_apply,
      EuclideanSpace.coe_proj, smul_eq_mul, neg_pos] using
      area_inter_strict_linear_sector_pos hA h0 (-p) s
      (v := WithLp.toLp 2 ![-b, 2 * a]) (by simpa [p] using hb)
      (by simp [s, p, q]; nlinarith)
  · simpa only [p, q, s, neg_apply, add_apply, smul_apply,
      EuclideanSpace.coe_proj, smul_eq_mul, neg_pos] using
      area_inter_strict_linear_sector_pos hA h0 (-q) s
      (v := WithLp.toLp 2 ![2 * b, -a]) (by simpa [q] using ha)
      (by simp [s, p, q]; nlinarith)

end ThreeSlices
