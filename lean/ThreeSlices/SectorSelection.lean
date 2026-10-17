import ThreeSlices.Algebra

open scoped BigOperators

namespace ThreeSlices

/-- The numerical selection at the end of Lemma 2, with geometric sector areas as inputs. -/
theorem sector_selection (β : ℝ) (hβ : 0 < β) (σ τ : Fin 3 → ℝ)
    (hσ : ∀ i, 0 < σ i) (hτ : ∀ i, 0 ≤ τ i)
    (hbudget : ∑ i, (σ i + 2 * τ i) ≤ 3 * β)
    (hratio : (3 / 2 : ℝ) ≤ ∑ i, τ i / σ i) :
    ∃ i, σ i ^ 2 ≤ β * τ i := by
  by_contra h
  push Not at h
  let ρ : Fin 3 → ℝ := fun i => τ i / σ i
  have hρ : ∀ i, 0 ≤ ρ i := fun i => div_nonneg (hτ i) (hσ i).le
  have heq : ∀ i, ρ i * σ i = τ i := fun i => div_mul_cancel₀ _ (hσ i).ne'
  have hstrict : ∀ i, β * ρ i < σ i := by
    intro i
    apply (mul_lt_mul_iff_left₀ (hσ i)).mp
    calc
      β * ρ i * σ i = β * τ i := by rw [mul_assoc, heq]
      _ < σ i * σ i := by nlinarith [h i]
  have hterm : ∀ i, β * (ρ i + 2 * ρ i ^ 2) < σ i + 2 * τ i := by
    intro i
    have hp := mul_nonneg (hρ i) (sub_nonneg.mpr (hstrict i).le)
    rw [mul_sub, heq] at hp
    nlinarith [hstrict i]
  have hsum : β * (∑ i, (ρ i + 2 * ρ i ^ 2)) < ∑ i, (σ i + 2 * τ i) := by
    rw [Finset.mul_sum]
    exact Finset.sum_lt_sum (fun i _ => (hterm i).le) ⟨0, Finset.mem_univ _, hterm 0⟩
  have hcs : (3 / 4 : ℝ) ≤ ∑ i, ρ i ^ 2 := by
    change (3 / 2 : ℝ) ≤ ∑ i, ρ i at hratio
    rw [Fin.sum_univ_three] at hratio ⊢
    nlinarith [sq_nonneg (ρ 0 - ρ 1), sq_nonneg (ρ 1 - ρ 2),
      sq_nonneg (ρ 2 - ρ 0), hρ 0, hρ 1, hρ 2]
  have hlarge : 3 ≤ ∑ i, (ρ i + 2 * ρ i ^ 2) := by
    change (3 / 2 : ℝ) ≤ ∑ i, ρ i at hratio
    rw [Finset.sum_add_distrib, ← Finset.mul_sum]
    linarith
  have hm := mul_le_mul_of_nonneg_left hlarge hβ.le
  linarith

end ThreeSlices
