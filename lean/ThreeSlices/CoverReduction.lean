import ThreeSlices.HellyCover

open Set

namespace ThreeSlices

/-- A finite planar halfplane cover either has a pair covering the body, or contains
three distinct halfplanes covering the entire plane, while no pair covers the body. -/
theorem cover_pair_or_three {ι : Type} [Fintype ι]
    (A : Set Plane) (hA : Convex ℝ A) (hne : A.Nonempty) (G : ι → Halfspace)
    (hcover : A ⊆ ⋃ j, (G j).openCap 1) :
    (∃ r s, A ⊆ (G r).openCap 1 ∪ (G s).openCap 1) ∨
      ∃ r s t, r ≠ s ∧ r ≠ t ∧ s ≠ t ∧
        (G r).openCap 1 ∪ (G s).openCap 1 ∪ (G t).openCap 1 = univ ∧
        ∀ u v, ¬ A ⊆ (G u).openCap 1 ∪ (G v).openCap 1 := by
  classical
  by_cases hpair : ∃ r s, A ⊆ (G r).openCap 1 ∪ (G s).openCap 1
  · exact Or.inl hpair
  right
  have hno : ∀ r s, ¬ A ⊆ (G r).openCap 1 ∪ (G s).openCap 1 := by
    simpa only [not_exists] using hpair
  obtain ⟨x, hx⟩ := hne
  obtain ⟨r₀, _⟩ := mem_iUnion.mp (hcover hx)
  have hpairs : ∀ j k : Option ι,
      (A ∩ (coverConstraint A G j ∩ coverConstraint A G k)).Nonempty := by
    intro j k
    obtain ⟨x, hxA, hx⟩ := not_subset.mp (hno (j.getD r₀) (k.getD r₀))
    have hxj : x ∉ (G (j.getD r₀)).openCap 1 := fun h => hx (Or.inl h)
    have hxk : x ∉ (G (k.getD r₀)).openCap 1 := fun h => hx (Or.inr h)
    refine ⟨x, hxA, ?_, ?_⟩
    · cases j with
      | none => exact hxA
      | some r => exact hxj
    · cases k with
      | none => exact hxA
      | some s => exact hxk
  obtain ⟨T, hcard, hempty⟩ := cover_helly_witness A hA G hcover
  have hthree : T.card = 3 := by
    by_contra h
    have hsmall : T.card ≤ 2 := by omega
    interval_cases hsize : T.card
    · have : T = ∅ := Finset.card_eq_zero.mp hsize
      simp [this] at hempty
    · obtain ⟨j, rfl⟩ := Finset.card_eq_one.mp hsize
      obtain ⟨x, _, hxj, _⟩ := hpairs j j
      have : x ∈ (⋂ k ∈ ({j} : Finset (Option ι)), coverConstraint A G k) := by
        simpa using hxj
      rw [hempty] at this
      exact this
    · obtain ⟨j, k, _, rfl⟩ := Finset.card_eq_two.mp hsize
      obtain ⟨x, _, hxj, hxk⟩ := hpairs j k
      have : x ∈ (⋂ l ∈ ({j, k} : Finset (Option ι)), coverConstraint A G l) := by
        simpa using And.intro hxj hxk
      rw [hempty] at this
      exact this
  obtain ⟨j, k, l, hjk, hjl, hkl, rfl⟩ := Finset.card_eq_three.mp hthree
  have hn : j ≠ none ∧ k ≠ none ∧ l ≠ none := by
    refine ⟨?_, ?_, ?_⟩
    · rintro rfl
      obtain ⟨x, hxA, hxk, hxl⟩ := hpairs k l
      have : x ∈ (⋂ q ∈ ({none, k, l} : Finset (Option ι)), coverConstraint A G q) := by
        simpa [coverConstraint] using And.intro hxA (And.intro hxk hxl)
      rw [hempty] at this
      exact this
    · rintro rfl
      obtain ⟨x, hxA, hxj, hxl⟩ := hpairs j l
      have : x ∈ (⋂ q ∈ ({j, none, l} : Finset (Option ι)), coverConstraint A G q) := by
        simpa [coverConstraint] using And.intro hxj (And.intro hxA hxl)
      rw [hempty] at this
      exact this
    · rintro rfl
      obtain ⟨x, hxA, hxj, hxk⟩ := hpairs j k
      have : x ∈ (⋂ q ∈ ({j, k, none} : Finset (Option ι)), coverConstraint A G q) := by
        simpa [coverConstraint] using And.intro hxj (And.intro hxk hxA)
      rw [hempty] at this
      exact this
  cases j with
  | none => exact False.elim (hn.1 rfl)
  | some r =>
    cases k with
    | none => exact False.elim (hn.2.1 rfl)
    | some s =>
      cases l with
      | none => exact False.elim (hn.2.2 rfl)
      | some t =>
        refine ⟨r, s, t, ?_, ?_, ?_, ?_, hno⟩
        · simpa using hjk
        · simpa using hjl
        · simpa using hkl
        · ext x
          simp only [mem_union, mem_univ, iff_true]
          by_contra hx
          have : x ∈ (⋂ q ∈ ({some r, some s, some t} : Finset (Option ι)),
              coverConstraint A G q) := by
            simpa [coverConstraint, and_assoc] using hx
          rw [hempty] at this
          exact this

/-- A pair covering the body leaves zero uncovered area, including degenerate bodies. -/
lemma uncovered_area_zero_of_pair_cover (A : Set Plane) (H K : Halfspace)
    (hcover : A ⊆ H.openCap 1 ∪ K.openCap 1) :
    area (A \ (H.openCap 1 ∪ K.openCap 1)) = 0 := by
  simp [sdiff_eq_empty.mpr hcover, area]

/-- The area-zero branch of Lemma 2 needs only a nonnegative value of β. -/
lemma pair_cover_bound_of_area_zero (A : Set Plane) (H K : Halfspace) (β : ℝ)
    (hβ : 0 ≤ β) (hz : area (A \ (H.openCap 1 ∪ K.openCap 1)) = 0) :
    area (A \ (H.openCap 1 ∪ K.openCap 1)) ^ 2 ≤
      β * area (A ∩ H.openCap 1 ∩ K.openCap 1) := by
  rw [hz, zero_pow (by decide : 2 ≠ 0)]
  exact mul_nonneg hβ (area_nonneg _)

/-- The reduction used in Lemma 2: outside the area-zero pair case, the three original
halfplanes cover the plane and every pair leaves a portion of the body of positive area. -/
theorem cover_zero_area_pair_or_three {ι : Type} [Fintype ι]
    (A : Set Plane) (hA : Convex ℝ A) (hne : A.Nonempty) (G : ι → Halfspace)
    (hcover : A ⊆ ⋃ j, (G j).openCap 1) :
    (∃ r s, area (A \ ((G r).openCap 1 ∪ (G s).openCap 1)) = 0) ∨
      ∃ r s t, r ≠ s ∧ r ≠ t ∧ s ≠ t ∧
        (G r).openCap 1 ∪ (G s).openCap 1 ∪ (G t).openCap 1 = univ ∧
        ∀ u v, 0 < area (A \ ((G u).openCap 1 ∪ (G v).openCap 1)) := by
  classical
  by_cases hz : ∃ r s, area (A \ ((G r).openCap 1 ∪ (G s).openCap 1)) = 0
  · exact Or.inl hz
  right
  rcases cover_pair_or_three A hA hne G hcover with ⟨r, s, hrs⟩ |
    ⟨r, s, t, hrs, hrt, hst, huniv, _⟩
  · exact False.elim (hz ⟨r, s, uncovered_area_zero_of_pair_cover A (G r) (G s) hrs⟩)
  · refine ⟨r, s, t, hrs, hrt, hst, huniv, fun u v => ?_⟩
    exact lt_of_le_of_ne (area_nonneg _) (fun h => hz ⟨u, v, h.symm⟩)

end ThreeSlices
