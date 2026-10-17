import Mathlib

open Set MeasureTheory
open scoped Pointwise

namespace ThreeSlices

abbrev Plane := EuclideanSpace ℝ (Fin 2)
abbrev Bodies := Fin 3 → Set Plane

noncomputable def area (A : Set Plane) : ℝ := volume.real A

def IsBody (A : Set Plane) : Prop := IsCompact A ∧ Convex ℝ A ∧ A.Nonempty

structure Halfspace where
  height : ℝ
  planar : Plane →L[ℝ] ℝ
  threshold : ℝ

def Halfspace.openCap (H : Halfspace) (i : Fin 3) : Set Plane :=
  {x | H.planar x < H.threshold - H.height * (i : ℝ)}

def Halfspace.closedCap (H : Halfspace) (i : Fin 3) : Set Plane :=
  {x | H.planar x ≤ H.threshold - H.height * (i : ℝ)}

noncomputable def openMass (A : Bodies) (H : Halfspace) : ℝ :=
  ∑ i, area (A i ∩ H.openCap i)

noncomputable def closedMass (A : Bodies) (H : Halfspace) : ℝ :=
  ∑ i, area (A i ∩ H.closedCap i)

noncomputable def totalArea (A : Bodies) : ℝ := ∑ i, area (A i)

def Compatible (A : Bodies) : Prop :=
  (1 / 2 : ℝ) • A 0 + (1 / 2 : ℝ) • A 2 ⊆ A 1

/-- The normalized statement of Theorem 1; zero-area bodies remain allowed. -/
def CenterpointStatement : Prop :=
  ∀ A : Bodies, (∀ i, IsBody (A i)) → totalArea A = 1 → Compatible A →
    ∃ i : Fin 3, ∃ x ∈ A i, ∀ H : Halfspace,
      x ∈ H.closedCap i → (2 / 9 : ℝ) ≤ closedMass A H

/-- The exact geometric assertion of Lemma 2. -/
def PlanarCoveringStatement : Prop :=
  ∀ (A : Set Plane), IsBody A → ∀ β : ℝ, 0 < β →
    ∀ (ι : Type) (_ : Fintype ι) (G : ι → Halfspace),
      (∀ j, (G j).planar ≠ 0) →
      A ⊆ ⋃ j, (G j).openCap 1 →
      (∀ j, area (A ∩ (G j).openCap 1) ≤ β) →
      ∃ r s : ι,
        area (A \ ((G r).openCap 1 ∪ (G s).openCap 1)) ^ 2 ≤
          β * area (A ∩ (G r).openCap 1 ∩ (G s).openCap 1)

lemma area_nonneg (A : Set Plane) : 0 ≤ area A := ENNReal.toReal_nonneg

lemma area_mono {A B : Set Plane} (h : A ⊆ B) (hB : IsCompact B) : area A ≤ area B :=
  measureReal_mono h (hB.measure_ne_top (μ := volume))

lemma Halfspace.isOpen_openCap (H : Halfspace) (i : Fin 3) : IsOpen (H.openCap i) :=
  isOpen_lt H.planar.continuous continuous_const

lemma closedMass_nonneg (A : Bodies) (H : Halfspace) : 0 ≤ closedMass A H :=
  Finset.sum_nonneg fun i _ => area_nonneg (A i ∩ H.closedCap i)

end ThreeSlices
