import ThreeSlices
import Grunbaum

open Lean Elab Command in
/-- Print the statement and transitive axiom dependencies, rejecting nonstandard axioms. -/
elab "#assert_standard_axioms " id:ident : command => do
  let c ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
  let bad := (← collectAxioms c).filter (· ∉ [``propext, ``Classical.choice, ``Quot.sound])
  unless bad.isEmpty do throwErrorAt id "{c} depends on nonstandard axioms {bad}"
  elabCommand (← `(#check $id))
  elabCommand (← `(#print axioms $id))

#assert_standard_axioms ThreeSlices.paper_centerpoint
#assert_standard_axioms ThreeSlices.paper_centerpoint_unnormalized
#assert_standard_axioms ThreeSlices.paper_mixed_integer_centerpoint
#assert_standard_axioms ThreeSlices.paper_sharpness
#assert_standard_axioms ThreeSlices.paper_mixed_integer_sharpness
#assert_standard_axioms ThreeSlices.planar_covering
#assert_standard_axioms ThreeSlices.normalized_tsintsifas
#assert_standard_axioms ThreeSlices.halfspaceMasses_eq_functionals
#assert_standard_axioms ThreeSlices.mixedArea_sliceUnion
#assert_standard_axioms ThreeSlices.sharpCentroid_eq_planarCentroid
#assert_standard_axioms Grunbaum.grunbaum_centroid_halfspace
#assert_standard_axioms Grunbaum.universalCentroidHalfspaceLowerBound_le_grunbaumConstant
#assert_standard_axioms Grunbaum.volume_inter_le_eq_volume_inter_lt

#print ThreeSlices.Halfspace.Proper
#print ThreeSlices.halfspaceMasses
#print ThreeSlices.halfspaceDepth
#print ThreeSlices.PlanarCoveringStatement
#print ThreeSlices.NormalizedTsintsifasStatement
#print ThreeSlices.mixedVolume
#print ThreeSlices.mixedArea

section ZeroTotalArea
open Set MeasureTheory ThreeSlices

/-- The unnormalized paper interface applies even when all three bodies are singletons. -/
example : ∃ p ∈ sliceUnion (fun _ => ({0} : Set Plane)),
    (0 : ℝ) ≤ halfspaceDepth (sliceUnion (fun _ => ({0} : Set Plane))) p := by
  have hA : ∀ _ : Fin 3, IsBody ({0} : Set Plane) :=
    fun _ => ⟨isCompact_singleton, convex_singleton 0, singleton_nonempty 0⟩
  have hcomp : Compatible (fun _ => ({0} : Set Plane)) := by simp [Compatible]
  simpa [totalArea, area, Measure.real] using
    paper_centerpoint_unnormalized (fun _ => ({0} : Set Plane)) hA hcomp

end ZeroTotalArea
