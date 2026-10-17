import ThreeSlices.Main
import ThreeSlices.Covering
import ThreeSlices.Tsintsifas

namespace ThreeSlices

/-- The planar covering lemma (Lemma 2). -/
theorem planar_covering : PlanarCoveringStatement :=
  planar_covering_of_tsintsifas normalized_tsintsifas

/-- The normalized three-body centerpoint theorem. -/
theorem centerpoint : CenterpointStatement :=
  centerpoint_of_covering planar_covering

end ThreeSlices
