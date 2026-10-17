# Formalization map

This document relates the Lean declarations to [arXiv:2609.32953v1](https://arxiv.org/abs/2609.32953v1). The manuscript is `three_slice_manuscript.tex` in the [v1 source archive](https://arxiv.org/src/2609.32953v1). All declarations below are available through `import ThreeSlices`.

## Results

| Paper result | Lean declaration | Statement |
| --- | --- | --- |
| Theorem 1, three planar bodies | `paper_centerpoint` | A nonempty compact convex triple with total area one and the midpoint inclusion has a point in its slice union of depth at least $2/9$. |
| Relative bound in the abstract and conclusion | `paper_centerpoint_unnormalized` | The same bound is $2/9$ times total area, including when total area is zero. |
| Theorem 1, mixed-integer sets | `paper_mixed_integer_centerpoint` | A compact convex subset of `Space` with exactly three positive-area integer slices has a mixed-integer point of depth at least $2/9$ times its mixed-integer mass. |
| Lemma 2 | `planar_covering` | For a finite open-halfplane cover of a nonempty compact convex planar set, with each cap of area at most a positive bound, two caps have squared uncovered area at most that bound times their overlap area. The two indices may coincide. |
| Tsintsifas inequality used in Lemma 2 | `normalized_tsintsifas` | The six-sector area-ratio sum is at least $3/2$ for the normalized three-line configuration, with the origin in the interior of the body and both fan parameters positive. |
| Three-slice optimality | `paper_sharpness` | For every constant greater than $2/9$, there is a compatible triple of total area one whose depth is strictly below that constant at every point in its slice union. |
| Mixed-integer optimality | `paper_mixed_integer_sharpness` | For every constant greater than $2/9$, there is a compact convex set with exactly three positive-area integer slices and positive mixed-integer mass whose depth at every mixed-integer point is strictly below that constant times its mass. |

The five `paper_*` declarations are in [Paper.lean](ThreeSlices/Paper.lean). [Theorem.lean](ThreeSlices/Theorem.lean) assembles Lemma 2, the normalized Tsintsifas inequality and the centerpoint theorem.

## Definitions and assumptions

The base definitions are in [Basic.lean](ThreeSlices/Basic.lean), integer-slice and mass definitions in [MixedIntegerBasic.lean](ThreeSlices/MixedIntegerBasic.lean), and `sliceUnion` in [ConvexHullSlices.lean](ThreeSlices/ConvexHullSlices.lean).

`Plane` is `EuclideanSpace ℝ (Fin 2)`, and `Space` is `ℝ × Plane`. A triple is placed at heights $0$, $1$ and $2$. `IsBody` means nonempty, compact and convex; it allows points, segments and other zero-area bodies. `Compatible` is exactly the inclusion of the midpoint Minkowski sum of the two outer bodies in the middle body.

`totalArea` is the sum of the three planar areas. `mixedVolume` sums planar slice volumes over all integer heights, and `mixedArea` is its real-valued form. The compactness assumptions in the paper-facing results ensure finite mass. Exactly three *positive-area* integer slices are required in the mixed-integer theorem; other nonempty zero-area slices are allowed. The three integer heights with positive-area slices are proved consecutive from convexity.

`Halfspace.Proper` is equivalent to a nonzero full linear normal. `halfspaceDepth` is the infimum of mixed-integer masses over all such closed halfspaces containing the point. `halfspaceMasses_eq_functionals` in [Paper.lean](ThreeSlices/Paper.lean) identifies this family with all nonzero continuous linear normals, including horizontal halfspaces. [HalfspaceGeometry.lean](ThreeSlices/HalfspaceGeometry.lean) and [SliceUnionMass.lean](ThreeSlices/SliceUnionMass.lean) establish the halfspace representation and slice-union mass identities.

## Auxiliary results and scope

The independent [Grünbaum library](Grunbaum.lean) proves the sharp centroid halfspace bound in every positive dimension, simplex sharpness and the open/closed-boundary identity. Its body type requires nonempty interior, which the planar application derives from positive area. In [Sharpness.lean](ThreeSlices/Sharpness.lean), `sharpCentroid_eq_planarCentroid` identifies the homothety center $(1/3, 1/3)$ with the volume centroid of `standardChordTriangle`. The mixed-integer construction uses the convex hull of the prescribed slices; `sharpHull_integer_inter` identifies all its integer sections.

The Tsintsifas interface is the normalized configuration needed for Lemma 2, rather than a separate theorem for arbitrary three concurrent lines. Its source is G. Tsintsifas, *Two inequalities for planar convex sets*, Canadian Mathematical Bulletin 28 (1985), 60–66, [DOI:10.4153/CMB-1985-005-5](https://doi.org/10.4153/CMB-1985-005-5).

The sharpness proofs establish optimality for every $c > 2/9$ by choosing a suitable homothety factor. They do not separately state the manuscript's full epsilon-parameterized family or its $2/9 + 7\varepsilon/9$ estimate. The cited background results in the introduction are outside this formalization.
