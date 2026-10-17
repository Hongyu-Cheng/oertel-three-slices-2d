import Lake
open Lake DSL

package threeSlices

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "d13f23b723b8a846827a245b89c10fc7d3f11612"

lean_lib LeanPool

@[default_target] lean_lib Grunbaum

@[default_target] lean_lib ThreeSlices
