# Third-party sources and notices

The standalone Grünbaum module and its LeanPool dependencies were copied from
`pengzhang91/Feige`, commit `19c61d6cb556d1e967dbb0ada9f293c290837867`.
The local port uses Lean 4.34.1 and mathlib
`d13f23b723b8a846827a245b89c10fc7d3f11612`.
`Grunbaum/ProbabilityCore.lean`, `Grunbaum/Main.lean`,
`Grunbaum/Sharpness.lean`, `Grunbaum/StrictBoundaryBridge.lean` and
`LeanPool/Isoperimetric/PrekopaLeindler.lean` contain marked API adaptations;
the mathematical assumptions and conclusions are preserved. Other imported
source files are unchanged.

The upstream notice below describes the original repository, including its
unmodified copy of LeanPool before this local port. All applicable copyright
and license notices are retained. The Apache 2.0 license is in `LICENSE`.

The `NOTICE` file of `Vilin97/lean-pool` at commit
`1bd76c49ce846f98a75d9a010799998666d168be` begins:

> Lean Pool
>
> Copyright the Lean Pool contributors and the respective project authors.

Its list of pooled projects records `LeanPool/Isoperimetric` as imported from
https://github.com/hojonathanho/isoperimetric, originally licensed under the
Apache License, Version 2.0.

## Upstream notice

```text
Feige's 1/e Conjecture in Lean
Copyright 2026 Guanyang Wang, Peng Zhang, and contributors

# Attribution and third-party notice

Individual source-file copyright notices are retained and take precedence
for those files.  In particular, the Grünbaum modules carrying an OpenAI
copyright header remain attributed to OpenAI, and the LeanPool files remain
attributed to Jonathan Ho.

The exact-calibration theorem and proof strategy formalized here are due to
Nikos Vlassis and Philip S. Thomas:

N. Vlassis and P. S. Thomas, "An Exact Distribution-Free Test for Means of
Nonnegative Random Variables", arXiv:2607.08415v1 (2026).

The centroid halfspace theorem formalized here is due to Branko Grünbaum:

B. Grünbaum, "Partitions of mass-distributions and of convex bodies by
hyperplanes", Pacific Journal of Mathematics 10 (1960), 1257--1261.

The files under `LeanPool/Isoperimetric/` are reproduced from
`Vilin97/lean-pool` commit
`1bd76c49ce846f98a75d9a010799998666d168be`.
Their Lean source is unchanged; the copied files differ only by
trailing-newline normalization.

They were authored by Jonathan Ho and are distributed under the Apache License
2.0. Their original copyright and license headers have been retained.

Source: https://github.com/Vilin97/lean-pool/tree/1bd76c49ce846f98a75d9a010799998666d168be/LeanPool/Isoperimetric
```
