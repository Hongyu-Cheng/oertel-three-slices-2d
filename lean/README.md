# Three-slice centerpoint formalization

This package formalizes both assertions of Theorem 1, Lemma 2, and the optimality of $2/9$ in both settings from *A Centerpoint Theorem for Three Planar Convex Bodies* ([arXiv:2609.32953v1](https://arxiv.org/abs/2609.32953v1)). The [formalization map](FORMALIZATION.md) gives the corresponding declarations, assumptions and scope.

## Build and verify

Install [elan](https://github.com/leanprover/elan), then run from this directory. Elan selects [lean-toolchain](lean-toolchain); Lake locks dependency revisions in [lake-manifest.json](lake-manifest.json).

```sh
lake exe cache get
lake build
lake env lean Check.lean
```

The first command downloads prebuilt mathlib files. Dependencies and build outputs stay in `.lake/`, which Git ignores.

[Check.lean](Check.lean) prints the main results, the mass and depth definitions, and transitive axiom dependencies. It fails if a checked result uses an axiom beyond `propext`, `Classical.choice` and `Quot.sound`. The [GitHub workflow](../.github/workflows/lean.yml) runs the build and this check.

## Use

```lean
import ThreeSlices
```

The five paper-facing `paper_*` theorems are in [ThreeSlices/Paper.lean](ThreeSlices/Paper.lean). The independent Grünbaum library has its own entry point, [Grunbaum.lean](Grunbaum.lean).

## Sources and license

[GRUNBAUM_NOTICE.md](GRUNBAUM_NOTICE.md) records upstream sources, compatibility adaptations and third-party attribution.

The Lean package is released under [Apache 2.0](LICENSE). This license covers the code under `lean/`, including the vendored sources with their retained notices; it does not cover the fact graph outside this directory.
