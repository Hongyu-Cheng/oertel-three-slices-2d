# Three-slice case of Oertel's conjecture

This repository contains the fact graph behind the paper

> H. Cheng and A. Basu, *A centerpoint theorem for three planar slices*, 2026.

The problem is stated in [`problem_statement.md`](problem_statement.md). It asks whether the three planar slices of a compact convex set in $\mathbb{Z}\times\mathbb{R}^2$ always contain a point such that every closed halfspace containing it captures at least 2/9 of the total area. The graph answers yes. The accepted final fact is [`0fee37ee73addcc3`](facts/0fee37ee73addcc3.md).

## How the graph was produced

The proof search ran in Codex, mainly with GPT-5.6 Sol and GPT-6 Astra, using a fact graph workflow similar to [Danus](https://arxiv.org/abs/2607.06447). A worker model proposes a candidate (a lemma, theorem, counterexample, or final proof) for a registered subgoal. A separate verifier model run reads the candidate together with the accepted facts it cites and returns `APPROVED` or `REJECTED`. Only approved candidates become facts, and a candidate may cite only accepted facts.

Every fact here carries the label `LLM-verified`. None of them has been reviewed by a human or checked formally. The proof in the paper, however, was distilled from this graph and verified by the authors, who take full responsibility for it.

## Size

| | count |
|---|---|
| accepted facts | 651 (532 lemmas, 42 theorems, 76 counterexamples, 1 final) |
| rejected candidates | 121 |
| registered subgoals | 567 (373 closed, 88 abandoned, 105 open, 1 legacy) |
| facts used by the final proof | 31, including the final fact |
| depth of the final fact | 12 |
| largest depth in the graph | 36 |

The depth of a fact is the length of the longest dependency chain below it. Most of the graph records directions that the final proof does not use, including counterexamples to intermediate conjectures.

## Files

- `facts/<id>.md` holds one accepted fact. The front matter gives its kind, the facts it depends on (`depends_on`), the subgoal it addresses, and the verifier run that approved it. The body has a statement and a proof.
- `candidates/<id>.json` holds every submitted candidate, accepted or rejected, as the worker wrote it.
- `verifications/<run>.json` holds every verifier verdict with its summary and, for rejections, the errors found.
- `state.json` is the ledger that ties these together: candidates, facts, runs, and subgoals with their status.

Prompts, handoff files, and the unverified working memory of the search are not included. Some run records in `state.json` still name those files.

Mathematics in these files is LaTeX source with `\(...\)` and `\[...\]` delimiters. GitHub's preview does not typeset it, so use the Raw view.

## The final proof

The final fact depends on the following facts. Reading them in this order gives the complete machine proof.

| depth | fact | kind | subgoal |
|---|---|---|---|
| 0 | [`1b4ea45680c75628`](facts/1b4ea45680c75628.md) | lemma | canonical-root-tail-concurrent-fan-crossing-inequality |
| 0 | [`2f9be517307232c7`](facts/2f9be517307232c7.md) | lemma | legacy-round-1 |
| 0 | [`400272f6de6c67bb`](facts/400272f6de6c67bb.md) | lemma | legacy-round-1 |
| 0 | [`640eff7c0417543d`](facts/640eff7c0417543d.md) | lemma | canonical-dominant-concurrent-fan-sector-inequality |
| 0 | [`8ad0785e5b4ae9ef`](facts/8ad0785e5b4ae9ef.md) | lemma | legacy-round-1 |
| 0 | [`a5309a9087686166`](facts/a5309a9087686166.md) | lemma | three-cover-geometric-strengthening |
| 0 | [`f4698a89f141eff4`](facts/f4698a89f141eff4.md) | lemma | r134-boundary-cap-algebra-certificate |
| 0 | [`f93a19566af88e9a`](facts/f93a19566af88e9a.md) | counterexample | canonical-root-tail-two-cap-allocation |
| 1 | [`8f5f00ddd4f22d2f`](facts/8f5f00ddd4f22d2f.md) | lemma | duality-reduction |
| 1 | [`9414163c0331b8f2`](facts/9414163c0331b8f2.md) | lemma | r134-natural-triangle-product-algebra |
| 1 | [`9fa81a67fd2eaafc`](facts/9fa81a67fd2eaafc.md) | lemma | balanced-middle-bridge |
| 1 | [`9fdf961ec71bd241`](facts/9fdf961ec71bd241.md) | lemma | canonical-root-tail-two-cap-allocation |
| 1 | [`ca6c285cd23ef4dc`](facts/ca6c285cd23ef4dc.md) | lemma | canonical-root-tail-two-cap-allocation |
| 1 | [`d7bdfc054d5093e8`](facts/d7bdfc054d5093e8.md) | lemma | legacy-round-1 |
| 2 | [`87035f4e1344144e`](facts/87035f4e1344144e.md) | theorem | middle-cover-coupling |
| 2 | [`fdfc3e7459f0e194`](facts/fdfc3e7459f0e194.md) | lemma | canonical-lifting-allocation |
| 3 | [`15bb2c1680a0254e`](facts/15bb2c1680a0254e.md) | lemma | residual-area-domain |
| 3 | [`c0b5fee36666b707`](facts/c0b5fee36666b707.md) | lemma | canonical-lifting-allocation |
| 3 | [`d2d117bcc58a1ba0`](facts/d2d117bcc58a1ba0.md) | lemma | global-middle-depth-region-helly |
| 4 | [`64760c76cadff481`](facts/64760c76cadff481.md) | lemma | triangle-barycentric-cover-equivalence |
| 4 | [`ab2620c83e116de2`](facts/ab2620c83e116de2.md) | lemma | canonical-lifting-allocation |
| 4 | [`e4a8e2c026dd7346`](facts/e4a8e2c026dd7346.md) | lemma | r129-three-cap-geometric-inequality |
| 5 | [`879a3c45b5f50670`](facts/879a3c45b5f50670.md) | lemma | canonical-lifting-allocation |
| 6 | [`6e68b44550cac3c8`](facts/6e68b44550cac3c8.md) | lemma | canonical-lifting-allocation |
| 7 | [`70dbfdc8fc4b6f51`](facts/70dbfdc8fc4b6f51.md) | lemma | canonical-root-tail-two-cap-allocation |
| 8 | [`2cf161fab8bf9e2b`](facts/2cf161fab8bf9e2b.md) | lemma | canonical-root-tail-two-cap-allocation |
| 9 | [`851e063a1b9908a3`](facts/851e063a1b9908a3.md) | theorem | canonical-dominant-concurrent-fan-sector-inequality |
| 10 | [`c4077ad10a0441a5`](facts/c4077ad10a0441a5.md) | lemma | r133-general-convex-cap-pair-inequality |
| 10 | [`cddd2c95c0ff12e3`](facts/cddd2c95c0ff12e3.md) | lemma | r133-triangle-sector-product-proof |
| 11 | [`30d5406c9459a845`](facts/30d5406c9459a845.md) | lemma | r134-planar-cap-pair-implies-three-slices |
| 12 | [`0fee37ee73addcc3`](facts/0fee37ee73addcc3.md) | final | r134-final-three-slice-centerpoint |
