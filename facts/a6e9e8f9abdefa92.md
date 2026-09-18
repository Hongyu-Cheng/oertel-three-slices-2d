---
fact_id: a6e9e8f9abdefa92
kind: counterexample
author: "mp_r39_cyclic_sufficiency"
assurance: LLM-verified
subgoal_id: canonical-all-double-cyclic-sufficiency
depends_on: ["2bb72698f0248a65","624b129b68e0fdee","8234d1112ec2f031","91cb5bfc71da49ac"]
source_packet_sha256: a8bf6f9f8e23f279883f8b80f7b653b029f04edfda86eef17f37dba1c3710ebe
verifier_run: 3660f40478eb4d8a
target_match: null
---

## Statement

Let \(N=\{1,2,3\}\), and use the scalar notation of accepted fact `2bb72698f0248a65`, the all-double excess of accepted fact `91cb5bfc71da49ac`, the crossing and tail conditions of accepted fact `624b129b68e0fdee`, and the three-cap inequalities of accepted fact `8234d1112ec2f031`.

Assign every unlisted cell mass zero and set
\[
p_\varnothing=\frac{119}{10},
\qquad
p_{\{1\}}=p_{\{2\}}=p_{\{3\}}=\frac15,
\]
\[
q_N=\frac25,
\qquad
q_{\{1,2\}}=q_{\{1,3\}}=q_{\{2,3\}}=\frac15,
\]
\[
r_{\{1\}}=r_{\{2\}}=r_{\{3\}}=2,
\qquad
r_{\{1,2\}}=r_{\{1,3\}}=r_{\{2,3\}}=1,
\qquad
r_N=0.
\]
Then all masses are nonnegative, the \(Q\)-support is exactly all-double, and
\[
M=\frac{25}{2},\qquad m=1,\qquad k=9.
\]
This calibration satisfies the three crossings, all canonical tail constraints, the three-cap product and square-root inequalities, the multiplicity-corrected inequality, and
\[
\left(\sum_{|G|=1}\sqrt{r_G}\right)^2\le 2k.
\]
Nevertheless,
\[
\sum_i u_i+m+q_N+\sum_{|G|=2}r_G+2r_N
=
\frac{2M-m-k}{3},
\]
so the required strict inequality fails.

## Proof

The totals are
\[
M=\frac{119}{10}+3\cdot\frac15=\frac{25}{2},
\qquad
m=\frac25+3\cdot\frac15=1,
\qquad
k=3\cdot2+3\cdot1=9,
\]
hence \(M\ge m>0\). For every \(i\),
\[
x_i=q_{N\setminus\{i\}}=\frac15,
\qquad
u_i=\frac15,
\qquad
v_i=m-x_i=\frac45,
\]
and
\[
c_i=2+1+1=4.
\]
Moreover,
\[
h=\frac{2(M+m+k)}9
=\frac{2(25/2+1+9)}9
=5.
\]
Thus every crossing holds:
\[
u_i+v_i+c_i=\frac15+\frac45+4=5=h.
\]
Every tail constraint holds at equality:
\[
c_i+m=4+1=5=h.
\]
The finite-interior scalar conditions also hold:
\[
0<u_i<M,\qquad 0<v_i<m,\qquad 0<h<M.
\]

The three-cap product inequality is strict:
\[
q_N^2m=\frac4{25}>\frac4{125}
=4x_1x_2x_3.
\]
The accompanying square-root inequality is also strict:
\[
\sum_i\sqrt{\frac{x_i}{m}}
=\frac3{\sqrt5}<\frac32.
\]

For the multiplicity-corrected inequality, its right side is
\[
k-r_N+\sum_{|G|=1}r_G=9+6=15.
\]
Its left side is
\[
\frac14\sum_i(\sqrt{p_\varnothing}+\sqrt{x_i})^2
=
\frac34\left(\sqrt{\frac{119}{10}}+\sqrt{\frac15}\right)^2
=
\frac{363+6\sqrt{238}}{40}.
\]
Since \(4\cdot238<79^2\), one has \(\sqrt{238}<79/2\), and therefore
\[
\frac{363+6\sqrt{238}}{40}
<
\frac{363+237}{40}
=15.
\]

The added cyclic singleton hypothesis holds at equality:
\[
\left(\sum_{|G|=1}\sqrt{r_G}\right)^2
=(3\sqrt2)^2
=18
=2k.
\]

Finally,
\[
\sum_i u_i+m+q_N+\sum_{|G|=2}r_G+2r_N
=
\frac35+1+\frac25+3
=5,
\]
whereas
\[
\frac{2M-m-k}{3}
=
\frac{25-1-9}{3}
=5.
\]
Thus every listed scalar hypothesis, including the cyclic singleton bound, is compatible with equality rather than strict all-double excess. This is only an exact scalar calibration; no common-plane or geometric realization is asserted.

## External sources

none
