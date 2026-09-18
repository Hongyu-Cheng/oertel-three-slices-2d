---
fact_id: 5ef0bf9afb2503ba
kind: lemma
author: "mp_r166_opposite_shape_uniform"
assurance: LLM-verified
subgoal_id: opposite-scalar-datum-shape-uniform-excess
depends_on: ["73a2cf54a856ca90"]
source_packet_sha256: d9252a123292c990283ca090b9d4e170bfb751adf63522f825245550a1e93f31
verifier_run: 2b4031b310e94b29
target_match: null
---

## Statement

Fix the exact datum of accepted fact `73a2cf54a856ca90`, and let \(A_0,A_2\) be arbitrary compact convex polygons realizing all of its prescribed cell areas, full chords, and incidences.  Use
\[
(p_j,p_\ell)=(X,Y),\qquad p_k=100-X-Y
\]
on \(A_0\), and
\[
U=-q_k,\qquad V=q_\ell,\qquad q_j=U-V-102
\]
on \(A_2\).  Put \(B=(A_0+A_2)/2\), and for a midpoint put \(r_i=(p_i+q_i)/2\).  Then
\[
\left|B\cap\{r_j<0,\ r_k<0,\ r_\ell>0\}\right|
\ge \frac{9901}{7920000}
>\frac1{10^7}.
\]
In particular, the prescribed positive budget \(1/10^7\) of \(R_{jk}\) cannot fit for any actual endpoint completion of this datum.

## Proof

The fixed full chords give the three points
\[
A=\left(0,\frac{9901}{100}\right),\qquad
E=\left(\frac{9999}{100},0\right),\qquad
C=(100,0)
\]
in \(A_0\): \(A\) is the upper endpoint of the \(X=0\) chord, while \(E,C\) are the two endpoints of the \(Y=0\) chord.  Convexity puts the segment \([A,C]\) in \(A_0\).  The point
\[
D=\frac1{99}A+\frac{98}{99}C
=\left(\frac{9800}{99},\frac{9901}{9900}\right)
\]
therefore belongs to \(A_0\), and direct addition gives
\[
D_X+D_Y=\frac{9999}{100}.
\]
Consequently the triangle
\[
T=\operatorname{conv}\{E,C,D\}
\]
is contained in \(A_0\).  Every point \((X,Y)\) in the interior of \(T\) satisfies
\[
Y>0,\qquad X+Y>\frac{9999}{100},\qquad X\le100.
\]

The fixed \(V=0\) chord of \(A_2\) contains the endpoint
\[
(U,V)=\left(\frac1{100},0\right).
\]
In \((q_j,q_k,q_\ell)\)-coordinates this point is
\[
q^*=\left(-\frac{10199}{100},-\frac1{100},0\right).
\]
For every \((X,Y)\in\operatorname{int}T\), the midpoint of the corresponding \(A_0\)-point and \(q^*\) has
\[
2r_j=X-\frac{10199}{100}<0,
\]
\[
2r_k=100-X-Y-\frac1{100}
=\frac{9999}{100}-X-Y<0,
\]
and
\[
2r_\ell=Y>0.
\]
Thus
\[
\frac{\operatorname{int}T+q^*}{2}
\subseteq B\cap R_{jk}.
\]
The affine map on the left scales planar area by \(1/4\).  Since \(EC\) is a horizontal base of length \(1/100\) and \(D\) has height \(9901/9900\),
\[
|T|
=\frac12\cdot\frac1{100}\cdot\frac{9901}{9900}
=\frac{9901}{1980000}.
\]
Boundaries have zero planar area, so
\[
|B\cap R_{jk}|
\ge\frac14|T|
=\frac{9901}{7920000}.
\]
Finally,
\[
9901\cdot10000000=99010000000>7920000,
\]
which proves \(9901/7920000>1/10000000\) exactly.

## External sources

none
