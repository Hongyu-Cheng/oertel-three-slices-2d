---
fact_id: eae946d6c38eda2c
kind: lemma
author: "mp_r156_opposite_a0_completion"
assurance: LLM-verified
subgoal_id: opposite-scalar-survivor-a0-completion
depends_on: ["73a2cf54a856ca90"]
source_packet_sha256: 9d5d3d13acd1ce68b2cc27d32ff45adfd3036632a09fd91c902ee5314505b4a9
verifier_run: 52f6128e58854afa
target_match: null
---

## Statement

Use the datum of accepted fact `73a2cf54a856ca90`, so
\[
\Delta=1,\qquad \delta=w_0=100,\qquad
\theta=\frac{5099}{50},
\]
\[
(a,b,c,d)=
\left(\frac1{10^7},\frac{13577853}{10^6},
\frac{30001}{10^7},\frac1{10^7}\right),
\]
and
\[
J=H=K=\frac1{100},\qquad
\alpha=99,\qquad \beta=\frac{9999}{100},
\qquad \gamma=\tau=0.
\]
In the coordinates
\[
p_j=X,\qquad p_\ell=Y,\qquad p_k=100-X-Y,
\]
there exists a compact strictly convex rational polygon \(A_0\) whose only positive-area exact cells are
\[
\begin{array}{c|c}
P_j&X<0,\ Y>0,\ X+Y<100,\\
P_0&X>0,\ Y>0,\ X+Y<100,\\
P_\ell&X>0,\ Y<0,\ X+Y<100,\\
P_{k\ell}&X>0,\ Y<0,\ X+Y>100,
\end{array}
\]
with respective areas \(a,b,c,d\), whose three full cutting-line chords have exactly the displayed parameters and literal zero-branch incidences, and which satisfies
\[
P_0\subseteq
\left\{(X,Y):100X+\frac{5099}{50}Y\le10198\right\}.
\]

## Proof

Let \(A_0\) be the convex hull of the following vertices, listed clockwise:
\[
\begin{aligned}
v_1&=\left(-\frac1{50000},\frac{19801}{200}\right),&
v_2&=\left(0,\frac{9901}{100}\right),\\
v_3&=\left(50,\frac{2487832853}{50000000}\right),&
v_4&=(100,0),\\
v_5&=\left(\frac{10000501}{100000},-\frac{499}{100000}\right),&
v_6&=\left(\frac{10001}{100},-\frac1{100}\right),\\
v_7&=\left(\frac{5029699}{50000},-\frac{597}{1000}\right),&
v_8&=\left(\frac{9999}{100},0\right),\\
v_9&=(0,99).
\end{aligned}
\]
With indices read modulo \(9\), the consecutive edge cross-products
\[
(v_{i+1}-v_i)\mathbin{\times}(v_{i+2}-v_{i+1})
\]
are
\[
-\frac{627462667147}{2500000000000},\quad
-\frac{12582853}{500000},\quad
-\frac{1095740647}{5000000000000},
\]
\[
-\frac1{5000000},\quad
-\frac{16951}{5000000000},\quad
-\frac{29501}{5000000},
\]
\[
-\frac{9999}{100000},\quad
-\frac{49797}{100000},\quad
-\frac1{5000000}.
\]
They are all negative.  Hence the displayed order is strictly convex, so \(A_0\) is a compact two-dimensional convex polygon having exactly these vertices.

Direct rational clipping by \(X=0\), \(Y=0\), and \(X+Y=100\) gives
\[
A_0\cap\{X=0\}
=\operatorname{conv}\left\{v_9,v_2\right\}
=\left\{(0,Y):99\le Y\le\frac{9901}{100}\right\},
\]
\[
A_0\cap\{Y=0\}
=\operatorname{conv}\left\{v_8,v_4\right\}
=\left\{(X,0):\frac{9999}{100}\le X\le100\right\},
\]
and
\[
\begin{aligned}
A_0\cap\{X+Y=100\}
&=\operatorname{conv}\left\{v_4,v_6\right\}\\
&=\left\{(100+t,-t):0\le t\le\frac1{100}\right\}.
\end{aligned}
\]
Thus the full chords have
\[
J=H=K=\frac1{100},\quad
\alpha=99,\quad \beta=\frac{9999}{100},\quad \gamma=0.
\]
Moreover,
\[
\beta+H=100=\delta,\qquad \tau=\delta-\beta-H=0.
\]
The horizontal right endpoint and diagonal lower endpoint literally coincide at
\[
v_4=(\beta+H,0)=(\delta+\gamma,-\gamma)=(100,0).
\]
Also \(\alpha,\beta>0\), so \(\alpha=0\Longleftrightarrow\beta=0\), while
\(\gamma=0\Longleftrightarrow\tau=0\), and
\[
\chi=\delta-\alpha-J=\frac{99}{100}>0.
\]
These verify the literal \(A_0\) incidence conditions on the unperturbed branch \(\gamma=\tau=0\) and \(w_0=\delta\).

The four closed cell polygons obtained by exact clipping are, in cyclic order,
\[
\overline{P_j}=(v_9,v_1,v_2),
\]
\[
\overline{P_0}=(v_9,v_8,v_4,v_3,v_2),
\]
\[
\overline{P_\ell}=(v_8,v_7,v_6,v_4),
\qquad
\overline{P_{k\ell}}=(v_4,v_5,v_6).
\]
Their shoelace areas are respectively
\[
\frac1{10000000},\qquad
\frac{13577853}{1000000},\qquad
\frac{30001}{10000000},\qquad
\frac1{10000000}.
\]
Their sum is
\[
\frac{135808533}{10000000}=|A_0|.
\]
The four polygons have disjoint interiors and meet only along the three displayed cutting-line chords.  Since their areas sum to \(|A_0|\), every other exact cell has area zero.  As \(\Delta=1\), these coordinate areas are exactly the required physical areas \(a,b,c,d\).

Finally, write the dominance slack at \((X,Y)\) as
\[
\frac{5099}{50}\,100-100X-\frac{5099}{50}Y.
\]
On the five vertices
\[
(v_9,v_8,v_4,v_3,v_2)
\]
of \(\overline{P_0}\), its exact values are
\[
\frac{5099}{50},\qquad
199,\qquad
198,\qquad
\frac{309540282553}{2500000000},\qquad
\frac{504801}{5000}.
\]
Every value is positive.  Affineness of the slack and convexity of
\(\overline{P_0}\) therefore give
\[
P_0\subseteq
\left\{(X,Y):100X+\frac{5099}{50}Y
\le\frac{5099}{50}\,100\right\},
\]
which is the required pointwise dominance containment.

## External sources

none
