---
fact_id: ebc88d35821abdcb
kind: lemma
author: "mp_r354_cyclic_residual_realizer"
assurance: LLM-verified
subgoal_id: triangle-cyclic-residual-geometric-realizability
depends_on: ["2f9be517307232c7","64760c76cadff481"]
source_packet_sha256: 5d6c10f5e8f5894c78edd66ce283faa3d298800c58ff55d277d42aeb9c2234f3
verifier_run: 3ff4647a8a9a41d9
target_match: null
---

## Statement

Assume the exact triangular \(N=3\) barycentric system of accepted fact
`64760c76cadff481` in the surviving orientation.  Thus
\[
A=|\det U|\le B=|\det V|,\qquad
t=\frac{2(1+A+B)}9,
\]
the residual parameters
\[
r=\frac AB,\qquad S=\frac1B
\]
satisfy
\[
0<r<\frac{27-2\sqrt{26}}{25},
\qquad L_0(r)<S<U_0(r),
\]
and, for some \(\varepsilon>0\),
\[
R=\varepsilon L,\qquad \tau=\varepsilon\sigma,\qquad
\mathbf1^\top R=\varepsilon\mathbf1^\top,\qquad
\sum_{i=1}^3\tau_i>\varepsilon.
\tag{1}
\]
The literal row masses are
\[
M_i=
\mathcal C(R_{i*};0)
+A\mathcal C((RU)_{i*};-\tau_i)
+B\mathcal C((RV)_{i*};\tau_i).
\tag{2}
\]

Suppose that, up to a row permutation, a common column permutation, and
positive scaling, \(R\) has the cyclic form
\[
\begin{pmatrix}
p&-a&-b\\
-b&p&-a\\
-a&-b&p
\end{pmatrix},
\qquad p,a,b>0,\qquad p>a+b.
\tag{3}
\]
Then
\[
\boxed{\quad
\max_{1\le i\le3}(M_i-t)
>
\frac{2(1+A-B)}9
>0.
\quad}
\tag{4}
\]
Consequently no real or rational strict realization of all three
inequalities \(M_i<t\) exists anywhere in the chamber (3).  In particular,
the low-\(S\), low-endpoint-ratio scalar calibration
\[
p=65,\qquad a=b=32,\qquad
A=\frac{441}{4000},\qquad B=\frac{441}{400}
\]
is geometrically impossible.

## Proof

We first extract the strict area inequality needed at the end.  The lower
residual boundary in accepted fact `64760c76cadff481` is
\[
L_0(r)=
\begin{cases}
1-r,&0<r\le9/25,\\[1mm]
(3r+2\sqrt r-1)/2,&r>9/25.
\end{cases}
\tag{5}
\]
For \(r>9/25\),
\[
L_0(r)-(1-r)
=\frac{5r+2\sqrt r-3}{2}>0,
\tag{6}
\]
because the numerator vanishes at \(r=9/25\) and is strictly increasing
for \(r>0\).  Hence in both branches
\[
S>L_0(r)\ge1-r.
\]
Substituting \(S=1/B\) and \(r=A/B\), and multiplying by \(B>0\), gives
\[
B<1+A.
\tag{7}
\]

For the small endpoint triangle \(A_0=U\Delta\), define the three literal
closed caps
\[
X_i=A_0\cap\{z:R_{i*}z\ge-\tau_i\},
\qquad
x_i=|X_i|
=A\mathcal C((RU)_{i*};-\tau_i).
\tag{8}
\]
These three halfplanes cover not merely \(A_0\), but the entire affine
plane
\[
\mathcal A=\{z\in\mathbb R^3:\mathbf1^\top z=1\}.
\tag{9}
\]
Indeed, if \(z\in\mathcal A\) were outside all three closed halfplanes,
then
\[
R_{i*}z<-\tau_i\qquad(i=1,2,3).
\]
Summing and using (1) would give
\[
\varepsilon
=\mathbf1^\top Rz
<-\sum_i\tau_i
<-\varepsilon,
\tag{10}
\]
which is impossible since \(\varepsilon>0\).  The strict inequalities in
(10) are exactly the complements of the closed caps, so this argument
also audits every boundary point.

Let \(g_0\) be the planar centroid of \(A_0\).  By (9), \(g_0\) belongs to
at least one of the three closed halfplanes, say the one indexed by
\(i_0\).  The planar Grünbaum inequality recorded in accepted fact
`2f9be517307232c7` applies to every closed halfplane containing the centroid
of a planar convex body.  It therefore gives
\[
x_{i_0}\ge\frac49 A.
\tag{11}
\]
There is no constant-functional exception hidden here.  Under (3), every
row of \(R\) has, up to positive scale and entry permutation, the three
values \(p,-a,-b\), which are not all equal.  Even if one allowed a whole
affine plane as a degenerate halfplane, its cap would have area \(A\), and
(11) would remain true.

It remains to combine the cap in (11) with the middle cap in the same row.
Every row in (3) is a permutation and positive multiple of
\((p,-a,-b)\).  Positive scaling and entry permutation do not change its
zero cap.  The complete cap formula of accepted fact
`64760c76cadff481` gives
\[
\mathcal C(R_{i*};0)
=c:=\frac{p^2}{(p+a)(p+b)}
\qquad(i=1,2,3).
\tag{12}
\]
Put \(d=p-a-b>0\).  The exact identity
\[
9p^2-4(p+a)(p+b)
=(a-b)^2+6d(a+b)+5d^2
>0
\tag{13}
\]
shows that
\[
c>\frac49.
\tag{14}
\]

The large-end contribution in (2) is nonnegative.  Equations
(11)--(14) therefore imply, for the same index \(i_0\),
\[
M_{i_0}
\ge c+x_{i_0}
>\frac49+\frac{4A}{9}
=\frac{4(1+A)}9.
\tag{15}
\]
Using (7),
\[
\frac{4(1+A)}9-t
=\frac{2(1+A-B)}9
>0.
\tag{16}
\]
Equations (15)--(16) prove (4).

Row permutations only change the index \(i_0\); a common column
permutation only permutes the three vertex values in every middle cap; and
positive scaling leaves every zero cap unchanged.  The plane-cover
calculation (10) uses only the invariant column-sum and height-sum
conditions in (1).  Thus the proof covers every permutation and scaling
orbit in (3), all determinant signs of \(U,V\), all exact midpoint-compatible
endpoint shapes, all independent height levels, and all open/closed support
boundaries.

For the displayed calibration, \(r=1/10\) and \(S=400/441\), so (7) holds
strictly and the explicit lower bound on the gap in (4) is
\[
\frac{2(1+A-B)}9=\frac{31}{18000}>0.
\]
The preceding argument applies without any further scalar or geometric
feasibility assumption.  Hence scalar cap-budget feasibility at that point
cannot lift to a full endpoint-matrix realization.

## External sources

Branko Grünbaum, “Partitions of mass-distributions and of convex bodies by
hyperplanes,” Pacific Journal of Mathematics 10 (1960), no. 4, 1257--1261,
Theorem 2,
https://msp.org/pjm/1960/10-4/pjm-v10-n4-p18-p.pdf.
In dimension two, the theorem says that every closed halfplane containing
the centroid of a planar convex body has area at least
\((2/3)^2=4/9\) of the body's area.  This is exactly the version already
sourced and checked in accepted fact `2f9be517307232c7`; it applies to the
nondegenerate compact triangle \(A_0=U\Delta\) in (8).
