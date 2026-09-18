---
fact_id: 009a0ffca7cbccd8
kind: lemma
author: "mp_r4_adaptive_segment"
assurance: LLM-verified
subgoal_id: adaptive-centroid-segment
depends_on: ["400272f6de6c67bb","9fa81a67fd2eaafc","e480e624b1618fae"]
source_packet_sha256: 85e3d516a96aef387ac1a0279e627e1ddc4fa782dacbda3e07b2e7ebb031924d
verifier_run: be30e88819cf4e38
target_match: null
---

## Statement

Under the balanced compatible hypotheses, let \(c_i\) be the centroid of \(A_i\), and define
\[
z_0=\frac{c_0+c_2}{2},\qquad
\delta=c_1-z_0,\qquad
D=\|\delta\|,\qquad
z_t=z_0+t\delta.
\]
For \(i=0,1,2\), let
\[
r_i=\max\{r\ge0:c_i+r\overline B_2\subseteq A_i\}>0,
\qquad
r_*=\min\{r_0,r_2\},
\qquad
m=\min\{a_0,a_2\},
\]
and write \(s_+=\max\{s,0\}\). Then every \(t\in[0,1]\) satisfies
\[
h_S((1,z_t))
\ge
\min\left\{
T-a_0,\,
T-a_2,\,
\frac49\left[
a_1\left(1-\frac{(1-t)D}{r_1}\right)_+^2
+
m\left(1-\frac{tD}{r_*}\right)_+^2
\right]
\right\}.
\tag{1}
\]
In particular, the explicit choice \(t=1/2\) gives
\[
h_S((1,z_{1/2}))\ge\frac{2T}{9}
\]
whenever
\[
a_1\left(1-\frac{D}{2r_1}\right)_+^2
+
m\left(1-\frac{D}{2r_*}\right)_+^2
\ge\frac T2.
\tag{2}
\]
The region certified by (2) is nonempty and contains compatible balanced triples for which neither component of the earlier bound in `e480e624b1618fae` reaches \(2T/9\).

## Proof

The centroid of every two-dimensional convex body \(K\subset\mathbb R^2\) lies in its interior. Indeed, if its centroid \(c\) lay on the boundary, a supporting line would give a nonzero \(q\) such that
\[
\langle q,w-c\rangle\le0\qquad(w\in K).
\]
Because \(K\) is two-dimensional, the inequality is strict on a positive-area subset of \(K\). Therefore
\[
0
=
\left\langle q,\int_K(w-c)\,dw\right\rangle
=
\int_K\langle q,w-c\rangle\,dw
<0,
\]
a contradiction. Hence \(c\in\operatorname{int}K\), so
\[
r=\max\{\rho\ge0:c+\rho\overline B_2\subseteq K\}
\]
is strictly positive.

Now record a shifted-centroid cap estimate for a two-dimensional convex body \(K\subset\mathbb R^2\) with area \(a\), centroid \(c\), and centered inradius \(r>0\). For every \(q\in\mathbb S^1\) and \(b\in\mathbb R\),
\[
\left|K\cap\{w:\langle q,w-c\rangle\le b\}\right|
\ge
\frac{4a}{9}\left(1-\frac{(-b)_+}{r}\right)_+^2.
\tag{3}
\]
If \(b\ge0\), the cap contains \(c\), so the planar Grünbaum inequality gives area at least \(4a/9\). If \(-r\le b<0\), put
\[
h=-b,\qquad
B=K\cap\{w:\langle q,w-c\rangle\le0\},\qquad
p=c-rq,\qquad
\theta=\frac hr.
\]
Then
\[
(1-\theta)B+\theta p
\subseteq
K\cap\{w:\langle q,w-c\rangle\le-h\},
\]
and its area is
\[
(1-\theta)^2|B|
\ge
\left(1-\frac hr\right)^2\frac{4a}{9}.
\]
If \(b<-r\), the right-hand side of (3) is zero. This is the centroid-cap homothety used in accepted fact `e480e624b1618fae`.

Each \(A_i\) is a two-dimensional convex polytope, hence a two-dimensional convex body. The preceding interior-centroid argument therefore shows \(r_i>0\) and permits applying (3) to every \(A_i\).

Accepted fact `9fa81a67fd2eaafc` gives \(z_0\in A_1\). Since \(c_1\in A_1\), convexity gives \(z_t\in A_1\) for every \(t\in[0,1]\). Fix a non-slice-parallel halfspace through \((1,z_t)\). By the exact normal form in accepted fact `400272f6de6c67bb`, its three caps have the form
\[
A_i\cap
\{w:\langle q,w-z_t\rangle\le\lambda(1-i)\}
\tag{4}
\]
for some \(q\in\mathbb S^1\) and \(\lambda\in\mathbb R\).

Set
\[
e=\langle q,\delta\rangle.
\]
The middle cap in (4) is
\[
A_1\cap
\{w:\langle q,w-c_1\rangle\le-(1-t)e\}.
\]
Its displacement away from \(c_1\) is \(((1-t)e)_+\le(1-t)D\). Hence (3), applied to the convex body \(A_1\), gives
\[
|{\rm middle\ cap}|
\ge
\frac{4a_1}{9}
\left(1-\frac{(1-t)D}{r_1}\right)_+^2.
\tag{5}
\]

For the outer caps, put
\[
d=\langle q,c_0-z_0\rangle
=-\langle q,c_2-z_0\rangle,
\qquad
\xi=\lambda-d.
\]
Relative to their centroids, the slice-\(0\) and slice-\(2\) thresholds are respectively
\[
b_0=\xi+te,\qquad b_2=-\xi+te.
\]
Thus their displacements away from their centroids are
\[
\eta_0=(-\xi-te)_+,\qquad
\eta_2=(\xi-te)_+.
\]
They satisfy
\[
\min\{\eta_0,\eta_2\}\le t(-e)_+\le tD.
\tag{6}
\]
Indeed, if \(e\ge0\), the two quantities cannot both be positive. If \(e<0\), write \(v=-e\). When \(|\xi|\ge tv\), one displacement is zero; when \(|\xi|<tv\), their minimum is \(tv-|\xi|\le tv\).

Choose \(j\in\{0,2\}\) with \(\eta_j\le tD\). Since \(A_j\) is a two-dimensional convex body, \(a_j\ge m\), and \(r_j\ge r_*\), estimate (3) gives
\[
|{\rm slice\text{-}0\ cap}|+|{\rm slice\text{-}2\ cap}|
\ge
\frac{4m}{9}
\left(1-\frac{tD}{r_*}\right)_+^2.
\tag{7}
\]
Adding (5) and (7) bounds every non-slice-parallel halfspace. The two slice-parallel terms are exactly \(T-a_2\) and \(T-a_0\) by `400272f6de6c67bb`, proving (1). Under balance, both exceed \(T/2>2T/9\), so (2) proves the target for \(t=1/2\).

To prove that this is a new nonempty region, use planar coordinates \((u,v)\) and set
\[
\begin{aligned}
A_0&=[-14/5,14/5]\times[-1,1],\\
A_1&=[-19/10,97/50]\times[-1,1],\\
A_2&=[-1,1]\times[-1,1].
\end{aligned}
\tag{8}
\]
Here
\[
\frac{A_0+A_2}{2}
=
[-19/10,19/10]\times[-1,1]
\subseteq A_1.
\]
Consequently,
\[
C=\operatorname{conv}\bigl(
(\{0\}\times A_0)\cup
(\{1\}\times A_1)\cup
(\{2\}\times A_2)
\bigr)
\]
has exactly these integer-height sections. At height \(1\), the total convex-combination weights on heights \(0\) and \(2\) are equal, so every such point lies in the convex hull of \(A_1\) and \((A_0+A_2)/2\), hence in \(A_1\). The sections at heights \(0\) and \(2\) are \(A_0\) and \(A_2\) directly.

The exact parameters are
\[
a_0=\frac{56}{5},\qquad
a_1=\frac{192}{25},\qquad
a_2=4,\qquad
T=\frac{572}{25},\qquad
\frac T2=\frac{286}{25}.
\]
Thus the triple is balanced. Moreover,
\[
c_0=c_2=(0,0),\qquad
c_1=(1/50,0),\qquad
D=\frac1{50},\qquad
r_0=r_1=r_2=r_*=1,\qquad
m=4.
\]
For \(t=1/2\), the bracket in (1) equals
\[
\left(\frac{192}{25}+4\right)
\left(\frac{99}{100}\right)^2
=
\frac{715473}{62500}
>
\frac{715000}{62500}
=
\frac T2.
\tag{9}
\]
Hence
\[
h_S((1,z_{1/2}))>\frac{2T}{9},
\qquad
z_{1/2}=(1/100,0).
\]

Neither component of the earlier bound in `e480e624b1618fae` reaches the target for this triple. Its centroid-bridge numerator satisfies
\[
(\sqrt{a_0}+\sqrt{a_2})^2+4m
=
\frac{156+8\sqrt{70}}5
<
\frac{1144}{25}
=
2T,
\tag{10}
\]
where the strict inequality is equivalent to \(\sqrt{70}<91/10\). Its inradius component satisfies
\[
m+a_1\left(1-\frac D{r_1}\right)^2
=
4+\frac{192}{25}\left(\frac{49}{50}\right)^2
=
\frac{710992}{62500}
<
\frac{715000}{62500}
=
\frac T2.
\tag{11}
\]
Thus `e480e624b1618fae` does not certify \(z_0\), while (1) certifies the interior segment point \(z_{1/2}\). All inequalities (9)–(11) are strict, so the same conclusion holds on a nonempty neighborhood within this compatible rectangle family.

## External sources

Branko Grünbaum, “Partitions of mass-distributions and of convex bodies by hyperplanes,” *Pacific Journal of Mathematics* 10 (1960), 1257–1261, https://doi.org/10.2140/pjm.1960.10.1257. The exact statement used is: if \(K\subset\mathbb R^2\) is a two-dimensional convex body with centroid \(c\), then every closed halfplane containing \(c\) intersects \(K\) in area at least \(4|K|/9\). Every application above is to one of the two-dimensional convex polygons \(A_i\), so the hypotheses are satisfied.
