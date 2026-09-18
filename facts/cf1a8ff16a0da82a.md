---
fact_id: cf1a8ff16a0da82a
kind: lemma
author: "mp_r331_crossing_core_cex"
assurance: LLM-verified
subgoal_id: convex-extension-support-clearance
depends_on: []
source_packet_sha256: e0b6c493e66bb3c20529bc32ebec08a766e2bb2bef98a621a6652d35e6bf3779
verifier_run: 3192ed938ed24371
target_match: null
---

## Statement

Let \(B\subset\mathbb R^2\) be a compact two-dimensional convex body, let \(H\subset\mathbb R^2\) be a proper closed halfplane with \(B\subseteq H\), and let \(K\supseteq B\) be a compact convex body. With planar area denoted by \(|\cdot|\), put
\[
A=|K\setminus B|,
\qquad
e=|(K\setminus B)\cap H|
\]
and define the support-clearance value
\[
\Gamma(B,H)=
\inf_{z\in\partial H}
\left(
|\operatorname{conv}(B\cup\{z\})|-|B|
\right).
\tag{1}
\]
Then
\[
e<A\quad\Longrightarrow\quad e\ge\Gamma(B,H).
\tag{2}
\]
The infimum in (1) is always attained. Moreover,
\[
\Gamma(B,H)=0
\quad\Longleftrightarrow\quad
B\cap\partial H\ne\varnothing.
\tag{3}
\]
In particular, \(\Gamma(B,H)>0\) when \(B\subset\operatorname{int}H\).

Suppose now that \(B\) is a convex polygon with counterclockwise cyclic vertices
\[
v_0,v_1,\ldots,v_{n-1},
\qquad v_n=v_0.
\]
Choose any affine parametrization
\[
z(s)=z_0+s d
\qquad(s\in\mathbb R)
\tag{4}
\]
of \(\partial H\), where \(d\ne0\), and write
\[
[u,v]=\det(u,v).
\]
For \(i=0,\ldots,n-1\), define
\[
\alpha_i=-[v_{i+1}-v_i,d],
\qquad
\beta_i=-[v_{i+1}-v_i,z_0-v_i].
\tag{5}
\]
Then the exact visible-edge formula is
\[
\boxed{
\ |\operatorname{conv}(B\cup\{z(s)\})|-|B|
=
\frac12\sum_{i=0}^{n-1}
\max\{0,\alpha_i s+\beta_i\}.
\ }
\tag{6}
\]
Thus the function in (6) is finite, convex, coercive, and piecewise affine. Its breakpoints belong to the finite set
\[
\mathcal R=
\left\{
-\frac{\beta_i}{\alpha_i}:
\alpha_i\ne0
\right\},
\tag{7}
\]
and
\[
\Gamma(B,H)
=
\min_{r\in\mathcal R}
\frac12\sum_{i=0}^{n-1}
\max\{0,\alpha_i r+\beta_i\}.
\tag{8}
\]
The set \(\mathcal R\) is nonempty. If all vertices \(v_i\), the point \(z_0\), and the direction \(d\) are rational, then every number in (5), every breakpoint in (7), and the minimum in (8) are rational. In particular, (8) is an exact finite rational computation whenever both \(B\) and \(H\) are rational.

## Proof

Assume first that \(e<A\). Since \(B\subseteq H\),
\[
A-e
=|(K\setminus B)\setminus H|
=|K\setminus H|>0.
\]
Hence \(K\) contains a point \(x\notin H\). Because \(B\) is two-dimensional and is contained in \(H\), it has a point \(b\in\operatorname{int}H\). The segment \([b,x]\subseteq K\) meets \(\partial H\) at some point \(z\). Both \(B\) and \(z\) lie in \(H\), so convexity gives
\[
\operatorname{conv}(B\cup\{z\})
\subseteq K\cap H.
\tag{9}
\]
Since \(B\subseteq\operatorname{conv}(B\cup\{z\})\), subtracting \(B\) from (9) gives
\[
\operatorname{conv}(B\cup\{z\})\setminus B
\subseteq
(K\setminus B)\cap H.
\]
Taking areas proves
\[
e\ge
|\operatorname{conv}(B\cup\{z\})|-|B|
\ge\Gamma(B,H),
\]
which is (2). This argument includes \(e=0\), support contact, and every case in which \(z\) lies on a vertex or a positive-length face of \(B\).

We next prove attainment and (3) for an arbitrary compact two-dimensional convex body. Parametrize \(\partial H\) as in (4) and set
\[
g(s)=|\operatorname{conv}(B\cup\{z(s)\})|-|B|.
\tag{10}
\]
The function \(g\) is continuous. One way to see this is to choose a closed disk containing \(B\) and \(z(s)\) for \(s\) in any fixed compact interval. Convex hulls vary continuously there in the Hausdorff metric, and planar area is continuous on compact convex sets under Hausdorff convergence.

The function \(g\) is coercive. Indeed, since \(B\) is two-dimensional, there are \(p,q\in B\) with
\[
[q-p,d]\ne0.
\]
The triangle \(\operatorname{conv}\{p,q,z(s)\}\) lies in
\(\operatorname{conv}(B\cup\{z(s)\})\), and its area is
\[
\frac12
\left|
[q-p,z_0-p]+s[q-p,d]
\right|.
\]
This tends to infinity as \(|s|\to\infty\). Therefore
\[
g(s)\ge
\left|\operatorname{conv}\{p,q,z(s)\}\right|-|B|
\longrightarrow\infty.
\]
Continuity and coercivity show that \(g\) attains its infimum.

If \(B\cap\partial H\ne\varnothing\), choose
\(z\in B\cap\partial H\). Then
\(\operatorname{conv}(B\cup\{z\})=B\), so
\(\Gamma(B,H)=0\). Conversely, suppose that
\(B\cap\partial H=\varnothing\). Every \(z\in\partial H\) then lies
outside the closed convex body \(B\). Adding an exterior point to a
two-dimensional convex body strictly increases its area, so \(g(s)>0\)
for every \(s\). Since the minimum is attained, it is strictly positive.
This proves (3), including vertex contact, edge contact, and strict
support clearance. Notice also that if \(A=0\), or if \(K\) leaves \(H\)
only on a null boundary set, then \(e=A\) and the premise of (2) is
correctly false.

It remains to prove the polygonal formula and its rational
minimization. For a counterclockwise edge
\([v_i,v_{i+1}]\), define
\[
D_i(z)=[v_{i+1}-v_i,z-v_i].
\tag{11}
\]
The polygon \(B\) lies on the left side of every directed edge, so the
edge is visible from \(z\) exactly when \(D_i(z)<0\). If \(z\notin B\),
the visible edges form one cyclic consecutive chain between the two
tangent contacts from \(z\) to \(B\). The triangles
\[
\operatorname{conv}\{z,v_i,v_{i+1}\}
\qquad(D_i(z)<0)
\]
have disjoint interiors, and their union, up to their boundary
segments, is
\[
\operatorname{conv}(B\cup\{z\})\setminus B.
\tag{12}
\]
Each such triangle has area \(-D_i(z)/2\). Hence
\[
|\operatorname{conv}(B\cup\{z\})|-|B|
=\frac12\sum_{i=0}^{n-1}\max\{0,-D_i(z)\}.
\tag{13}
\]
If \(z\in B\), all \(D_i(z)\ge0\), and both sides of (13) are zero.
If \(z\) lies on an edge line, including a tangent vertex or a
collinear boundary segment, the corresponding determinant is zero and
(13) remains literal. Thus (13) covers all visibility and contact
degeneracies.

For completeness, the area identity in (12) can also be checked
without a picture. If the visible chain runs from edge \(p\) through
edge \(q\), then
\[
\begin{aligned}
\sum_{i=p}^{q}-D_i(z)
&=
\sum_{i=p}^{q}
\bigl(
[v_i,z]+[z,v_{i+1}]-[v_i,v_{i+1}]
\bigr)\\
&=
[v_p,z]+[z,v_{q+1}]
-\sum_{i=p}^{q}[v_i,v_{i+1}].
\end{aligned}
\]
After division by \(2\), this is exactly the shoelace-area change
obtained by replacing the visible boundary chain by the two hull edges
\([v_p,z]\) and \([z,v_{q+1}]\).

Substituting \(z=z_0+s d\) into (11) gives
\[
-D_i(z(s))
=-[v_{i+1}-v_i,z_0-v_i]
-s[v_{i+1}-v_i,d]
=\beta_i+\alpha_i s.
\]
Equation (13) is therefore exactly (6). Each summand in (6) is the
maximum of two affine functions, so their sum is finite, convex, and
piecewise affine. Coercivity was already proved above. It also implies
that at least one \(\alpha_i\) is positive and at least one is negative,
so \(\mathcal R\ne\varnothing\).

Between consecutive values in the sorted set \(\mathcal R\), the signs
of all \(\alpha_i s+\beta_i\) are fixed, and (6) is affine. A coercive
piecewise-affine function cannot attain its minimum in the interior of
such an interval unless it is constant there; in the constant case the
same value is attained at both finite endpoints. Consequently its
global minimum is attained at a breakpoint, which proves (8).

Finally, if \(v_i,z_0,d\in\mathbb Q^2\), then (5) gives
\(\alpha_i,\beta_i\in\mathbb Q\). Every breakpoint in (7) is rational,
and evaluating (6) there uses only rational arithmetic and comparisons.
Thus the minimum in (8) is rational and is found by a finite exact
visible-edge audit. This completes the proof.

## External sources

none
