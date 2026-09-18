---
fact_id: eeb8a6b3b5e04d6c
kind: lemma
author: "mp_r342_quantile_clearance_survivor"
assurance: LLM-verified
subgoal_id: counterexample-quantile-clearance-survivor
depends_on: ["19703e1e768865b1"]
source_packet_sha256: b725ef6f362d972ecbb92239e0aba2822e1413f2b5fc1ed6e390eae109012019
verifier_run: b4b356bd0c804bd3
target_match: null
---

## Statement

Let \(A_0,A_2\) be the endpoint triangles in accepted fact
`19703e1e768865b1`:
\[
\begin{aligned}
A_0=\operatorname{conv}\{&
(-1719/1000,-203/1000),\\
&(1519/500,-629/1000),\\
&(-333/200,53/250)\},
\end{aligned}
\]
\[
\begin{aligned}
A_2=\operatorname{conv}\{&
(149/100,109/50),\\
&(669/250,2063/1000),\\
&(1503/1000,2273/1000)\}.
\end{aligned}
\]
Write
\[
M=|A_0|=\frac{1997159}{2000000},
\qquad
m=|A_2|=\frac{111819}{2000000},
\]
and put
\[
z=\left(\frac{5323}{3000},\frac{737}{375}\right).
\]
Every point \(p\in z-A_2\) has planar halfspace depth in \(A_0\) at
least \(M/9\).  In particular,
\[
\frac M9-m=\frac{247697}{4500000}>0.
\tag{1}
\]

For any nonzero linear form \(\lambda:\mathbb R^2\to\mathbb R\), define
\[
q(\lambda)=\inf\left\{
q:\left|A_0\cap\{\lambda\le q\}\right|\ge m
\right\},
\qquad
\beta(\lambda)=\max_{a\in A_2}\lambda(a).
\tag{2}
\]
Then
\[
q(\lambda)+\beta(\lambda)<\lambda(z).
\tag{3}
\]
Consequently, for every triple of nonzero linear forms satisfying
\(\lambda_1+\lambda_2+\lambda_3=0\),
\[
\sum_{i=1}^3\bigl(q(\lambda_i)+\beta(\lambda_i)\bigr)<0.
\tag{4}
\]
Thus no such triple can satisfy the strict projection-quantile budget
\[
\sum_{i=1}^3\bigl(q(\lambda_i)+\beta(\lambda_i)\bigr)>2
\]
required by accepted fact `19703e1e768865b1`.

## Proof

We first prove a depth bound for a triangle.  Let \(\Delta\) be a
triangle of area \(D\), and let \(p\in\operatorname{int}\Delta\) have
barycentric coordinates
\[
(\alpha,\beta,\gamma),\qquad
\alpha,\beta,\gamma\ge\frac16.
\tag{5}
\]
We claim that every closed halfplane containing \(p\) cuts area at least
\(D/9\) from \(\Delta\).

It is enough to consider a halfplane whose boundary line passes through
\(p\), since translating the boundary of an arbitrary halfplane toward
\(p\), on the side that retains \(p\), can only decrease its
intersection with \(\Delta\).  A line through an interior point divides
the triangle into a triangular side and a quadrilateral side, with the
usual limiting interpretation when the line passes through a vertex.
Relabel the vertices so that the triangular side has first vertex
\((1,0,0)\) and its other two vertices are
\[
X=(1-r,r,0),\qquad Y=(1-s,0,s),
\qquad 0<r,s\le1.
\]
For some \(0<\theta<1\),
\[
p=\theta X+(1-\theta)Y.
\]
Hence
\[
\beta=\theta r,\qquad
\gamma=(1-\theta)s.
\]
The triangular side has relative area
\[
rs=\frac{\beta\gamma}{\theta(1-\theta)}
\ge4\beta\gamma\ge\frac19.
\tag{6}
\]
The quadrilateral side has relative area \(1-rs\).  Moreover,
\[
\alpha=\theta(1-r)+(1-\theta)(1-s),
\]
while
\[
1-rs\ge\max\{1-r,1-s\}\ge\alpha\ge\frac16.
\tag{7}
\]
Thus either side has relative area at least \(1/9\), proving the claim.
The vertex-line degeneracies follow directly from the same inequalities
with a zero-length boundary segment, or by taking a limit.

We now verify that the reflected small triangle \(z-A_2\) lies in the
barycentric core (5) of \(A_0\).  In the displayed vertex order of
\(A_0\) and \(A_2\), the barycentric coordinates in \(A_0\) of the
three vertices \(z-a\), \(a\in\operatorname{vert}(A_2)\), are
\[
\left(
\frac{367224}{1997159},
\frac{2496040}{5991477},
\frac{33715}{84387}
\right),
\tag{8}
\]
\[
\left(
\frac{814399}{1997159},
\frac{1000516}{5991477},
\frac{35884}{84387}
\right),
\tag{9}
\]
\[
\left(
\frac{815536}{1997159},
\frac{2494921}{5991477},
\frac{14788}{84387}
\right).
\tag{10}
\]
These are exact: substituting them in the affine combination of the
three displayed vertices of \(A_0\) gives respectively
\(z-a\), and each row sums to one.  Subtracting \(1/6\) coordinatewise
gives
\[
\left(
\frac{206185}{11982954},
\frac{998307}{3994318},
\frac{39301}{168774}
\right),
\tag{11}
\]
\[
\left(
\frac{2889235}{11982954},
\frac{1291}{3994318},
\frac{43639}{168774}
\right),
\tag{12}
\]
\[
\left(
\frac{2896057}{11982954},
\frac{997561}{3994318},
\frac{1447}{168774}
\right),
\tag{13}
\]
whose nine entries are positive.  The region in \(A_0\) where all three
barycentric coordinates are at least \(1/6\) is convex.  Since the
vertices (8)-(10) lie in it, the whole triangle \(z-A_2\) lies in it.
Applying (6)-(7) after an affine transformation from \(A_0\) to
\(\Delta\) proves that every \(p\in z-A_2\) has depth at least \(M/9\).
The exact difference in (1) follows from the displayed values of \(M\)
and \(m\).

Fix a nonzero \(\lambda\), and choose \(a_\lambda\in A_2\) with
\[
\lambda(a_\lambda)=\beta(\lambda).
\]
Then \(p_\lambda=z-a_\lambda\) belongs to \(z-A_2\), so the halfplane
\(\{\lambda\le\lambda(p_\lambda)\}\), which contains
\(p_\lambda\), satisfies
\[
\left|A_0\cap
\{\lambda\le\lambda(p_\lambda)\}\right|
\ge\frac M9>m.
\tag{14}
\]
The cap-area function
\[
s\longmapsto
\left|A_0\cap\{\lambda\le s\}\right|
\]
is continuous.  Also \(p_\lambda\) is in the interior of \(A_0\), since
all its barycentric coordinates are strictly positive.  Therefore
\(\lambda(p_\lambda)>\min_{A_0}\lambda\), and the strict area margin in
(14), together with continuity, gives some
\(s<\lambda(p_\lambda)\) whose cap area is still greater than \(m\).
By (2),
\[
q(\lambda)<\lambda(p_\lambda)
=\lambda(z)-\beta(\lambda),
\]
which is (3).

Applying (3) to \(\lambda_1,\lambda_2,\lambda_3\) and using their
zero sum gives
\[
\sum_{i=1}^3
\bigl(q(\lambda_i)+\beta(\lambda_i)\bigr)
<
\sum_{i=1}^3\lambda_i(z)=0.
\]
This proves (4).

## External sources

none
