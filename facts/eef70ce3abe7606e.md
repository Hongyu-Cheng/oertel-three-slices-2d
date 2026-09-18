---
fact_id: eef70ce3abe7606e
kind: lemma
author: "/root/mp_r43_triangle_cad"
assurance: LLM-verified
subgoal_id: canonical-all-double-strict-rational-realizability
depends_on: ["b1eaab0ae37367d1","b7cb6541c1d790bc"]
source_packet_sha256: 4c54bf9b90b9cf579b1c4bc1b6f18a9a99a207105cfb1135f85cf055b063f01d
verifier_run: 35a4a53d31f94866
target_match: null
---

## Statement

Assume the polytopal \(A_2\)-only setting of the strict rational table: the
three pairwise interior-disjoint outer caps have equal positive area and the
central remainder has twice that area.  Apply accepted fact
`b7cb6541c1d790bc` and affinely normalize the global central triangle to
\[
\Delta=\left\{\alpha\in\mathbb R^3:
\alpha_1+\alpha_2+\alpha_3=1,\quad \alpha_i\geq0\right\}.
\]
Use \((\alpha_1,\alpha_2)\) as planar coordinates and let
\(e_1,e_2,e_3\) be the three barycentric vertices.  Then every polygon
obtained from the accepted reduction is represented by the following
fifteen scalars:
\[
x_{ij}\quad(i\ne j),\qquad
\rho_{12},\rho_{23},\rho_{31},\qquad
\theta_{12},\theta_{23},\theta_{31},\qquad
\tau_1,\tau_2,\tau_3.
\tag{1}
\]
They satisfy
\[
x_{ij}\geq0,\qquad
L_i:=1-x_{i,i^-}-x_{i,i^+}>0,
\tag{2}
\]
and, for the cyclic pairs \((i,j)=(1,2),(2,3),(3,1)\),
\[
x_{ij}=0\quad\Longleftrightarrow\quad x_{ji}=0.
\tag{2a}
\]
Condition (2a) is the finite union of the eight strata obtained by choosing,
for each cyclic pair, whether both entries vanish or both are positive.
\[
0\leq\rho_{12},\rho_{23},\rho_{31}\leq1,
\qquad
0\leq\theta_{12},\theta_{23},\theta_{31}\leq1,
\qquad
0<\tau_i<1.
\tag{3}
\]
Here \(i^+=i+1\) and \(i^-=i-1\), with indices modulo \(3\) in
\(\{1,2,3\}\).  Define
\[
D
=1-(1-\rho_{12})x_{12}x_{21}
  -(1-\rho_{23})x_{23}x_{32}
  -(1-\rho_{31})x_{31}x_{13},
\tag{4}
\]
and require \(D>0\).  Put
\[
c=\frac D4,\qquad h_i=\frac{D}{2L_i}.
\tag{5}
\]

For distinct \(i,j\), let \(k\) be the missing index and define the chord
endpoint
\[
p_{ij}=(1-x_{ij})e_k+x_{ij}e_j.
\tag{6}
\]
For the cyclic pairs \((i,j)=(1,2),(2,3),(3,1)\), again with missing index
\(k\), define
\[
z_{ij}
=\rho_{ij}e_k
 +(1-\rho_{ij})
  \bigl((1-\theta_{ij})p_{ij}+\theta_{ij}p_{ji}\bigr).
\tag{7}
\]
Define the outer cap vertex
\[
u_i
=-h_i e_i
 +(1+h_i)\bigl((1-\tau_i)e_{i^-}+\tau_i e_{i^+}\bigr).
\tag{8}
\]
Finally form the cyclic labeled list
\[
\mathcal V=
(p_{13},u_1,p_{12},z_{12},p_{21},u_2,
  p_{23},z_{23},p_{32},u_3,p_{31},z_{31}).
\tag{9}
\]

For planar vectors write \([a,b]=\det(a,b)\), using their
\((\alpha_1,\alpha_2)\)-coordinates.  The exact convex-order constraint is
\[
[V_{r+1}-V_r,V_s-V_r]\geq0
\quad
\text{for every }r,s\in\{1,\ldots,12\},
\tag{10}
\]
where \(V_{13}=V_1\).  Redundant entries in (9) are allowed.  After
substituting (4)-(8), (10) is a finite semialgebraic system: multiplying by
the positive product \(L_1L_2L_3\) clears every denominator without changing
an inequality.

Conversely, every tuple satisfying (2)-(5) and (10), including (2a), defines
a convex polygon whose only positive cells are its three outer caps and its central
remainder, with coordinate areas
\[
|C_1|=|C_2|=|C_3|=c,\qquad |C_0|=2c.
\tag{11}
\]
Thus its coordinate total area is \(5c=5D/4\).

If the polygon is rescaled so that its physical area is one, and
\(E_i\) are the physical vertices of the global central triangle, then
\[
\left|\det(E_1-E_3,E_2-E_3)\right|=\frac4{5D},
\qquad
|\mathcal T_Q|=\frac2{5D}.
\tag{12}
\]
Consequently the lower bound in accepted fact `b1eaab0ae37367d1` is
equivalent in this finite system to
\[
D\leq\frac4{169}.
\tag{13}
\]
The desired \(A_2\)-only upper bound is therefore exactly the assertion that
(2)-(5) and (10) force
\[
D>\frac4{169}.
\tag{14}
\]

## Proof

Let the three central halfplanes be \(\alpha_i\geq0\).  Pairwise
disjointness of the outer cap interiors implies that each endpoint of the
chord on \(\alpha_i=0\) lies on the side of \(\Delta\), rather than on an
extension beyond a vertex.  Indeed, if at such an endpoint some
\(\alpha_j<0\), a sufficiently small relative neighborhood inside the
polygon on the outer side of \(\alpha_i=0\) would have both
\(\alpha_i<0\) and \(\alpha_j<0\), giving a positive-area overlap of two
caps.  Therefore there are unique \(x_{ij}\geq0\) such that (6) holds.
Endpoints on different sides coincide only at the common vertex \(e_k\).
Since each line crosses the polygon interior, such a point is an endpoint
of both chords through it; this is exactly (2a).  The two endpoints on side
\(i\) remain distinct and occur in the correct order exactly when
\[
x_{i,i^-}+x_{i,i^+}<1,
\]
which is (2).  Thus the same-line denominators \(L_i\) never vanish, even
on a cross-line coincidence stratum.

The accepted reduction leaves at most one unmarked vertex on the central arc
from \(p_{ij}\) to \(p_{ji}\).  Let \(k\) be the missing index.  The convex
central cell contains the chord \(p_{ij}p_{ji}\), while its complementary
boundary arc through the other four marks lies on the side of that chord
opposite \(e_k\).  Hence the short labeled arc lies in
\[
\operatorname{conv}\{e_k,p_{ij},p_{ji}\}.
\]
Every possible unmarked vertex on that arc has the unique form (7), apart
from the immaterial nonuniqueness when it lies on the chord or equals
\(e_k\).  The parameter \(\rho_{ij}\) is its height fraction above the
chord, while \(\theta_{ij}\) is its tangential fraction.

The six marks alone bound the central hexagon
\[
H=(p_{12},p_{21},p_{23},p_{32},p_{31},p_{13}).
\]
It is obtained from \(\Delta\) by deleting the three corner triangles of
areas
\[
\frac{x_{12}x_{21}}2,\qquad
\frac{x_{23}x_{32}}2,\qquad
\frac{x_{31}x_{13}}2.
\]
Thus
\[
|H|
=\frac12\left(
1-x_{12}x_{21}-x_{23}x_{32}-x_{31}x_{13}
\right).
\tag{15}
\]
Replacing the chord \(p_{ij}p_{ji}\) by the two-edge arc through \(z_{ij}\)
adds
\[
\frac{\rho_{ij}x_{ij}x_{ji}}2.
\tag{16}
\]
Equations (4), (15), and (16) give the central-cell area
\[
|C_0|=\frac D2.
\tag{17}
\]

The reduced cap arc on side \(i\) has endpoints
\(p_{i,i^-},p_{i,i^+}\) and at most one outer vertex.  Its base occupies the
fraction \(L_i\) of the corresponding side of \(\Delta\).  At barycentric
height \(\alpha_i=-h_i\), every point of the cap-only chamber has the form
(8) for a unique \(0<\tau_i<1\).  The cap triangle has coordinate area
\[
|C_i|=\frac{L_i h_i}{2}.
\tag{18}
\]
With (5), equations (17)-(18) become exactly (11).  Thus all four area
conditions have been eliminated from the free variables rather than added
as equations.  On the generic stratum this also matches the elementary
dimension count: the normalized marks and six unmarked vertices have
eighteen scalar coordinates, while equality of the three cap areas and the
condition \(|C_0|=2|C_1|\) impose three independent relations.

The list (9) follows the six chamber arcs in their boundary order.  Every
three-point arc stays in its assigned convex chamber by (3), (7), and (8).
Condition (10) says that every listed point lies in the closed left
halfplane of every directed consecutive edge.  It is therefore equivalent
to (9) being the counterclockwise boundary list of a convex polygon, with
collinear or redundant entries allowed.  This proves both necessity and
sufficiency of the stated finite system.

It remains to compute the objective.  Let
\[
J=\left|\det(E_1-E_3,E_2-E_3)\right|.
\]
The affine map from \((\alpha_1,\alpha_2)\)-coordinates to the physical
plane has area multiplier \(J\).  Since the physical polygon has area one
and its coordinate area is \(5D/4\),
\[
J\frac{5D}{4}=1.
\]
The normalized central triangle has coordinate area \(1/2\), so
\[
|\mathcal T_Q|=\frac J2=\frac2{5D}.
\]
This proves (12).  Comparing with \(169/10\) gives (13), and its strict
negation is (14).  No inequality beyond this exact finite target is asserted.

## External sources

none
