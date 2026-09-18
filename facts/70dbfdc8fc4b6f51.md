---
fact_id: 70dbfdc8fc4b6f51
kind: lemma
author: "mp_r77_two_cap_polygon_kkt_localization"
assurance: LLM-verified
subgoal_id: canonical-root-tail-two-cap-allocation
depends_on: ["6e68b44550cac3c8","9fdf961ec71bd241","ca6c285cd23ef4dc","f93a19566af88e9a"]
source_packet_sha256: 9bf1e420bc0646f828147bcaec4347ed06f67e125e9b9af73674017576032793
verifier_run: 72b861b0ac2f4bd1
target_match: null
---

## Statement

Use the six rays and sector names of accepted fact `f93a19566af88e9a`:
\[
r_0=(1,0),\quad r_1=(0,1),\quad r_2=(-1,1),\quad
r_3=(-1,0),\quad r_4=(0,-1),\quad r_5=(1,-1),
\]
with sectors \(P,W_x,N_x,O,N_y,W_y\) in cyclic order. Let \(K\) be a two-dimensional convex polygon containing \(0\) in its interior. Assume that no vertex lies on a fan ray and that every ray meets the relative interior of its boundary edge transversely. Write \(S=|K|\), use the same six capital letters for the sector areas, and suppose
\[
N_x-W_y=N_y-W_x=:e>0,
\qquad
\int_Kx\,dA\ge0,\qquad \int_Ky\,dA\ge0.
\]
Put
\[
C=e+W_x+W_y+O,\qquad d=P+W_x+W_y.
\]
Thus
\[
C=|K\cap\{x\le0\}|=|K\cap\{y\le0\}|,
\qquad
e=S-C-d.
\]
Assume the Regime A constraint
\[
d\ge\frac{4S}{9}.
\]
Uniformly dilate about \(0\) so that \(S=1\), and define
\[
\Phi(K)=C^2-4ed=C^2-4d(1-C-d).
\]
Within the smooth stratum having the same number of genuine vertices and the same transversal fan-crossing pattern, suppose \(K\) is a local minimizer of \(\Phi\) among polygons satisfying
\[
S=1,\qquad
N_x-W_y=N_y-W_x,\qquad
d\ge\frac49,
\]
together with the two displayed centroid inequalities and the open condition \(e>0\). If
\[
\Phi(K)<0,
\]
then \(K\) is a triangle, and its vertices occupy one of the two alternating parity classes
\[
P,N_x,N_y
\qquad\text{or}\qquad
W_x,O,W_y.
\]
Consequently no such negative local minimizer exists.

The same terminal conclusion includes a triangular vertex on a boundary ray: replacing the three open sectors above by their closures still gives \(\Phi\ge0\) in the first parity class and \(e\le0\) in the second. The smooth vertex-velocity assertion itself is only for the stated fan-transverse stratum; no global attainment or compactness claim, and no claim about a higher polygon in a different nonsmooth ray-boundary stratum, is part of this lemma.

## Proof

It is convenient first to put the fan into the notation used by the rank calculation. Set
\[
u=x,\qquad v=y,\qquad \ell_3=-(x+y).
\]
In cyclic order let
\[
\begin{array}{lll}
A:\ u<0,\ v<0,&
B:\ u>0,\ v<0,\ u+v<0,&
C_0:\ u>0,\ v<0,\ u+v>0,\\
D:\ u>0,\ v>0,&
E:\ u<0,\ v>0,\ u+v>0,&
F:\ u<0,\ v>0,\ u+v<0.
\end{array}
\]
The correspondence with the original names is
\[
(A,B,C_0,D,E,F)=(O,N_y,W_y,P,W_x,N_x).
\tag{1}
\]
In these coordinates the three halfplane indicators, viewed as vectors in
\(\mathbb R^6\), are
\[
\begin{aligned}
h_1&=(1,0,0,0,1,1),\\
h_2&=(1,1,1,0,0,0),\\
h_3&=(0,0,1,1,1,0),
\end{aligned}
\qquad
\mathbf1=(1,1,1,1,1,1).
\tag{2}
\]
Thus \(h_1\) is the indicator of \(x\le0\), \(h_2\) that of \(y\le0\), and
\(h_3\) that of \(x+y\ge0\). The balance constraint is
\[
(h_1-h_2)\cdot s=0,
\tag{3}
\]
where \(s\) is the vector of the six sector areas.

We now derive the vertex-velocity map and its complete rank defect in the
fan-transverse stratum. Orient the genuine vertices
\(Q_1,\ldots,Q_n\) counterclockwise, put
\[
d_i=Q_{i+1}-Q_i
\]
with cyclic indices, and give \(Q_i\) velocity \(V_i\). On the \(i\)-th edge use
\[
q_i(t)=Q_i+t d_i,\qquad
V_i(t)=(1-t)V_i+tV_{i+1},
\qquad 0\le t\le1.
\]
A moving boundary element sweeps signed outward area
\[
\det(V_i(t),d_i)\,dt.
\]
At a transversal crossing with a fixed fan ray, replacing the moving crossing
point by the old one changes the swept region only by \(O(\varepsilon^2)\).
Therefore the exact first derivative of the \(j\)-th sector area is
\[
(LV)_j
=\sum_{i=1}^n\int_0^1
\mathbf1_j(q_i(t))
\det\bigl((1-t)V_i+tV_{i+1},d_i\bigr)\,dt.
\tag{4}
\]

For a sector-weight vector
\(\lambda=(\lambda_A,\lambda_B,\lambda_{C_0},
\lambda_D,\lambda_E,\lambda_F)\), let \(\lambda_i(t)\) be the weight of the
sector containing \(q_i(t)\). Expanding \(\lambda\cdot LV\) in (4) and
collecting the coefficient of \(V_i\) shows that it vanishes for every
velocity precisely when
\[
\left(\int_0^1(1-t)\lambda_i(t)\,dt\right)d_i
+
\left(\int_0^1t\lambda_{i-1}(t)\,dt\right)d_{i-1}=0
\tag{5}
\]
at every vertex. The two incident edge directions are nonparallel because the
vertices are genuine. Hence (5) is equivalent to the two scalar conditions
\[
\int_0^1(1-t)\lambda_i(t)\,dt=0,\qquad
\int_0^1t\lambda_i(t)\,dt=0
\tag{6}
\]
on every edge. Thus
\[
\ker L^T
=\{\lambda\in\mathbb R^6:\text{\((6)\) holds on every edge}\}.
\tag{7}
\]

For a nonempty interval \(I\subset(0,1)\), put
\[
m(I)=\left(\int_I(1-t)\,dt,\int_I t\,dt\right).
\]
If \(I\) precedes a disjoint interval \(J\), then
\[
\det(m(I),m(J))
=|I|\,|J|\,(\overline t_J-\overline t_I)>0,
\tag{8}
\]
where the bars denote interval midpoints. In particular, the two moment
columns belonging to two disjoint positive-length edge pieces are linearly
independent.

Because \(0\in\operatorname{int}K\), the six rays meet the boundary exactly
once and in cyclic order. Let \(k_i\) be the number of rays met in the relative
interior of the \(i\)-th edge. A supporting line cannot subtend an angle of
\(\pi\) or more at the origin, so
\[
0\le k_i\le3,\qquad \sum_i k_i=6.
\tag{9}
\]
An edge with \(k_i=0\) forces its single sector weight to vanish by (6). An
edge with \(k_i=1\) forces both weights to vanish by (8). An edge with
\(k_i=2\) has three sector pieces; if one of their weights vanishes, (8)
forces the other two to vanish. An edge with \(k_i=3\) has four sector pieces;
if two of their weights vanish, (8) forces the remaining two to vanish.

Suppose a nonzero \(\lambda\) satisfies (6). No edge can have \(k_i=1\).
Indeed, the two consecutive zero weights produced there propagate across
every adjacent edge with at most two crossings. There cannot be two
three-crossing edges in addition to the one-crossing edge because their
crossing counts would exceed six. Thus the propagation reaches both ends of
the possible unique three-crossing edge and kills it as well.

It follows that all \(k_i\) belong to \(\{0,2,3\}\). If a three-crossing edge
occurs, (9) forces exactly two such edges and all remaining edges to have zero
crossings. A zero-crossing edge in each of the two opposite endpoint sectors
would set both endpoint weights to zero and then kill both three-crossing
edges. Hence every zero-crossing edge lies in one endpoint sector. Equivalently,
all but one vertices lie in one open sector and the remaining vertex lies in
the opposite sector; its two incident edges cross three rays each. Conversely,
in this \(3+3\) pattern, prescribing the opposite-sector weight and solving
the two moment equations on each crossing edge gives a one-dimensional
annihilator.

If no three-crossing edge occurs, (9) gives exactly three two-crossing edges.
Any zero-crossing edge would give a zero weight which propagates through all
three of them, so there are no other edges. The polygon is a triangle and
each edge crosses two consecutive rays. If its crossing parameters on the
three cyclically oriented edges are
\[
0<a_i<b_i<1\qquad(i=1,2,3),
\]
then direct solution of (6) on one edge gives
\[
\frac{\lambda_1}{\lambda_0}
=-\frac{a_i(1+b_i-a_i)}{(b_i-a_i)(1-a_i)},
\qquad
\frac{\lambda_2}{\lambda_0}
=\frac{a_ib_i}{(1-a_i)(1-b_i)}.
\tag{10}
\]
All three entries are nonzero. Compatibility around the triangle is exactly
\[
\prod_{i=1}^3
\frac{a_ib_i}{(1-a_i)(1-b_i)}=1.
\tag{11}
\]
We have proved
\[
\operatorname{rank}L\ge5.
\tag{12}
\]
Rank is five exactly in the \(3+3\) pattern or in the alternating triangle
pattern satisfying (11), and is six in every other fan-transverse pattern.
This includes every rank-deficient pattern.

The nontriangular \(3+3\) annihilator has one further property needed for KKT.
Define
\[
\mathcal W=\operatorname{span}\{\mathbf1,h_1,h_2,h_3\}.
\tag{13}
\]
We claim that the annihilator line of a \(3+3\) polygon is not contained in
\(\mathcal W\). A permutation of the three forms and, if necessary,
simultaneous sign reversal sends its opposite sector pair to \(A,D\), while
preserving \(\mathcal W\). We may therefore assume that the unique vertex is
in \(A\), all remaining vertices are in \(D\), and the two crossing edges run
through
\[
A,B,C_0,D
\qquad\text{and}\qquad
A,F,E,D.
\]
Every other edge lies in \(D\), so \(\lambda_D=0\). Normalize
\(\lambda_A=1\).

Write the \(A\)-vertex in \((u,v)\)-coordinates as
\[
(-x,-y),\qquad x,y>0,\qquad
\theta=\frac{x}{x+y}.
\]
For the first crossing edge, let its \(D\)-endpoint have normalized positive
coordinates
\[
X=\frac{u}{x},\qquad Y=\frac{v}{y},\qquad X>Y>0,
\qquad
R=\frac{1+Y}{X-Y}>0.
\]
Its three crossing parameters are
\[
\frac1{1+X},\qquad
\frac1{1+Y+\theta(X-Y)},\qquad
\frac1{1+Y}.
\]
Solving its two equations (6) gives
\[
\lambda_B=-\frac{R^2+2R+\theta}{1-\theta},
\qquad
\lambda_{C_0}=\frac{R^2}{\theta}.
\tag{14}
\]
On the other crossing edge write
\[
X'=\frac{u}{x},\qquad Y'=\frac{v}{y},\qquad
Y'>X'>0,\qquad
Q=\frac{1+X'}{Y'-X'}>0.
\]
The symmetric calculation gives
\[
\lambda_F=-\frac{Q^2+2Q+1-\theta}{\theta},
\qquad
\lambda_E=\frac{Q^2}{1-\theta}.
\tag{15}
\]

Every \(w\in\mathcal W\) satisfies
\[
w_A-w_B=w_E-w_D,\qquad
w_{C_0}-w_D=w_A-w_F.
\tag{16}
\]
If the normalized annihilator belonged to \(\mathcal W\), the first relation
in (16), together with (14)-(15), would give
\[
Q^2=(R+1)^2,
\]
hence \(Q=R+1\). The second relation would then give
\[
R^2=(Q+1)^2=(R+2)^2,
\]
which forces \(R=-1\), contradicting \(R>0\). Therefore
\[
\ker L^T\cap\mathcal W=\{0\}
\tag{17}
\]
in the nontriangular rank-five pattern.

We now impose the optimization constraints. First, a negative feasible point
cannot have an active centroid inequality. If
\(\int_Kx\,dA=0\), then the centroid lies on \(x=0\), and the planar centroid
halfplane estimate proved in accepted fact `6e68b44550cac3c8` gives
\[
C=|K\cap\{x\le0\}|\ge\frac49.
\]
The same conclusion follows from
\(\int_Ky\,dA=0\), because balance makes the two side-cap areas equal.
For
\[
\phi(c,d)=c^2-4d(1-c-d)
\]
one has
\[
\frac{\partial\phi}{\partial c}=2c+4d>0,\qquad
\frac{\partial\phi}{\partial d}=4(c+2d-1).
\tag{18}
\]
On \(c,d\ge4/9\), both derivatives are positive and
\[
\phi(c,d)\ge\phi(4/9,4/9)=0.
\tag{19}
\]
This contradicts \(\Phi(K)<0\). Hence both centroid moments are strictly
positive at a negative local minimizer. The condition \(e>0\) is also open.
The only active constraints are therefore area normalization, balance, and
possibly \(d=4/9\).

Suppose now that the negative local minimizer is not an alternating triangle.
By the rank classification, \(L\) is either onto or has the nontriangular
\(3+3\) rank defect. In the latter case, (17) implies that the differentials
of
\[
\mathbf1\cdot s=1,\qquad
(h_1-h_2)\cdot s=0,
\]
and, when active, \(h_3\cdot s=4/9\), are independent after pullback by \(L\).
They are plainly independent in the onto case. Thus the ordinary multiplier
rule applies.

At \(S=1\), put \(c=h_1\cdot s=h_2\cdot s\) and \(d=h_3\cdot s\).
There exist \(\alpha,\beta\in\mathbb R\) and, only when \(d=4/9\), a
multiplier \(\mu\ge0\) such that
\[
L^Tq=0,
\tag{20}
\]
where
\[
q=
(2c+4d)h_1
+\bigl(4(c+2d-1)-\mu\bigr)h_3
-\alpha\mathbf1-\beta(h_1-h_2).
\tag{21}
\]
In particular \(q\in\mathcal W\). The four vectors
\(\mathbf1,h_1,h_2,h_3\) are linearly independent. Since
\[
2c+4d>0,
\]
the \(h_1\)- and \(h_2\)-coefficients in (21) cannot both vanish, so
\[
q\ne0.
\tag{22}
\]
If \(L\) is onto, (20) contradicts (22). If \(L\) has the nontriangular
\(3+3\) rank defect, (20)-(22) contradict (17). Therefore the local minimizer
must be the remaining rank-five pattern: a triangle whose vertices occupy
either
\[
B,D,F
\qquad\text{or}\qquad
A,C_0,E.
\]
By (1), these are precisely
\[
P,N_x,N_y
\qquad\text{or}\qquad
W_x,O,W_y.
\tag{23}
\]

For the first class, accepted fact `9fdf961ec71bd241` gives
\[
(e+W_x+W_y+O)^2\ge4e(P+W_x+W_y),
\]
contradicting \(\Phi(K)<0\). For the second class, the nonnegative centroid
moments and accepted fact `ca6c285cd23ef4dc` give \(e\le0\), contradicting
\(e>0\). Both accepted facts explicitly include vertices on their indicated
boundary rays; the first even makes the inequality strict there. Thus the
terminal triangular ray-boundary cases require no perturbation and are
excluded as well.

This proves the claimed local result. The argument produces a descent
direction at every negative nontriangular point of a smooth fan-transverse
stratum, but it does not prove that iterating such directions attains a
triangle, that a normalized global minimum exists, or that a minimizing
sequence cannot enter a different higher-polygon ray-boundary stratum.

## External sources

none
