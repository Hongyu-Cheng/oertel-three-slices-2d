---
fact_id: 9fdba5fffd591cda
kind: lemma
author: "mp_r399_midpoint_separator"
assurance: LLM-verified
subgoal_id: counterexample-opposite-asymmetric-low-r
depends_on: ["18ec957fdaeb4b8d","711016a2ec425271","9aa5e8e4ddcd1c62"]
source_packet_sha256: 4fd137f8c14c96234e47bc0d977955287e906f9acc1976306afee90174397043
verifier_run: 08e0e15956db4ac1
target_match: null
---

## Statement

Use the common affine coordinates and exact-cell convention of accepted fact `9aa5e8e4ddcd1c62`.  Thus
\[
D=16072081,\qquad
\gamma=\frac{320000}{D},\qquad
d=\frac{D}{640000000},\qquad
\varepsilon=\frac{126243}{32144162000}.
\]
In \((\pi_1,\pi_2)\)-coordinates the closure of the central endpoint cell is
\[
T_{10}:=\{(x,y):x\geq0,\ y\geq0,\ x+y\leq10\},
\]
and physical area is \(\gamma\) times coordinate area.  In
\((\theta_1,\theta_2)=(x,y)\)-coordinates one has
\(\theta_3=-12-x-y\).  Let \(A_2\) be any compact
two-dimensional convex body, and write \(Q\) for its image in these
\(\theta\)-coordinates.  Suppose its exact \(Q\)-cell areas are
\[
\begin{array}{c|rrrrrrr}
J&1&2&3&12&13&23&123\\ \hline
|Q_J|_{\rm phys}&
\frac{11}{2000}&0&\frac1{2000}&
\frac3{2000}&\frac1{2000}&
\frac3{2000}&\frac1{2000}.
\end{array}
\tag{1}
\]
Accepted facts `18ec957fdaeb4b8d` and `711016a2ec425271`
give two actual such endpoint polygons in this common fan.

There is no compact convex body \(K\) satisfying
\[
\frac{A_0+A_2}{2}\subseteq K
\tag{2}
\]
whose middle exact cells have, in particular, the two target areas
\[
\rho_1=\frac{4327}{15000}-\frac{\varepsilon}{2},
\qquad
\rho_3=\frac{2611}{10000}-\frac{\varepsilon}{2}
\tag{3}
\]
from `9aa5e8e4ddcd1c62`.  Hence no realization of (1), including
either accepted endpoint polygon, can realize the full target
\(\rho\)-table in that fact.

More generally, let \(C_1=\overline{Q_1}\) and
\(C_3=\overline{Q_3}\), and define
\[
r_i=\max_{C_i}(x+y)-\min_{C_i}x-\min_{C_i}y
\qquad(i=1,3).
\tag{4}
\]
The endpoint table and convexity imply the exact profile constraints
\[
|C_1|_{\rm coord}=11d,\qquad
|C_3|_{\rm coord}=|Q_{13}|_{\rm coord}=d,
\tag{5}
\]
\[
11d\le r_1h_1-\frac{h_1^2}{2},\qquad
d\le r_3h_3-\frac{h_3^2}{2},
\tag{6}
\]
\[
d\ge 12h+\frac{h^2}{2},
\qquad h=\min\{h_1,h_3\},
\tag{7}
\]
where \(h_i=\max\{y:(x,y)\in C_i\}\).  The target singleton
areas additionally imply
\[
r_1\le
\frac{73695475241}{96000000000}<1,\qquad
r_3\le
\frac{7775191129}{32000000000}<\frac14.
\tag{8}
\]
Equations (5)--(8) are inconsistent.

## Proof

All positive entries of (1) contain strict chamber points.  In the
\((x,y)=(\theta_1,\theta_2)\)-plane the relevant chambers are
\[
\begin{array}{c|c}
Q_1&y>0,\ x+y<-12,\\
Q_{12}&y<0,\ x+y<-12,\\
Q_{13}&y>0,\ -12-y<x<0,\\
Q_3&x>0,\ y>0,\\
Q_{23}&x>0,\ y<0,\ x+y>-12.
\end{array}
\tag{9}
\]
Boundary choices do not affect area.

Choose strict points in \(Q_1\) and \(Q_{12}\).  Their segment lies
in \(Q\), remains on the side \(x+y<-12\), and crosses \(y=0\).
Approaching the crossing from \(Q_1\) proves
\[
\min_{C_1}y=0.
\tag{10}
\]
Likewise, a segment from a strict \(Q_1\)-point to a strict
\(Q_{13}\)-point crosses \(x+y=-12\) while \(y>0\), so
\[
\max_{C_1}(x+y)=-12.
\tag{11}
\]
If \(a=\min_{C_1}x\), then (4), (10), and (11) give
\[
r_1=-12-a
\]
and
\[
C_1\subseteq
\{(x,y):x\ge a,\ y\ge0,\ x+y\le-12\}.
\tag{12}
\]

Segments from a strict \(Q_3\)-point to strict points in
\(Q_{13}\) and \(Q_{23}\), respectively, give
\[
\min_{C_3}x=\min_{C_3}y=0.
\tag{13}
\]
Consequently
\[
C_3\subseteq
\{(x,y):x\ge0,\ y\ge0,\ x+y\le r_3\}.
\tag{14}
\]
The physical-to-coordinate Jacobian and (1) now give (5).

We record the exact Minkowski constraint.  For every compact convex
planar set \(C\), put
\[
r(C)=\max_C(x+y)-\min_Cx-\min_Cy.
\]
The three outward normals of \(T_L\) are proportional to
\((0,-1),(-1,0),(1,1)\).  Expanding the shoelace formula for the
ordered edge vectors of the Minkowski sum, or equivalently adding
the three boundary strips, gives the identity
\[
|T_L+C|_{\rm coord}
=\frac{L^2}{2}+|C|_{\rm coord}+Lr(C).
\tag{15}
\]
Indeed, the three strip contributions are
\(L(-\min_Cy)\), \(L(-\min_Cx)\), and
\(L\max_C(x+y)\); their sum is translation invariant and equals
\(Lr(C)\).  This also proves (15) for a general compact convex
\(C\) by polygonal approximation.

For \(i=1,3\), the midpoint of the central \(P_0\)-cell and \(Q_i\)
has positive scores at both indices different from \(i\); since the
three middle scores sum to \(-1\), its remaining score is negative.
Thus, up to null cutting lines,
\[
\frac{T_{10}+C_i}{2}\subseteq K\cap R_i.
\tag{16}
\]
Using (15), (5), and the Jacobian therefore gives
\[
\rho_1\ge
\frac{\gamma}{4}\bigl(50+11d+10r_1\bigr),
\qquad
\rho_3\ge
\frac{\gamma}{4}\bigl(50+d+10r_3\bigr).
\tag{17}
\]
Equality in either inequality in (17) holds exactly when the
corresponding middle cell has no positive-area part outside the
Minkowski set in (16).  Also
\[
|C|\le\frac{r(C)^2}{2},
\tag{18}
\]
because translating by \((-\min_Cx,-\min_Cy)\) puts \(C\) in
\(T_{r(C)}\).  Equality in (18) holds exactly when \(C\) is that
translated triangle.  Hence the ordinary Brunn--Minkowski singleton
gate is the coarsening of the exact support identity (17), and its
equality case requires both this aligned triangle and equality in
(16).

Substituting (3) into (17) and simplifying over \(\mathbb Q\) gives
\[
r_1\le
\frac{4\rho_1/\gamma-50-11d}{10}
=\frac{73695475241}{96000000000},
\tag{19}
\]
\[
r_3\le
\frac{4\rho_3/\gamma-50-d}{10}
=\frac{7775191129}{32000000000}.
\tag{20}
\]
The exact gaps
\[
1-\frac{73695475241}{96000000000}
=\frac{22304524759}{96000000000}>0,
\]
\[
\frac14-\frac{7775191129}{32000000000}
=\frac{224808871}{32000000000}>0
\]
prove (8).

It remains to use the shared section profile.  By (12), at height
\(0\le y\le h_1\) a horizontal section of \(C_1\) has length at
most \(r_1-y\).  By (14), the analogous section of \(C_3\) has
length at most \(r_3-y\).  Integration gives the sharp bounds (6).
Equality in either bound in (6) occurs exactly when, up to null
sets, every section fills its entire allowed interval; the cell is
the corresponding aligned triangle truncated at height \(h_i\).
In particular, since both cells have positive area,
\[
h_1>\frac{11d}{r_1},\qquad
h_3>\frac d{r_3}.
\tag{21}
\]

For every \(0<y<h=\min\{h_1,h_3\}\), the horizontal section of
\(Q\) contains a point of \(C_1\) at or to the left of
\(x=-12-y\) and a point of \(C_3\) at or to the right of \(x=0\).
Convexity of that section forces the whole interval
\([-12-y,0]\), which is precisely the \(Q_{13}\) strip at height
\(y\).  Integration proves (7).  Equality in (7) can occur only if
the \(Q_{13}\)-section is exactly this forced interval for almost
every \(0<y<h\) and \(Q_{13}\) has no positive-area section outside
that common vertical overlap.

Finally, exact arithmetic gives
\[
11d-\frac1{10}
=\frac{112792891}{640000000}>0,
\qquad
4d-\frac1{10}
=\frac{72081}{160000000}>0.
\tag{22}
\]
Equations (8), (21), and (22) imply \(h_1>1/10\) and
\(h_3>1/10\).  Thus (7) yields
\[
d>\frac{12}{10}+\frac1{2\cdot10^2}
=\frac{241}{200}.
\tag{23}
\]
But
\[
d=\frac{16072081}{640000000}<\frac1{20},
\tag{24}
\]
contradicting (23).  Hence no \(K\) with the target \(\rho\)-table
exists for any convex realization of (1).  The contradiction uses
only rational identities and inequalities; SageMath \(10.8\) was
used independently to check the reductions (19)--(20) and all
displayed rational signs.

## External sources

none
