---
fact_id: 18ec957fdaeb4b8d
kind: lemma
author: "mp_r395_onezero_q_realizer"
assurance: LLM-verified
subgoal_id: counterexample-opposite-asymmetric-low-r
depends_on: ["9aa5e8e4ddcd1c62"]
source_packet_sha256: 51fd874fc92351cc7bd5af23ea61fb13699fa421b8711229c55135aacae8263e
verifier_run: a7b3f2b4826b4c87
target_match: null
---

## Statement

Use the endpoint datum and the common-plane exact-cell convention of accepted fact `9aa5e8e4ddcd1c62`.  Put
\[
D=16072081,\qquad
\gamma=\frac{320000}{D},\qquad
d=\frac{D}{640000000}.
\]
Thus \(\gamma d=1/2000\).  In shifted affine coordinates
\[
s=q_1,\qquad t=q_2,\qquad q_3=-12-s-t
\tag{1}
\]
define the following rational numbers:
\[
h_-=\frac3{1250},\qquad
h_+=\frac{283}{125000},\qquad
\alpha=\frac{1943}{1000000},
\]
\[
C_-=12\alpha-\frac{\alpha^2}{2},\qquad
\eta=\frac{2(d-C_-)}{12-\alpha},\qquad
\beta=\alpha+\eta=\frac{8610961}{3839378240},
\tag{2}
\]
\[
G_0=\frac{6d}{\alpha},\qquad
L_0=-12-G_0=-\frac{55677363}{621760},
\]
\[
G_+=\frac{22d}{h_+}-G_0,\qquad
L_+=-12-h_+-G_+
=-\frac{785131799042953}{4398952000000},
\qquad L_-=7,
\tag{3}
\]
\[
z=\frac{1761}{1000000},\qquad
R_0=\frac{2d}{z}=\frac{16072081}{563520},
\]
\[
C_+=12h_++\frac{h_+^2}{2},\qquad
R_+=\frac{2(d-C_+)}{h_+-z}
=-\frac{4115872571}{503000000},
\]
\[
A_-=\frac{L_-(h_--\beta)}2,\qquad
R_-=\frac{2(3d+A_-)}{h_-}-R_0
=\frac{187793201635282937}{5408916064512\cdot1000}.
\tag{4}
\]
Let \(\mathcal Q\) be the convex hull, in the displayed counterclockwise order, of
\[
\begin{aligned}
&(L_-,-h_-),\ (R_-,-h_-),\ (R_0,0),\ (0,z),\
(R_+,h_+),\\
&(L_+,h_+),\ (L_0,0),\
(-12+\alpha,-\alpha),\ (0,-\beta).
\end{aligned}
\tag{5}
\]
Then \(\mathcal Q\) is a compact two-dimensional rational convex polygon of coordinate area \(20d=D/32000000\).  Its exact sign-cell areas for (1) are
\[
\begin{array}{c|rrrrrrr}
H&1&2&3&12&13&23&123\\ \hline
|\mathcal Q_H|&
11d&0&d&3d&d&3d&d .
\end{array}
\tag{6}
\]
Its three cutting chords have the exact support incidences
\[
\mathcal Q\cap\{q_1=0\}
=[(0,-\beta),(0,z)],
\tag{7}
\]
\[
\mathcal Q\cap\{q_2=0\}
=[(L_0,0),(R_0,0)],
\tag{8}
\]
\[
\mathcal Q\cap\{q_3=0\}
=[(-12+\alpha,-\alpha),(-12-h_+,h_+)].
\tag{9}
\]

More concretely, take physical coordinates
\[
(X,Y)=(\gamma s,t),
\]
put
\[
L_1=L_2=0,\qquad L_3=-11,
\]
\[
f_1(X,Y)=X/\gamma,\qquad
f_2(X,Y)=Y,\qquad
f_3(X,Y)=-1-X/\gamma-Y,
\tag{10}
\]
and let \(A_2\) have the nine rational vertices
\[
(\gamma s,t)\qquad ((s,t)\text{ listed in }(5)).
\tag{11}
\]
Then \(f_1+f_2+f_3=-1\), \(L_1+L_2+L_3=-11\), hence \(\delta=10\), and the inverse area Jacobian of both the \((\pi_1,\pi_2)\)- and \((q_1,q_2)\)-charts is \(\gamma\).  The physical exact-cell areas of \(A_2\) are therefore precisely
\[
\begin{array}{c|rrrrrrr}
H&1&2&3&12&13&23&123\\ \hline
q_H&
\frac{11}{2000}&0&\frac1{2000}&
\frac3{2000}&\frac1{2000}&\frac3{2000}&\frac1{2000}.
\end{array}
\tag{12}
\]
Together with the rational triangle \(C_0\) already realized in accepted fact `9aa5e8e4ddcd1c62`, this gives simultaneous endpoint polygons in one common affine fan.

## Proof

It is useful first to expose the convex profile encoded by (5).  For
\(-h_-\leq t\leq h_+\), write
\[
\mathcal Q\cap\{q_2=t\}
=\{(s,t):L(t)\leq s\leq R(t)\}.
\tag{13}
\]
The left endpoint \(L\) is the piecewise-affine function through
\[
(-h_-,L_-),\quad(-\beta,0),\quad
(-\alpha,-12+\alpha),\quad(0,L_0),\quad(h_+,L_+),
\tag{14}
\]
and the right endpoint \(R\) is the piecewise-affine function through
\[
(-h_-,R_-),\quad(0,R_0),\quad(z,0),\quad(h_+,R_+).
\tag{15}
\]
All breakpoints and values are rational.  In the order in (14), the four exact slopes are
\[
-\frac{479922280000}{10777621},\quad
-\frac{143953371775249}{3597028374},\quad
-\frac{150679534624}{3775249},\quad
-\frac{391214455817953}{9959227328},
\tag{16}
\]
and they are strictly increasing.  In the order in (15), the three exact slopes are
\[
-\frac{55877010796648895}{21635664258048},\quad
-\frac{50225253125}{3101121},\quad
-\frac{4115872571}{253009},
\tag{17}
\]
and they are strictly decreasing.  These orders follow by direct cross multiplication of positive denominators.  Thus \(L\) is convex and \(R\) is concave.  Moreover \(R_- > L_-\) and \(R_+>L_+\); hence the concave width \(R-L\) is positive throughout the interval.  This proves that (13), equivalently (5), is a compact two-dimensional convex polygon and that every point displayed in (5) is an extreme vertex.

The same exact arithmetic gives
\[
0<\alpha<\beta<h_-,\qquad 0<z<h_+,
\tag{18}
\]
\[
L_+<-12-h_+<R_+<0<R_0,\qquad
L_0<-12<0<L_-<R_-.
\tag{19}
\]
On the lower profile, \(L\) meets \(q_1=0\) at
\((0,-\beta)\) and meets \(q_3=0\), equivalently
\(s=-12-t\), at \((-12+\alpha,-\alpha)\).  On the upper profile,
\(R\) meets \(q_1=0\) at \((0,z)\), while the top edge meets
\(q_3=0\) at \((-12-h_+,h_+)\).  The horizontal section at \(t=0\)
has endpoints \((L_0,0),(R_0,0)\).  Convexity and (18)--(19) now give
exactly the three chord identities (7)--(9), with no additional
intersection with any cutting line.

The open chamber \(Q_2\) is empty.  Indeed every point of \(\mathcal Q\)
has \(t\geq-h_->-12\).  If additionally \(s>0\) and \(t\leq0\), then
\[
q_3=-12-s-t<-12+h_-<0,
\]
so the point is in \(Q_{23}\), not \(Q_2\).  This proves the zero entry
in (6) as a literal empty-cell assertion, not merely a zero-area one.

We now compute the remaining six areas.  Cutting lines are null, so
weak versus strict signs do not affect these computations.

On \(0\leq t\leq h_+\), the left boundary lies strictly to the left of
\(s=-12-t\).  Its gaps from this line at the two endpoints are \(G_0\)
and \(G_+\).  Therefore
\[
|\mathcal Q_1|
=\frac{h_+(G_0+G_+)}2=11d
\tag{20}
\]
by the definition of \(G_+\).

On \(-\alpha\leq t\leq0\), the gap between \(s=-12-t\) and the left
boundary grows affinely from \(0\) to \(G_0\).  Hence
\[
|\mathcal Q_{12}|=\frac{\alpha G_0}{2}=3d.
\tag{21}
\]
The central lower cell has two pieces.  Between \(-\beta\) and
\(-\alpha\), its area is the triangle
\[
\frac{(\beta-\alpha)(12-\alpha)}2
=\frac{\eta(12-\alpha)}2=d-C_-.
\]
Between \(-\alpha\) and \(0\), its width is \(12+t\), so its area is
\[
\int_{-\alpha}^{0}(12+t)\,dt=C_-.
\]
Thus
\[
|\mathcal Q_{123}|=d.
\tag{22}
\]

The positive part of the lower left endpoint occurs only on
\([-h_-,-\beta]\); it is a triangle of area \(A_-\).  The whole
integral under the positive lower right endpoint is
\[
\int_{-h_-}^{0}R(t)\,dt
=\frac{h_-(R_-+R_0)}2=3d+A_-.
\]
Subtracting the positive-left triangle gives
\[
|\mathcal Q_{23}|=3d.
\tag{23}
\]

On the upper right boundary, \(R\) decreases affinely from \(R_0\) to
\(0\) on \([0,z]\).  Thus
\[
|\mathcal Q_3|=\frac{zR_0}{2}=d.
\tag{24}
\]
For the upper central cell, first integrate the full central width
\(12+t\) over \([0,h_+]\), obtaining \(C_+\).  On \([z,h_+]\), the
negative right boundary removes the signed triangular area
\[
\frac{R_+(h_+-z)}2=d-C_+.
\]
Consequently
\[
|\mathcal Q_{13}|=C_++(d-C_+)=d.
\tag{25}
\]
Equations (20)--(25), together with the empty \(Q_2\), prove (6) and
\[
|\mathcal Q|=(11+1+3+1+3+1)d=20d.
\tag{26}
\]

As an independent exact audit, SageMath 10.8 was run with
`sage --nodotsage` and `Polyhedron(base_ring=QQ)`.  The polygon (5)
was clipped by the three rational halfspace pairs
\[
q_1\lesseqgtr0,\qquad q_2\lesseqgtr0,\qquad
q_3=-12-q_1-q_2\lesseqgtr0.
\]
The exact coordinate output was
\[
\begin{array}{c|rrrrrrr}
H&1&2&3&12&13&23&123\\ \hline
|\mathcal Q_H|&
\frac{176792891}{640000000}&0&
\frac{16072081}{640000000}&
\frac{48216243}{640000000}&
\frac{16072081}{640000000}&
\frac{48216243}{640000000}&
\frac{16072081}{640000000},
\end{array}
\]
and the total was \(16072081/32000000\).  The same exact run checked
all slope orders in (16)--(17), compactness, dimension two, and the
three chord incidences.

Finally, the map \((s,t)\mapsto(\gamma s,t)\) has determinant
\(\gamma\).  Thus physical area is \(\gamma\) times coordinate area,
and \(\gamma d=1/2000\) turns (6) into (12).  Equations (10) give
\[
\pi_1=s,\qquad \pi_2=t,\qquad \pi_3=10-s-t
\]
and simultaneously give (1) for the \(Q\)-chart.  Therefore the
accepted \(P\)-triangle realization in `9aa5e8e4ddcd1c62` and the
polygon just proved use exactly the same affine functions, offsets,
\(\delta\), and area Jacobian.  This proves the simultaneous endpoint
claim.

## External sources

none
