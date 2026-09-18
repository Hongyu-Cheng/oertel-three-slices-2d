---
fact_id: 6cedf2fe59ea9b71
kind: counterexample
author: "mp_r66_rank2_coordinatewise_middle_feasibility"
assurance: LLM-verified
subgoal_id: canonical-all-double-positive-middle-scale-closure
depends_on: ["174b54e9843ef8fc","27839a03c483c90b","29dfdfc94477e532","ed22242313aecf82"]
source_packet_sha256: 0d2ba266acf51622766df8c5727297589b18a2e329c543d66b90b823f1dc09d0
verifier_run: 6f5ae7185fda43ab
target_match: null
---

## Statement

Use the finite-rank-two endpoint conventions of accepted facts 174b54e9843ef8fc, 27839a03c483c90b, 29dfdfc94477e532, and ed22242313aecf82.  Put
\[
f_1(w)=w_1,\qquad f_2(w)=w_2,\qquad
f_3(w)=-1-w_1-w_2,\qquad L_1=L_2=L_3=-37.
\]
Thus, on the two endpoint planes,
\[
p_i=f_i-L_i,\qquad p_1+p_2+p_3=110,
\]
\[
q_i=-f_i-L_i,\qquad q_1+q_2+q_3=112.
\]
Let \(A_0\) be the image, under
\((p_1,p_2)\mapsto(p_1-37,p_2-37)\), of the parallelogram
\[
\mathcal A=\operatorname{conv}\left\{
\left(-\frac1{20},\frac72\right),
\left(-\frac1{20},\frac{207}{2}\right),
\left(\frac{159}{20},\frac{5071}{50}\right),
\left(\frac{159}{20},\frac{71}{50}\right)
\right\},
\]
and let \(A_2\) be the image, under
\((q_1,q_2)\mapsto(-q_1+37,-q_2+37)\), of
\[
\mathcal Q=\operatorname{conv}\left\{
\left(-\frac56,\frac14\right),
\left(-\frac56,\frac{1682}{15}\right),
\left(\frac16,\frac{16781}{150}\right),
\left(\frac16,-\frac1{100}\right)
\right\}.
\]
Let
\[
B=\frac{\mathcal A-\mathcal Q}{2},\qquad
\mathcal T=\{f_1,f_2,f_3\leq0\},\qquad
K_0=\operatorname{conv}(B\cup\mathcal T).
\]
Put
\[
u_i=|\mathcal A\cap\{p_i<0\}|,\qquad
x_i=|\mathcal Q\cap\{q_i<0,\ q_j>0\ (j\ne i)\}|,
\]
\[
q=|\mathcal Q\cap\{q_1,q_2,q_3>0\}|,\qquad
U=u_1+u_2+u_3.
\]
Up to their area-zero boundaries, let \(R_J\) be the middle cell on
which \(f_i\leq0\) exactly for \(i\in J\), and put
\[
r_{123}=|\mathcal T|,\qquad
J_B=|B\cap R_{12}|+|B\cap R_{13}|+|B\cap R_{23}|+2r_{123}.
\]
Writing
\[
c_i^{\rm cr}(k)=\frac{2(M+m+k)}9-u_i-m+x_i,
\qquad c_{i,0}=|K_0\cap\{f_i\leq0\}|,
\]
the single rational value
\[
\Delta=320
\]
satisfies
\[
0<
c_i^{\rm cr}(|K_0|)-c_{i,0}+\frac{2\Delta}{9}
<\Delta
\qquad(i=1,2,3),
\]
and
\[
0<\Delta<M+m-|K_0|.
\]
All three strict marginal ceilings hold, but
\[
J_B<
\frac{M-3m}{3}-U-q.
\]

For the next invariant, put \(H_i=\{f_i\leq0\}\) and define the exact
convex-extension marginal set
\[
\mathcal E_{K_0}(\Delta)=
\left\{
\left(
|(K\setminus K_0)\cap H_1|,
|(K\setminus K_0)\cap H_2|,
|(K\setminus K_0)\cap H_3|
\right):
\begin{array}{l}
K\supseteq K_0\text{ is a compact convex body},\\
|K\setminus K_0|=\Delta
\end{array}
\right\}.
\]
An actual middle extension requires its crossing-increment vector to
belong to \(\mathcal E_{K_0}(\Delta)\).  The coordinatewise hypothesis
only places that vector in \([0,\Delta]^3\).

## Proof

The two displayed endpoint maps preserve area.  The four vertices of
\(\mathcal A\) have \(p_2,p_3>0\).  Its \(p_1<0\) part is a vertical
strip of width \(1/20\) in a parallelogram of width \(8\) and height
\(100\).  Hence
\[
M=800,\qquad (u_1,u_2,u_3)=(5,0,0).
\]

The parallelogram \(\mathcal Q\) has width \(1\) and vertical-edge
length \(6713/60\), so
\[
m=\frac{6713}{60}.
\]
The line \(q_2=0\) meets its lower sloping edge at \(q_1=5/39>0\),
and the line \(q_3=0\) meets its upper sloping edge at
\(q_1=25/222>0\).  Therefore the positive \(Q\)-support is exactly
\(\{123,12,13,23\}\).  Direct triangle areas give
\[
x_1=q_{23}=\frac{6713}{72},\qquad
x_2=q_{13}=\frac1{5200},\qquad
x_3=q_{12}=\frac1{925},
\]
\[
q=q_{123}
=m-x_1-x_2-x_3
=\frac{1291493}{69264}>0.
\]
In particular,
\[
x_1-\frac{5m}{9}-u_1=\frac{5633}{216}>0,
\]
and \(x_2,x_3<4m/9\).  Thus all strict dominant endpoint inequalities
hold.

Exact Minkowski subtraction gives the counterclockwise vertices of
\(B\):
\[
\left(-\frac{13}{120},-\frac{4064}{75}\right),\quad
\left(\frac{527}{120},-\frac{16607}{300}\right),\quad
\left(\frac{527}{120},\frac{10117}{200}\right),\quad
\left(-\frac{13}{120},\frac{10351}{200}\right).
\]
The middle lines have rank two and are pairwise nonparallel and
nonconcurrent, and
\[
\mathcal T=\operatorname{conv}\{(-1,0),(0,-1),(0,0)\},
\qquad |\mathcal T|=\frac12.
\]
Exact orientation tests show that the counterclockwise vertices of
\(K_0\) are
\[
(-1,0),\quad
\left(-\frac{13}{120},-\frac{4064}{75}\right),\quad
\left(\frac{527}{120},-\frac{16607}{300}\right),\quad
\left(\frac{527}{120},\frac{10117}{200}\right),\quad
\left(-\frac{13}{120},\frac{10351}{200}\right).
\]
The determinant formula therefore gives
\[
|B|=\frac{38139}{80},\qquad
k_0:=|K_0|=\frac{15090331}{28800},
\]
\[
M+m-k_0=\frac{11171909}{28800},
\qquad
M+m-k_0-\Delta=\frac{1955909}{28800}>0.
\]

Exact clipping of \(B\) by the three middle halfplanes gives
\[
d_1=\frac{165269}{14400},\qquad
d_2=\frac{98589}{400},\qquad
d_3=\frac{97761}{400}.
\]
Since
\[
\frac{4M-5m}{9}=\frac{31687}{108},
\]
the three marginal slacks are
\[
\frac{4M-5m}{9}-(d_1+u_1-x_1)
=\frac{15990793}{43200}>0,
\]
\[
\frac{4M-5m}{9}-(d_2+u_2-x_2)
=\frac{1647097}{35100}>0,
\]
\[
\frac{4M-5m}{9}-(d_3+u_3-x_3)
=\frac{19579093}{399600}>0.
\]
Thus all three strict marginal ceilings hold.

Exact clipping of \(K_0\) gives
\[
c_{1,0}=\frac{1690829}{28800},\qquad
c_{2,0}=\frac{4871353}{18000},\qquad
c_{3,0}=\frac{9643469}{36000}.
\]
Consequently, for
\[
a_i=c_i^{\rm cr}(k_0)-c_{i,0},
\]
one has
\[
(a_1,a_2,a_3)=
\left(
\frac{61358321}{259200},
-\frac{534379669}{8424000},
-\frac{1454813599}{23976000}
\right).
\]
At the common value \(\Delta=320\), the three required increments are
\[
\left(a_i+\frac{2\Delta}{9}\right)_{i=1}^3
=
\left(
\frac{79790321}{259200},
\frac{64660331}{8424000},
\frac{250146401}{23976000}
\right).
\]
They are all positive.  Their exact upper slacks from \(\Delta\) are
\[
\left(
\frac{3153679}{259200},
\frac{2631019669}{8424000},
\frac{7422173599}{23976000}
\right),
\]
which are also all positive.  This proves all three unsummed
coordinatewise conditions with one and the same \(\Delta\).

For completeness, these increments satisfy even the abstract
noncentral sign-cell incidence constraints.  Their sum minus
\(\Delta\) is
\[
D_*=\frac{49387639}{8311680}>0.
\]
Assign added-cell masses
\[
z_{12}=D_*,\qquad z_{13}=z_{23}=0,
\]
\[
z_1=\frac{4704791227}{15584400},\qquad
z_2=\frac{83137813}{47952000},\qquad
z_3=\frac{250146401}{23976000}.
\]
All six masses are nonnegative, their sum is \(320\), and their three
coordinate marginals are exactly the three displayed required
increments.  Hence neither coordinatewise bounds nor sign-cell
incidence can be the missing condition.  The next actual condition is
membership in \(\mathcal E_{K_0}(320)\), which couples the cell masses
through one spatially convex extension of this fixed \(K_0\).  A sharp
next test is to decide whether the displayed increment vector belongs
to \(\mathcal E_{K_0}(320)\), or to derive a separating inequality for
that set.

Finally, exact clipping of \(B\) into its three double cells gives
\[
|B\cap R_{12}|=\frac{8307767}{1440000},\qquad
|B\cap R_{13}|=\frac{8071583}{1440000},\qquad
|B\cap R_{23}|=\frac{404209}{28800}.
\]
Since \(r_{123}=|\mathcal T|=1/2\),
\[
J_B
=|B\cap R_{12}|+|B\cap R_{13}|+|B\cap R_{23}|+2r_{123}
=\frac{63383}{2400}.
\]
On the other hand,
\[
\frac{M-3m}{3}-U-q
=\frac{45415499}{346320},
\]
and the strict reverse gap is
\[
\frac{M-3m}{3}-U-q-J_B
=\frac{362693321}{3463200}>0.
\]
This completes the exact counterexample verification.

## External sources

none
