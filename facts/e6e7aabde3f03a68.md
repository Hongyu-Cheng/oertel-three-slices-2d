---
fact_id: e6e7aabde3f03a68
kind: lemma
author: "/root/mp_r53_extreme_ratios"
assurance: LLM-verified
subgoal_id: canonical-all-double-positive-middle-scale-closure
depends_on: ["0009896ebff12f31","084bf2f472bf29c7","444fb905d0cc5122","6aa12d1b76699246","c49613ac26c0c4a8","edf57cbc053c4a13"]
source_packet_sha256: 8d1a8928548175f03590aa665bd3312a151e2ca90db9bed51e77f8db891d8638
verifier_run: 693b4c5ab2b343da
target_match: null
---

## Statement

Let
\[
\lambda_1,\lambda_2,\lambda_3>0,\qquad
R=\lambda_1+\lambda_2+\lambda_3,
\]
and assume the \(\mathcal B_{12\mid3}\) face with \(\lambda_1\) relabeled as the unique dominant coordinate:
\[
\sqrt{\lambda_1}-\sqrt{\lambda_2}
\geq\sqrt{1+3\lambda_3}.
\tag{1}
\]
Assume the accepted cap constraints
\[
4\lambda_1\lambda_2\lambda_3\leq1+R,
\qquad
\sqrt{\lambda_1}+\sqrt{\lambda_2}+\sqrt{\lambda_3}
\leq\frac32\sqrt{1+R},
\tag{2}
\]
and the closed survivor condition
\[
\delta(\lambda_1,\lambda_2,\lambda_3)\leq\tau(R),
\qquad
\tau(R)=
\frac{49}{
\left(\sqrt{1+R}+\sqrt{204+120R}\right)^2},
\tag{3}
\]
where \(\delta\) is the seven-term function of accepted fact
`6aa12d1b76699246`.

Define
\[
z=\frac1{\sqrt{1+R}},\qquad
u_i=z\sqrt{\lambda_i}\quad(i=1,2,3),\qquad
v=\sqrt{120+84z^2},
\tag{4}
\]
\[
\pi=u_1u_2u_3,\qquad
Q_2=u_1^2u_2^2+u_1^2u_3^2+u_2^2u_3^2,
\]
\[
\mathcal A=(1+v)^2,\qquad
\mathcal C=\mathcal A-49z^2,\qquad
n=z^2-2\pi,\qquad
B_k=2\pi+z^2u_k.
\tag{5}
\]
Then \(z,u_1,u_2,u_3,v>0\), \(\mathcal C>0\), and the ratios in
(1)-(3) are in exact bijection with the union of the following three
semialgebraic systems.

All three systems contain the common base
\[
z^2+u_1^2+u_2^2+u_3^2=1,\qquad
v^2=120+84z^2,
\tag{6}
\]
\[
u_1>u_2,\qquad
(u_1-u_2)^2\geq z^2+3u_3^2,
\tag{7}
\]
\[
4\pi^2\leq z^4,\qquad
2(u_1+u_2+u_3)\leq3.
\tag{8}
\]
They also satisfy the strict accepted consequence
\[
2u_2^2u_3^2<z^4.
\tag{9}
\]
The three alternatives are
\[
\mathcal H_0:\qquad
3\pi^2\mathcal A\leq49z^4Q_2,
\tag{10}
\]
\[
\mathcal H_2:\qquad
u_2\leq u_3,\qquad
n^2\mathcal A\geq\mathcal C B_2^2,
\tag{11}
\]
\[
\mathcal H_3:\qquad
u_3\leq u_2,\qquad
n^2\mathcal A\geq\mathcal C B_3^2.
\tag{12}
\]
Conversely, every positive solution of the common base and at least one of
(10)-(12) gives by
\[
\lambda_i=\frac{u_i^2}{z^2}
\tag{13}
\]
a point satisfying exactly (1)-(3).  Thus (10)-(12) are exhaustive; when
\(u_2=u_3\), the two minor-cap systems overlap harmlessly.

For a full positive-middle \(W=0\) common-plane realization, every
non-strict survivor inequality selected in (10)-(12) can be taken strict,
and its determinant satisfies
\[
D\mathcal A<49z^2.
\tag{14}
\]
For each of the three ratio systems, substitute \(q=1\) and
\(x_i=u_i^2/z^2\) into accepted fact `c49613ac26c0c4a8` and choose one of
its eight endpoint-pair strata.  After clearing powers of the positive
\(z\) and the positive side gaps, the displayed normal-form equations and
convex-order inequalities are polynomial.  Hence the full face has an
exact reduction to \(3\cdot8=24\) explicit unequal-cap normal-form systems,
with (14) appended as the strict common-plane scale condition.

The ratio defect \(\epsilon\) of accepted fact `0009896ebff12f31` is zero
on this face, so that fact alone does not lower \(\tau\).  Nevertheless,
accepted fact `444fb905d0cc5122` implies that no sequence of realizations
inside these 24 systems can have \(\eta/q\to0\); the remaining systems
necessarily retain a nonvanishing \(P/R\)-defect.  This is a finite
reduction, not a claim that any one of the 24 necessary systems extends to
a full common-plane realization.

## Proof

Accepted fact `edf57cbc053c4a13` identifies (1) as one of the exact
zero-defect faces, proves that the dominant coordinate is unique, and gives
(2), with the square-root inequality in fact strict on this face.  The
change of variables (4) has the inverse (13).  Since
\[
1+R=\frac1{z^2},
\]
it gives (6), while (1) becomes (7).  The two cap inequalities become
\[
4u_1^2u_2^2u_3^2\leq z^4,\qquad
u_1+u_2+u_3\leq\frac32,
\]
which is (8).  The strict minor-product conclusion of the same accepted
fact is
\[
\lambda_2\lambda_3<\frac12,
\]
and this is exactly (9).  Conversely, reversing these calculations proves
that every positive solution of (6)-(8) gives (1)-(2).  Thus (4) is an
exact compactification of the positive face; replacing positivity by
nonnegativity gives its compact boundary closure.

In these variables, (3) becomes
\[
\tau(R)=\frac{49z^2}{(1+v)^2}
=\frac{49z^2}{\mathcal A}.
\tag{15}
\]
The function
\[
\frac{z}{1+\sqrt{120+84z^2}}
\]
is strictly increasing for \(z>0\), because its derivative has the sign of
\[
1+\frac{120}{\sqrt{120+84z^2}}>0.
\]
Since \(0<z<1\),
\[
0<\tau(R)
<
\frac{49}{(1+\sqrt{204})^2}
<
\frac{64}{289}
<1.
\tag{16}
\]
The middle comparison follows from
\[
111^2<64\cdot204.
\]
In particular, \(\mathcal C=\mathcal A(1-\tau)>0\).

We now specialize every term of \(\delta\).  The harmonic term is
\[
d_0
=
\min\left\{
1,\
\frac{3\pi^2}{z^2Q_2}
\right\}.
\tag{17}
\]
For every \(k\), the ratio
\[
\frac{c_k^2}{A_k}
=\frac{4\lambda_1\lambda_2\lambda_3}{1+R}
=\frac{4\pi^2}{z^4}
=:y
\tag{18}
\]
is independent of \(k\).  Consequently all three \(d_{1k}\) coincide:
\[
d_1=\frac{4y}{(1+y)^2}
=\frac{16\pi^2z^4}{(z^4+4\pi^2)^2}.
\tag{19}
\]
The product inequality in (8) says \(0<y\leq1\).

For the three clipped terms, direct substitution gives
\[
\frac{\sqrt{A_k}-c_k}{1+c_k}
=
\frac{z^2-2\pi}{2\pi+z^2u_k}
=\frac n{B_k}.
\tag{20}
\]
The product inequality gives \(n\geq0\).  Hence the function
\[
d_{2k}=1-\operatorname{clip}(n/B_k)^2
\]
is nondecreasing in \(u_k\): the numerator is common, \(B_k\) is
increasing in \(u_k\), and \(1-\operatorname{clip}(s)^2\) is
nonincreasing for \(s\geq0\).  Since \(u_1\) is the unique dominant
coordinate,
\[
d_{21}\geq\min\{d_{22},d_{23}\}.
\tag{21}
\]
More precisely, the minimum clipped term is \(d_{22}\) when
\(u_2\leq u_3\), and it is \(d_{23}\) when \(u_3\leq u_2\).

The common \(d_1\) term never supplies an additional survivor branch.
Let
\[
w=\min\{u_2,u_3\},
\]
and suppose the corresponding minimum clipped term is larger than
\(\tau\).  From (20),
\[
1-\operatorname{clip}(n/(2\pi+z^2w))^2>\tau>0.
\]
Thus
\[
\frac n{2\pi+z^2w}<1,
\]
and therefore
\[
4\pi>z^2(1-w).
\tag{22}
\]
Also \(w<1/2\): if the other minor coordinate is \(w'\geq w\), then
\[
u_1+w'+w>3w,
\]
whereas (8) gives \(u_1+w'+w\leq3/2\).  Equation (22) now yields
\[
\pi>\frac{z^2}{8},
\qquad
y=\frac{4\pi^2}{z^4}>\frac1{16}.
\]
The function \(4y/(1+y)^2\) is increasing on \(0<y\leq1\), so
\[
d_1>\frac{64}{289}>\tau
\tag{23}
\]
by (16).

It follows from (21)-(23) that
\[
\delta\leq\tau
\quad\Longleftrightarrow\quad
d_0\leq\tau
\ \text{or}\
\begin{cases}
d_{22}\leq\tau,&u_2\leq u_3,\\
d_{23}\leq\tau,&u_3\leq u_2.
\end{cases}
\tag{24}
\]
Indeed, the reverse implication is immediate.  For the forward
implication, if the minimum clipped term exceeds \(\tau\), then (21) and
(23) put every clipped term and \(d_1\) above \(\tau\), leaving only
\(d_0\).

Because \(\tau<1\), equations (15) and (17) show that
\[
d_0\leq\tau
\quad\Longleftrightarrow\quad
3\pi^2\mathcal A\leq49z^4Q_2,
\]
which is (10).  Also \(0<1-\tau=\mathcal C/\mathcal A<1\).  With
\(n/B_k\geq0\), equation (20) gives the exact equivalence
\[
d_{2k}\leq\tau
\quad\Longleftrightarrow\quad
n^2\mathcal A\geq\mathcal C B_k^2.
\tag{25}
\]
The right side of (25) automatically forces \(n>0\).  Combining
(24)-(25) proves the exhaustive three-system reduction (10)-(12), and
also proves its converse.  Every inequality used was non-strict except
for consequences already strict on the positive face, so all boundaries
listed in the statement remain present.

Finally suppose a full positive-middle \(W=0\) common-plane realization
exists.  Accepted fact `084bf2f472bf29c7`, applied with
\[
U=|\mathcal T_Q|=\frac qD,
\]
gives \(D<\tau(R)\), while accepted fact `6aa12d1b76699246` gives
\(D\geq\delta\).  Hence \(\delta<\tau\), so one selected alternative in
(10)-(12) is strict, and (15) gives (14).

Accepted fact `c49613ac26c0c4a8` is an exact finite union over eight
endpoint-pair strata for every prescribed positive ratio triple.  Its
substitution described in the statement therefore gives exactly 24
necessary \(A_2\)-normal-form systems and retains coincident endpoints,
collinear labels, redundant labels, and cutting-line boundaries.  On the
face (1), accepted facts `edf57cbc053c4a13` and `0009896ebff12f31` give
\(\epsilon=0\), so no positive ratio-defect threshold is available.
However, if a sequence of full realizations in the reduced systems had
\(\eta/q\to0\), then
\[
0\leq\frac{r_{123}}q\leq\frac{\eta}{6q}\longrightarrow0,
\]
contradicting accepted fact `444fb905d0cc5122`.  This proves the final
nondegeneration assertion and completes the finite reduction.

## External sources

none
