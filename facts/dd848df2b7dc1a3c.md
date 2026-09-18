---
fact_id: dd848df2b7dc1a3c
kind: lemma
author: "mp_r373_asym_quad_twofan"
assurance: LLM-verified
subgoal_id: counterexample-sage-exact-cover-search
depends_on: []
source_packet_sha256: 5f79cc28f9f619cd27f9b6720e1449eb2d8618e48499959b892f8ecbef9edeb2
verifier_run: 7dcf25daaa644452
target_match: null
---

## Statement

Let
\[
\begin{aligned}
A_0&=\operatorname{conv}\{(0,0),(1,1/5),(3/5,1/2),(1/10,13/25)\},\\
A_1&=\operatorname{conv}\{(0,0),(3/2,0),(8/5,1/5),(1/2,1),(0,4/5)\},\\
A_2&=\operatorname{conv}\{(0,0),(2,0),(1,3/5),(0,1)\}.
\end{aligned}
\]
Put
\[
q=\frac{2521}{4500},\qquad z_*=\left(\frac12,\frac12\right).
\]
For a nonzero normal \(n\in\mathbb R^2\), define
\[
\mu_n(u,d)=
\left|A_0\cap\{n\cdot z\le u+d\}\right|
+\left|A_1\cap\{n\cdot z\le u\}\right|
+\left|A_2\cap\{n\cdot z\le u-d\}\right|
\]
and its strict-low capacity ceiling
\[
C(n)=\sup\{u\in\mathbb R:\exists d\in\mathbb R,\
\mu_n(u,d)<q\}.
\]
Define
\[
\alpha=\frac{1396+\sqrt{683191}}{1125},
\qquad
\beta=\frac{1304+\sqrt{434791}}{1125}.
\]
Then
\[
\frac53<\beta<\alpha<2
\]
and the following hold.

1. For every real \(t>\beta\),
\[
\boxed{
C(-(1,t))<-\frac{1+t}{2}.
}
\tag{1}
\]
For the downward vertical normal,
\[
\boxed{
C((0,-1))<-\frac12.
}
\tag{2}
\]

2. For every real \(\beta<t<\alpha\),
\[
\boxed{
C((1,t))=\sqrt{\frac{2153t}{4500}}
<\frac{1+t}{2}.
}
\tag{3}
\]

3. Let
\[
\lambda_2,\lambda_3\ge0,\qquad
\lambda_2+\lambda_3>0,\qquad
\mu_j>\beta\lambda_j,
\]
\[
\mu_2+\mu_3<
\alpha(\lambda_2+\lambda_3),
\]
and define the zero-sum triple
\[
\begin{aligned}
n_1&=(\lambda_2+\lambda_3,\mu_2+\mu_3),\\
n_2&=(-\lambda_2,-\mu_2),\\
n_3&=(-\lambda_3,-\mu_3).
\end{aligned}
\tag{4}
\]
Then
\[
\boxed{
C(n_1)+C(n_2)+C(n_3)<0.
}
\tag{5}
\]
The conclusion includes \(\lambda_j=0\), in which case \(n_j\) is a
downward vertical normal.  Thus no constants
\(u_i<C(n_i)\) for a triple (4) can satisfy
\(u_1+u_2+u_3>0\).

## Proof

The exact areas are
\[
|A_0|=\frac{321}{1000}=:m,\qquad
|A_1|=|A_2|=\frac{11}{10}=:M,
\]
so the stated \(q\) is \(2(m+2M)/9\).

For any fixed normal, every polygon cap area is continuous and
nondecreasing in its threshold.  Consequently
\[
E_n(u):=
\min_d\left(
|A_0\cap\{n\cdot z\le u+d\}|
+|A_2\cap\{n\cdot z\le u-d\}|
\right)
\tag{6}
\]
is nondecreasing in \(u\).  It is also continuous.  Indeed, on a
compact \(u\)-interval the cap functions are constant on both tails,
so all minimizers in (6) may be restricted to one compact
\(d\)-interval; continuity then follows from uniform continuity on
that compact set.  Thus
\[
G_n(u):=
|A_1\cap\{n\cdot z\le u\}|+E_n(u)
\tag{7}
\]
is continuous and nondecreasing.  The set in the definition of
\(C(n)\) is therefore an open lower interval.

We first prove (3).  Fix
\(\beta\le t\le\alpha\), put \(L(x,y)=x+ty\), and write
\[
F_j(s)=|A_j\cap\{L\le s\}|.
\]
The endpoint score orders are
\[
0<
p_3:=\frac1{10}+\frac{13t}{25}
<
p_1:=1+\frac t5
<
p_2:=\frac35+\frac t2
\tag{8}
\]
on \(A_0\), and
\[
0<
\zeta_3:=t
<
\zeta_1:=2
<
\zeta_2:=1+\frac{3t}{5}
\tag{9}
\]
on \(A_2\).

For a triangle of area \(B\) with ordered vertex scores
\(0<b<c\), its exact lower-cap function is
\[
\tau_{B,b,c}(s)=
\begin{cases}
0,&s\le0,\\
\displaystyle\frac{Bs^2}{bc},&0\le s\le b,\\
\displaystyle
B\left(1-\frac{(c-s)^2}{c(c-b)}\right),
&b\le s\le c,\\
B,&s\ge c.
\end{cases}
\tag{10}
\]
Triangulating from the origin gives areas
\(19/100,131/1000\) for \(A_0\), and
\(3/5,1/2\) for \(A_2\).  Equations (8)-(10) therefore give exactly
five cap chambers for each endpoint.

Set
\[
c=\sqrt{\frac{2153t}{4500}}.
\tag{11}
\]
Exact algebra gives
\[
2c>p_2,\qquad
c<\min\left\{\frac32,\frac{4t}{5}\right\}.
\tag{12}
\]
The second inequality puts the \(A_1\) cap at \(c\) in the triangle
at the origin, whence
\[
F_1(c)=\frac{c^2}{2t}=\frac{2153}{9000}.
\tag{13}
\]

For every one of the \(5\cdot5\) endpoint chamber pairs, exact real
quantifier elimination tested whether there exist real \(t,c,x\) with
\[
\beta\le t\le\alpha,\qquad
c>0,\qquad4500c^2=2153t,
\]
\[
x\text{ in the selected \(A_0\) chamber},\qquad
2c-x\text{ in the selected \(A_2\) chamber},
\]
\[
F_0(x)+F_2(2c-x)<m.
\tag{14}
\]
The complete Boolean matrix was
\[
\begin{pmatrix}
\mathrm{False}&\mathrm{False}&\mathrm{False}&\mathrm{False}&\mathrm{False}\\
\mathrm{False}&\mathrm{False}&\mathrm{False}&\mathrm{False}&\mathrm{False}\\
\mathrm{False}&\mathrm{False}&\mathrm{False}&\mathrm{False}&\mathrm{False}\\
\mathrm{False}&\mathrm{False}&\mathrm{False}&\mathrm{False}&\mathrm{False}\\
\mathrm{False}&\mathrm{False}&\mathrm{False}&\mathrm{False}&\mathrm{False}
\end{pmatrix}.
\tag{15}
\]
Equality is attained at \(x=2c\): by (12) the \(A_0\) cap is full,
and the \(A_2\) cap at \(0\) has zero area.  Hence the endpoint
infimal convolution at \(c\) is exactly \(m\).  Together with (13),
\[
G_{(1,t)}(c)
=m+\frac{2153}{9000}
=q.
\tag{16}
\]
For \(u<c\) sufficiently close to \(c\), take \(d=u\).  Then the
\(A_0\) cap remains full, the \(A_2\) cap is zero, and the middle cap
has area \(u^2/(2t)<2153/9000\).  Equations (7) and (16) therefore
prove the equality in (3).  Finally,
\[
\sqrt{\frac{2153t}{4500}}
<\sqrt t
\le\frac{1+t}{2},
\]
which proves its strict center-score inequality.

We next prove (1).  Fix \(t\ge\beta\) and continue to use
\(L(x,y)=x+ty\).  For \(j=0,1,2\), define the upper cap
\[
U_j(s;t)=|A_j\cap\{L\ge s\}|.
\]
For \(n=-(1,t)\), the center score is
\[
u_*=-\frac{1+t}{2}.
\]
Putting \(w=-u_*\), the minimum mass of a row whose middle boundary
passes through \(z_*\) is
\[
U_1(w;t)+
\min_x\bigl(U_0(x;t)+U_2(1+t-x;t)\bigr).
\tag{17}
\]

Use the endpoint scores
\[
p_1=1+\frac t5,\qquad
p_2=\frac35+\frac t2,\qquad
p_3=\frac1{10}+\frac{13t}{25},
\]
\[
\zeta_1=2,\qquad
\zeta_2=1+\frac{3t}{5},\qquad
\zeta_3=t.
\]
All endpoint and middle score-order changes on \(t\ge\beta\) occur at
\[
2,\qquad\frac52,\qquad\frac{45}{16},
\qquad\frac{11}{3},\qquad25.
\]
They give exactly the following six chambers.  Adjacent formulas agree
at every nondegenerate shared boundary.  At \(t=5/2\) and \(t=25\),
two vertex scores of one endpoint triangle coincide; those two rational
degenerate boundaries are audited separately below.
\[
\begin{array}{c|c|c|c}
t\text{-range}&A_0\text{ positive-score order}
&A_2\text{ positive-score order}
&|A_1\cap\{L\le(1+t)/2\}|\\ \hline
[\beta,2]&p_3\le p_1<p_2&\zeta_3\le\zeta_1<\zeta_2
&\dfrac{(t+1)^2}{8t}\\[2mm]
[2,5/2]&p_3<p_1<p_2&\zeta_1\le\zeta_3<\zeta_2
&\dfrac{13t^2-4t+1}{8t(2t+1)}\\[2mm]
[5/2,45/16]&p_3\le p_1<p_2&\zeta_1<\zeta_2\le\zeta_3
&\dfrac{13t^2-4t+1}{8t(2t+1)}\\[2mm]
[45/16,11/3]&p_1\le p_3<p_2&\zeta_1<\zeta_2<\zeta_3
&\dfrac{13t^2-4t+1}{8t(2t+1)}\\[2mm]
[11/3,25]&p_1<p_3\le p_2&\zeta_1<\zeta_2<\zeta_3
&\dfrac{233t^2-356t-55}{40t(8t-11)}\\[2mm]
[25,\infty)&p_1<p_2\le p_3&\zeta_1<\zeta_2<\zeta_3
&\dfrac{233t^2-356t-55}{40t(8t-11)}.
\end{array}
\tag{18}
\]

On the nondegenerate part of each row of (18), triangulation and (10)
give exactly five global score chambers for \(U_0\) and five for
\(U_2\).  For every one of the \(6\cdot5\cdot5=150\) cells, exact real
quantifier elimination tested whether there exist \(t,x\) in that cell
such that
\[
U_0(x;t)+U_2(1+t-x;t)+U_1((1+t)/2;t)
\le q+\frac1{20}.
\tag{19}
\]
For each of the six parameter chambers, the resulting \(5\)-by-\(5\)
matrix was the literal matrix
\[
\begin{pmatrix}
\mathrm{False}&\mathrm{False}&\mathrm{False}&\mathrm{False}&\mathrm{False}\\
\mathrm{False}&\mathrm{False}&\mathrm{False}&\mathrm{False}&\mathrm{False}\\
\mathrm{False}&\mathrm{False}&\mathrm{False}&\mathrm{False}&\mathrm{False}\\
\mathrm{False}&\mathrm{False}&\mathrm{False}&\mathrm{False}&\mathrm{False}\\
\mathrm{False}&\mathrm{False}&\mathrm{False}&\mathrm{False}&\mathrm{False}
\end{pmatrix}.
\tag{20}
\]
Together with the exact \(t=5/2\) and \(t=25\) audits in (23), this
proves, uniformly for every \(t\ge\beta\),
\[
G_{-(1,t)}\left(-\frac{1+t}{2}\right)
>q+\frac1{20}.
\tag{21}
\]
Continuity and monotonicity from (7) imply that the strict-low capacity
ceiling lies strictly below this center score.  This proves (1), with
a uniform positive mass margin at the tested score.

The downward vertical case is an exact rational boundary audit.  For
\(n=(0,-1)\), the endpoint infimal convolution at \(u_*=-1/2\) is
\[
\frac{38997}{157000},
\]
attained at the upper-\(y\) threshold \(247/785\) on \(A_0\), while
the middle upper cap has area
\[
\frac{119}{320}.
\]
Therefore
\[
G_{(0,-1)}(-1/2)-q
=\frac{678707}{11304000}
>\frac1{20}.
\tag{22}
\]
Again continuity gives (2).

For an independent exact boundary audit, SageMath over \(\mathbb Q^2\)
enumerated every endpoint breakpoint and every stationary point of
the active rational quadratic on each interval.  It returned:
\[
\begin{array}{c|c|c|c}
t&\min_x(U_0+U_2)&U_1&G_{-(1,t)}(u_*)-q\\ \hline
2&40027/187000&43/80&644003/3366000\\
5/2&4241/21000&239/480&35191/252000\\
45/16&6109/29000&3655/7632&1192751/9222000\\
11/3&443907/1967000&97/220&20712589/194733000\\
25&223411/916000&7123/18900&10483447/173124000
\end{array}
\tag{23}
\]
Every entry in the last column is strictly above \(1/20\), consistent
with (20)-(21).  Equation (22) is the corresponding exact vertical
boundary audit.

It remains to prove (5).  Capacity is positively homogeneous:
\[
C(\rho n)=\rho C(n)\qquad(\rho>0),
\tag{24}
\]
because scaling \(n,u,d\) by \(\rho\) leaves every halfspace section
unchanged.

Put
\[
\Lambda=\lambda_2+\lambda_3,\qquad
\mathsf M=\mu_2+\mu_3,\qquad
t_1=\frac{\mathsf M}{\Lambda}.
\]
The hypotheses in (4) give
\[
\beta<t_1<\alpha.
\]
Thus (3) and (24) imply
\[
C(n_1)-n_1\cdot z_*<0.
\tag{25}
\]
If \(\lambda_j>0\), put \(t_j=\mu_j/\lambda_j>\beta\).  Then
\[
n_j=\lambda_j(-(1,t_j)),
\]
so (1) and (24) give
\[
C(n_j)-n_j\cdot z_*<0.
\tag{26}
\]
If \(\lambda_j=0\), then
\[
n_j=\mu_j(0,-1),
\]
and (2) gives the same strict inequality.

Finally, \(n_1+n_2+n_3=0\), so
\[
\sum_{i=1}^3n_i\cdot z_*=0.
\]
Adding (25)-(26) yields
\[
\sum_{i=1}^3C(n_i)
=
\sum_{i=1}^3\bigl(C(n_i)-n_i\cdot z_*\bigr)
<0,
\]
which is (5).

All \(150\) cell queries in (19), all endpoint order assertions in
(18), and the positive-chamber \(25\)-cell audit in (14) were run with
local Wolfram Kernel \(14.3.0\) using exact `Resolve` over the reals.
Every cell returned the stated literal Boolean, and none timed out.
The rational boundary table (23) and vertical calculation (22) were
independently rerun with SageMath \(10.8\), using
`Polyhedron(..., base_ring=QQ)`, exact breakpoint enumeration, and
exact stationary points.  No randomized computation or external
source is used.

## External sources

none
