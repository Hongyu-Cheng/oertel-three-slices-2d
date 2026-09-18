---
fact_id: e46ceefe535e9fa0
kind: lemma
author: "mp_r409_infinite_tail_d0large"
assurance: LLM-verified
subgoal_id: canonical-tail-exclusion
depends_on: ["15bb2c1680a0254e"]
source_packet_sha256: d2004c3a50fa1460126e80b0bb71b53802fc280dbdbfaafdfecc16c539dab1e7
verifier_run: 16c35a9dbf694e8a
target_match: null
---

## Statement

Let
\[
\mathcal A=\left\{\lambda\in\mathbb R^3:
\lambda_1+\lambda_2+\lambda_3=1\right\},
\qquad
\Delta=\operatorname{conv}\{e_1,e_2,e_3\}\subset\mathcal A,
\qquad
g=\frac13(1,1,1),
\]
and normalize planar area so that \(|\Delta|=1\).  Let
\[
u\geq v>0,\qquad P\in\mathcal A,
\]
and define
\[
A_0=P+u(\Delta-g),\qquad
A_2=P+v(\Delta-g),\qquad
K=\Delta.
\tag{1}
\]
Assume
\[
\frac{A_0+A_2}{2}\subseteq K.
\tag{2}
\]
Thus
\[
M=|A_0|=u^2,\qquad
m=|A_2|=v^2,\qquad
k=|K|=1.
\tag{3}
\]
Assume that this area triple lies in the exact strict residual domain
of accepted fact `15bb2c1680a0254e`, and impose the remaining
large-\(D_0\) condition
\[
D_0=\frac{2M-m-k}{3}
=\frac{2u^2-v^2-1}{3}>v^2=m.
\tag{4}
\]

Choose
\[
0\leq s_j\leq1\quad(j=1,2,3),
\qquad
s_1+s_2+s_3<1,
\tag{5}
\]
put
\[
d=1-s_1-s_2-s_3>0,
\qquad
f_j(\lambda)=\frac{s_j-\lambda_j}{d},
\tag{6}
\]
and set
\[
t=\frac{2(M+m+k)}9=\frac{2(1+u^2+v^2)}9,
\tag{7}
\]
\[
c_j=|K\cap\{f_j\leq0\}|,
\tag{8}
\]
\[
\mu_j(a)
=c_j+|A_0\cap\{f_j\leq a\}|
       +|A_2\cap\{f_j\leq-a\}|,
\qquad
I_j=\{a\in\mathbb R:\mu_j(a)<t\}.
\tag{9}
\]
Then the \(f_j\) are nonconstant with pairwise nonparallel linear
parts and
\[
f_1+f_2+f_3=-1.
\tag{10}
\]
For every \(q\in\{1,2,3\}\),
\[
c_q+m<t
\quad\Longrightarrow\quad
I_i=\varnothing
\quad\text{for some }i\ne q.
\tag{11}
\]
Hence the registered tail-exclusion implication holds throughout the
whole \(D_0>m\) portion of the family (1), for every barycentric
edge-support profile (5)-(6).

## Proof

We first record the exact geometry forced by compatibility.  Since
\(\Delta-g\) is convex,
\[
\frac{A_0+A_2}{2}
=P+\frac{u+v}{2}(\Delta-g).
\tag{12}
\]
The minimum of the \(j\)-th coordinate on the right side is
\[
P_j-\frac{u+v}{6}.
\]
All its points have coordinate sum \(1\), so (2) is equivalent to
\[
P_j\geq\frac{u+v}{6}
\qquad(j=1,2,3).
\tag{13}
\]
Summing (13) gives
\[
u+v\leq2.
\tag{14}
\]

The strict residual domain in accepted fact `15bb2c1680a0254e`
contains
\[
M-m<k.
\]
For (3), this is
\[
u^2-v^2<1.
\tag{15}
\]
Only (13)-(15), not the sign of \(m-D_0\), will be used below.

We next compute every row profile exactly.  From (6),
\[
K\cap\{f_j\leq0\}
=\Delta\cap\{\lambda_j\geq s_j\}.
\]
For \(0\leq s_j\leq1\), this is the corner triangle similar to
\(\Delta\) by factor \(1-s_j\), including all of \(\Delta\) at
\(s_j=0\) and the support vertex at \(s_j=1\).  Therefore
\[
c_j=(1-s_j)^2.
\tag{16}
\]

For \(c>0\), write
\[
[x]_c=\min\{c,\max\{0,x\}\}.
\tag{17}
\]
A point of \(A_0\) has the form
\[
\lambda=P+u(\eta-g),\qquad\eta\in\Delta.
\]
Consequently the cap
\[
A_0\cap\{\lambda_j\geq\tau\}
\]
has area
\[
\left[P_j+\frac{2u}{3}-\tau\right]_u^2.
\tag{18}
\]
Indeed, between its two support values the cap is a corner triangle
whose two edge ratios are the raw side length divided by \(u\);
multiplication by \(|A_0|=u^2\) gives the square in (18).
The two clamps in (17) give respectively the empty and full cap.
The same formula holds for \(A_2\), with \(u\) replaced by \(v\).
Thus support edges, empty caps, and full caps are already part of
(18).

Fix \(j\) and \(a\in\mathbb R\), and put
\[
x=P_j+\frac{2u}{3}-s_j+da.
\tag{19}
\]
The raw side length of the \(A_2\)-cap in (9) is then
\[
P_j+\frac{2v}{3}-s_j-da=R_j-x,
\]
where
\[
R_j=2\left(P_j+\frac{u+v}{3}-s_j\right).
\tag{20}
\]
As \(a\) ranges over \(\mathbb R\), so does \(x\).  Hence the exact
optimized endpoint contribution in row \(j\) is
\[
\inf_{a\in\mathbb R}
\left(
|A_0\cap\{f_j\leq a\}|
+|A_2\cap\{f_j\leq-a\}|
\right)
=\phi(R_j),
\tag{21}
\]
where
\[
\phi(D)=\inf_{x\in\mathbb R}
\left([x]_u^2+[D-x]_v^2\right).
\tag{22}
\]

We now solve (22), including every boundary case:
\[
\phi(D)=
\begin{cases}
0,&D\leq0,\\[1mm]
\min\{D^2/2,v^2\},&D>0.
\end{cases}
\tag{23}
\]
If \(D\leq0\), every \(x\in[D,0]\) makes both terms zero.  Suppose
\(D>0\).  If \(x\leq0\), then
\[
[D-x]_v^2\geq\min\{D^2,v^2\}
\geq\min\{D^2/2,v^2\}.
\]
If \(x\geq D\), then \(u\geq v\) gives
\[
[x]_u^2\geq\min\{D^2,u^2\}
\geq\min\{D^2,v^2\}
\geq\min\{D^2/2,v^2\}.
\]
If \(0<x<D\) and one cap is full, the sum is at least \(v^2\),
because \(u\geq v\).  If neither cap is full, then
\[
x^2+(D-x)^2\geq\frac{D^2}{2}.
\]
This proves the lower bound in (23).  If
\[
0<D\leq\sqrt2\,v,
\]
the value \(x=D/2\) has both caps nonempty and nonfull and attains
\(D^2/2\).  If
\[
D\geq\sqrt2\,v,
\]
the value \(x=0\) makes the \(A_0\)-cap empty and the \(A_2\)-cap
full, attaining \(v^2\).  Equality \(D=\sqrt2\,v\) is included in
both descriptions, and (23) is continuous and nondecreasing.

Equations (16), (21), and (23) give the exact row minimum
\[
\inf_{a\in\mathbb R}\mu_j(a)
=(1-s_j)^2+\phi(R_j).
\tag{24}
\]
The infimum is attained in all cases described above.

It remains to prove the payment forced by the third direction.  Put
\[
w=u+v,\qquad E=u^2+v^2,\qquad R_*=w-\frac23.
\tag{25}
\]
We claim
\[
9\phi(R_*)>2(E-1).
\tag{26}
\]
If \(R_*\leq0\), then \(w\leq2/3\), and positivity of \(u,v\) gives
\[
E=u^2+v^2<w^2\leq\frac49<1.
\]
Thus (26) follows from \(\phi(R_*)=0\).

Suppose \(R_*>0\).  Formula (23) gives
\[
9\phi(R_*)
=\min\left\{\frac92R_*^2,9v^2\right\}.
\tag{27}
\]
The full-\(A_2\)-cap value is strictly larger than the right side of
(26): by (15),
\[
E-1=u^2+v^2-1<2v^2,
\]
so
\[
2(E-1)<4v^2<9v^2.
\tag{28}
\]
The interior two-cap value is also strictly larger, because
\[
\begin{aligned}
\frac92\left(w-\frac23\right)^2-2(E-1)
&=\frac52w^2+4uv-6w+4\\
&=\frac52\left(w-\frac65\right)^2
  +4uv+\frac25
>0.
\end{aligned}
\tag{29}
\]
Equations (27)-(29) prove (26).  Notice that (28) is the replacement
for the vanished \(m-D_0\) term: it uses the actual full-cap tail of
\(A_2\), not a fictitious uncovered area.

By (5), some index \(j\) satisfies
\[
s_j<\frac13.
\tag{30}
\]
For every such index, (13) and (20) give
\[
R_j
\geq u+v-2s_j
>u+v-\frac23
=R_*.
\tag{31}
\]
Monotonicity of \(\phi\), (16), (26), and (31) imply
\[
\begin{aligned}
\inf_a\mu_j(a)
&=(1-s_j)^2+\phi(R_j)\\
&>\frac49+\frac{2(E-1)}9\\
&=\frac{2(1+E)}9=t.
\end{aligned}
\tag{32}
\]
Thus every index satisfying (30) has
\[
I_j=\varnothing.
\tag{33}
\]

Now assume the tail hypothesis \(c_q+m<t\).  Formula (23) gives
\(\phi(D)\leq v^2=m\) for every \(D\).  Hence (24) gives
\[
\inf_a\mu_q(a)
=c_q+\phi(R_q)
\leq c_q+m<t.
\tag{34}
\]
The infimum is attained, so \(I_q\ne\varnothing\).  Therefore \(q\)
cannot be one of the indices in (30).  Such an index exists by (5),
and (33) shows that it is an \(i\ne q\) with \(I_i=\varnothing\).
This proves (11).

All caps in the proof are closed.  Every nonconstant affine cutting
line has planar area zero.  Formulae (17)-(23) explicitly include
zero-area support faces, empty caps, full caps, and every equality
between profile pieces.  All strictness in (32) comes from
\(s_j<1/3\), the strict residual inequality (15), and \(u,v>0\);
none is lost at a cap boundary.

We finish with an exact rational nonempty example in the requested
large-\(D_0\) regime.  Take
\[
u=\frac{26}{25},\qquad
v=\frac3{10},\qquad
P=g,
\tag{35}
\]
and
\[
s_1=\frac38,\qquad
s_2=s_3=\frac{31}{100}.
\tag{36}
\]
Then
\[
s_1+s_2+s_3=\frac{199}{200}<1,
\qquad d=\frac1{200},
\]
and
\[
f_1=75-200\lambda_1,\qquad
f_2=62-200\lambda_2,\qquad
f_3=62-200\lambda_3.
\tag{37}
\]
The midpoint triangle in (12) has scale
\[
\frac{u+v}{2}=\frac{67}{100}<1
\]
about \(g\), so it is contained in \(\Delta\).  The areas and target
are
\[
M=\frac{676}{625},\qquad
m=\frac9{100},\qquad
k=1,\qquad
t=\frac{5429}{11250}.
\tag{38}
\]
Here
\[
r=\frac mM=\frac{225}{2704}<\frac9{25},
\qquad
\frac kM=\frac{625}{676},
\]
and the exact residual inequalities are
\[
1-r=\frac{2479}{2704}
<
\frac{2500}{2704}
=\frac kM
<
\frac{2929}{2704}
=1+r.
\tag{39}
\]
Moreover,
\[
D_0=\frac{2683}{7500}
>\frac9{100}=m.
\tag{40}
\]

With \(q=1\), every middle cap is strictly below \(t\):
\[
c_1=\frac{25}{64}<t,\qquad
c_2=c_3=\frac{4761}{10000}<t,
\tag{41}
\]
the latter margin being
\[
t-\frac{4761}{10000}=\frac{583}{90000}>0.
\]
The tail inequality is also strict:
\[
c_1+m
=\frac{769}{1600}
=t-\frac{703}{360000}
<t.
\tag{42}
\]
For rows \(2,3\), equations (20) and (23) give
\[
R_2=R_3=\frac{47}{50},
\qquad
\phi(R_2)=\phi(R_3)=v^2=\frac9{100},
\]
so
\[
\inf_a\mu_2(a)=\inf_a\mu_3(a)
=\frac{5661}{10000}
=t+\frac{7517}{90000}
>t.
\tag{43}
\]
Thus \(I_1\ne\varnothing\) and \(I_2=I_3=\varnothing\).  This example
lies strictly in \(D_0>m\), has all three middle caps below \(t\), and
attains the full-\(A_2\), empty-\(A_0\) profile piece in (23).  It
therefore verifies that the lemma is neither a \(c_i\geq t\) shortcut
nor a hidden \(D_0\leq m\) argument.

## External sources

none
