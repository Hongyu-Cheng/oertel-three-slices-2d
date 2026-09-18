---
fact_id: c4b10eea7cd8ea81
kind: lemma
author: "mp_r86_cf_negative_gap_coercivity"
assurance: LLM-verified
subgoal_id: canonical-root-tail-concurrent-fan-crossing-inequality
depends_on: []
source_packet_sha256: abaa089320359be99ccdeae61f4cbc9e1698c3ae80ea045e7f21cfa0fffdd0bf
verifier_run: 8e2bf41796ad426f
target_match: null
---

## Statement

Let \(\ell _1,\ell _2,\ell _3\) be nonzero pairwise nonparallel linear forms on \(\mathbb R^2\) such that
\[
\ell _1+\ell _2+\ell _3=0.
\]
For a compact convex body \(K\) of positive area containing the common zero \(O\) in its interior, put
\[
p_i(K)=\frac{|K\cap\{\ell_i\leq0\}|}{|K|}.
\]
Fix a Euclidean norm and \(\varepsilon>0\).  There is a constant
\(C=C(\varepsilon,\ell_1,\ell_2,\ell_3)\) such that every area-one
convex polygon \(P\) with
\[
O\in\operatorname{int}P,\qquad
p_1(P),p_2(P)\leq\frac12,
\]
and
\[
p_3(P)-(1-p_1(P))(1-p_2(P))\leq-\varepsilon
\]
satisfies
\[
\operatorname{diam}P\leq C.
\]
The conclusion remains true without the polygonal and fan-transversality
assumptions.

## Proof

Translate \(O\) to the origin.  The fixed invertible coordinate change
\[
x=\frac{\ell_1-\ell_2}{2},\qquad
y=\frac{\ell_1+\ell_2}{2}
\]
puts the forms in the canonical shape
\[
\ell_1=x+y,\qquad
\ell_2=-x+y,\qquad
\ell_3=-2y.                                      \tag{1}
\]
It preserves all three area ratios.  Its distortion of diameter and
area is fixed, and a further common scalar dilation restores area one.
It therefore suffices to work with (1).

We first prove the only auxiliary planar estimate needed below.

Suppose that a line \(X=0\) bisects the area of a planar convex body
\(Q\), and that its chord is
\[
Q\cap\{X=0\}=\{0\}\times[-a,b],
\qquad a,b\geq0,\qquad b\geq a.                  \tag{2}
\]
Then
\[
|Q\cap\{Y\geq0\}|\geq\frac{|Q|}{4}.             \tag{3}
\]
Indeed, the midpoint of the chord in (2) has height
\((b-a)/2\geq0\).  Translating that midpoint to the origin and scaling
the \(Y\)-coordinate reduces (3) to the following symmetric-chord
claim: if \(X=0\) bisects area and
\[
Q\cap\{X=0\}=\{0\}\times[-1,1],
\]
then every one of the two halfplanes bounded by \(Y=0\) has area at
least \(|Q|/4\).  The halfplane above the translated line is contained
in the original halfplane \(Y\geq0\), so the reduction is valid.

Write \(|Q|=2V\), and let \(U_+\) and \(U_-\) be the areas above
\(Y=0\) in the right and left halves of \(Q\), respectively.  We prove
that \(U_++U_-\geq V/2\).  Suppose instead that
\[
U_++U_-<\frac V2.                               \tag{4}
\]
In particular, \(0<U_+,U_-<V/2\).

Let \(A=(0,-1)\) and \(B=(0,1)\).  A supporting line of \(Q\) at
\(A\) is not vertical, because \(Q\) has positive area on both sides
of \(X=0\).  It can therefore be written
\[
Y=mX-1,\qquad Q\subseteq\{Y\geq mX-1\}.          \tag{5}
\]
We use the following one-sided consequence of (5).  Let \(C\) be
either half of \(Q\), reflected into \(X\geq0\) if necessary.  Suppose
\(|C|=V\), its vertical base is \([A,B]\), the supporting line at
\(A\) has slope \(m\), and
\[
U=|C\cap\{Y\geq0\}|<\frac V2.
\]
Then
\[
mV\leq 2-\frac{V}{2U}.                           \tag{6}
\]

To prove (6), write
\[
C\cap\{Y=0\}=[0,s]\times\{0\}.
\]
The triangle with vertices \((0,0),B,(s,0)\) lies in the upper part of
\(C\), so
\[
s\leq2U.                                         \tag{7}
\]
If \(mU\geq1/2\), then \(m>0\), and the lower part of \(C\) is
contained in the triangle
\[
\{X\geq0,\ Y\leq0,\ Y\geq mX-1\},
\]
whose area is \(1/(2m)\leq U\).  This would give \(V\leq2U\), a
contradiction.  Hence
\[
2mU<1.                                           \tag{8}
\]
If \(2mU\leq-1\), then
\[
mV\leq-\frac{V}{2U}<2-\frac{V}{2U},
\]
and (6) follows.  We may thus assume
\[
-1<2mU<1.                                        \tag{9}
\]

For any \((X,Y)\) in the lower part of \(C\), the segment joining it
to \(B\) meets \(Y=0\) at
\[
\left(\frac{X}{1-Y},0\right).
\]
Consequently (5) and the definition of \(s\) give
\[
X\leq s(1-Y),\qquad Y\geq mX-1.                 \tag{10}
\]
Also \(ms\leq1\), by applying (5) at \((s,0)\).  From (7) and (9) one
gets \(ms>-1\): this is immediate for \(m\geq0\), while for \(m<0\)
the inequality reverses in (7).  Direct integration of the region
defined by (10), \(X\geq0\), and \(Y\leq0\) gives
\[
|C\cap\{Y\leq0\}|
\leq F_m(s):=\frac{s(3-ms)}{2(1+ms)}.            \tag{11}
\]
For completeness, when \(m>0\), the two upper bounds
\((Y+1)/m\) and \(s(1-Y)\) for \(X\) meet at
\[
Y=\frac{ms-1}{ms+1}\in[-1,0].
\]
When \(m<0\), the same value is below \(-1\); one integrates first
between \((Y+1)/m\) and \(s(1-Y)\), and then between \(0\) and
\(s(1-Y)\).  Both calculations give (11), and for \(m=0\) its value
is \(3s/2\).

On the interval \(-1<ms\leq1\),
\[
\frac{d}{ds}F_m(s)
=\frac{(1-ms)(3+ms)}{2(1+ms)^2}\geq0.
\]
Equations (7) and (9) therefore imply
\[
V-U\leq F_m(s)\leq F_m(2U)
=\frac{U(3-2mU)}{1+2mU}.
\]
Thus
\[
V\leq\frac{4U}{1+2mU},
\]
which is exactly (6).

Apply (6) to the right half of \(Q\), with \(U=U_+\) and slope \(m\),
and to the reflection of the left half, with \(U=U_-\) and slope
\(-m\).  Adding the two resulting inequalities yields
\[
\frac1{U_+}+\frac1{U_-}\leq\frac8V.              \tag{12}
\]
On the other hand,
\[
\frac1{U_+}+\frac1{U_-}
\geq\frac4{U_++U_-}>\frac8V
\]
by (4), a contradiction.  This proves (3).

We now analyze every possible unbounded sequence.  Suppose
\(K_n\) are area-one centered convex bodies in the canonical
coordinates (1), with
\[
p_1(K_n),p_2(K_n)\leq\frac12,\qquad
\operatorname{diam}K_n=d_n\longrightarrow\infty. \tag{13}
\]
After replacing \(K_n\) by
\[
\widehat K_n=d_n^{-1}K_n,
\]
the bodies have diameter one, contain the origin, and have area
\(d_n^{-2}\to0\).  They all lie in the unit disk.  Their support
functions are uniformly bounded and uniformly Lipschitz on the unit
circle, so a uniformly convergent subsequence gives Hausdorff
convergence to a compact convex set \(S\).  The limit has diameter
one.  It cannot contain a nondegenerate triangle, since such a
triangle, slightly contracted toward an interior point, would
eventually lie in \(\widehat K_n\) and give a fixed positive lower
bound on their areas.  Thus \(S\) is a segment.

Choose diameter endpoints of \(\widehat K_n\), let \(e_n\) be the
unit vector from one endpoint to the other, and let \(f_n\) be its
counterclockwise perpendicular.  After passing to a subsequence,
\[
e_n\longrightarrow e,\qquad f_n\longrightarrow f,
\]
where \(e\) is parallel to \(S\).  Let \(w_n\) be the width of
\(\widehat K_n\) in the \(f_n\)-direction.  Then \(w_n\to0\).  Define
\[
Q_n=\{(s,t):s e_n+w_nt f_n\in\widehat K_n\}.      \tag{14}
\]
The \(s\)-coordinates lie in \([-1,1]\).  The \(t\)-coordinates form
an interval of length one containing zero, so they also lie in
\([-1,1]\).  The two diameter endpoints in (14) have the same
\(t\)-coordinate and \(s\)-coordinates differing by one.  One of the
two transverse supporting points has \(t\)-distance at least \(1/2\)
from that diameter line.  Their convex hull is a triangle of area at
least \(1/4\).  Consequently, after another subsequence,
\[
Q_n\longrightarrow Q
\]
in Hausdorff distance, where \(Q\) is a two-dimensional convex body.
Areas and areas cut by convergent nonzero linear halfplanes converge,
because convex boundaries and lines have planar area zero.

Put
\[
a_{i,n}=\ell_i(e_n),\qquad b_{i,n}=\ell_i(f_n),
\qquad a_i=\ell_i(e).
\]
In the coordinates (14),
\[
\ell_i=a_{i,n}s+w_nb_{i,n}t.                    \tag{15}
\]
After a subsequence, assume also that
\[
p_i(K_n)\longrightarrow q_i
\]
for all \(i\), and put
\[
L=\frac{|Q\cap\{s\leq0\}|}{|Q|}.
\]
Whenever \(a_i\neq0\), (15) gives
\[
q_i=
\begin{cases}
L,&a_i>0,\\
1-L,&a_i<0.
\end{cases}                                      \tag{16}
\]

First suppose that no \(a_i\) is zero.  If \(a_1,a_2\) have the same
sign, then \(q_1=q_2\), \(q_3=1-q_1\), and
\[
q_3-(1-q_1)(1-q_2)=q_1(1-q_1)\geq0.             \tag{17}
\]
If \(a_1,a_2\) have opposite signs, the two inequalities
\(q_1,q_2\leq1/2\) force \(L=1/2\).  Hence
\[
q_1=q_2=q_3=\frac12
\]
and the limiting defect is \(1/4\).

At most one \(a_i\) can vanish.  If \(a_1=0\), then
\(a_2=-a_3\neq0\), so (16) gives \(q_2+q_3=1\).  Therefore
\[
q_3-(1-q_1)(1-q_2)=q_1q_3\geq0.                 \tag{18}
\]
If \(a_2=0\), the symmetric calculation gives
\[
q_3-(1-q_1)(1-q_2)=q_2q_3\geq0.                 \tag{19}
\]

It remains to treat collapse along the third fan line:
\[
a_3=0,\qquad a_1=-a_2\neq0.                     \tag{20}
\]
Equation (16) and \(q_1,q_2\leq1/2\) give
\[
q_1=q_2=\frac12.                                \tag{21}
\]
Consider the extended-real limit of \(a_{3,n}/w_n\).  If it is
\(+\infty\) or \(-\infty\), (15) shows that the third cap converges
to one of the two half-bodies \(s\leq0\) or \(s\geq0\).  By (21), its
area ratio tends to \(1/2\), and the limiting defect is \(1/4\).

Suppose instead that \(a_{3,n}/w_n\) has a finite limit.  Reverse
\(e_n,f_n\) simultaneously if needed, and put
\[
c_n=\frac{a_{1,n}-a_{2,n}}2>0.
\]
On \(Q_n\), make the further exact linear change
\[
X=\frac{\ell_1-\ell_2}{2c_n},\qquad
Y=\frac{\ell_1+\ell_2}{2w_n}.                    \tag{22}
\]
The maps in (22) converge to an invertible linear map: the
\(X\)-coordinate tends to \(s\), while the coefficient of \(t\) in
\(Y\) tends to \(-\ell_3(f)/2\neq0\).  Thus the transformed bodies,
still denoted by \(R_n\), converge to a two-dimensional convex body
\(R\).  In these coordinates the three forms are exactly
\[
\ell_1=c_nX+w_nY,\qquad
\ell_2=-c_nX+w_nY,\qquad
\ell_3=-2w_nY.                                  \tag{23}
\]
Put \(\delta_n=w_n/c_n\to0\).  Equations (21) and (23) show that
\(X=0\) bisects the area of \(R\).  Write its chord as
\[
R\cap\{X=0\}=\{0\}\times[-\alpha,\beta],
\qquad \alpha,\beta\geq0.                        \tag{24}
\]

The cap assumptions also give \(p_1(K_n)+p_2(K_n)\leq1\).  Away from
the two fan lines, the pointwise identity
\[
\mathbf1_{\{\ell_1\leq0\}}+\mathbf1_{\{\ell_2\leq0\}}
=1+\mathbf1_{\{\ell_1<0,\ell_2<0\}}
-\mathbf1_{\{\ell_1>0,\ell_2>0\}}
\]
therefore implies
\[
|\{\ell_1<0,\ell_2<0\}\cap R_n|
\leq
|\{\ell_1>0,\ell_2>0\}\cap R_n|.                \tag{25}
\]
By (23), the two regions in (25) are
\[
\left\{Y<-\frac{|X|}{\delta_n}\right\},
\qquad
\left\{Y>\frac{|X|}{\delta_n}\right\},           \tag{26}
\]
respectively.  The change \(X=\delta_n\xi\), followed by dominated
convergence, gives
\[
\frac1{\delta_n}
\left|R_n\cap\left\{Y<-\frac{|X|}{\delta_n}\right\}\right|
\longrightarrow \alpha^2,
\]
\[
\frac1{\delta_n}
\left|R_n\cap\left\{Y>\frac{|X|}{\delta_n}\right\}\right|
\longrightarrow \beta^2.                       \tag{27}
\]
Indeed, after that change of variables the limiting lower integrand
is supported on
\(-\alpha<Y<0,\ |\xi|<-Y\), whose area is \(\alpha^2\);
the upper one is supported on
\(0<Y<\beta,\ |\xi|<Y\), whose area is \(\beta^2\).
All transformed bodies lie in one fixed box, and the two endpoints
in (24) are the only exceptional \(Y\)-values.  Thus (25)-(27) imply
\[
\alpha\leq\beta.                                \tag{28}
\]

The auxiliary estimate (3), applied to (24) and (28), now gives
\[
q_3=\frac{|R\cap\{Y\geq0\}|}{|R|}
\geq\frac14.                                    \tag{29}
\]
Together with (21), this says that the limiting product defect is
nonnegative.  This finishes all possible segment directions,
including a segment contained in a fan ray and a segment having the
origin as an endpoint.

We have proved that every diameter-unbounded sequence satisfying the
two cap constraints has, after a subsequence, a nonnegative limiting
product defect.  If the asserted diameter bound failed for some
\(\varepsilon>0\), one could choose such a sequence with defect at
most \(-\varepsilon\).  Continuity of
\[
(r_1,r_2,r_3)\longmapsto r_3-(1-r_1)(1-r_2)
\]
would make its limiting defect at most \(-\varepsilon\), contradicting
the preceding analysis.  Hence the required constant \(C\) exists.

## External sources

none
