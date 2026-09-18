---
fact_id: bb4b1ec9edb3e64e
kind: lemma
author: "mp_r349_balanced_linear_tube"
assurance: LLM-verified
subgoal_id: triangle-balanced-linear-separation
depends_on: ["291c24bb45bd4946","64760c76cadff481","f74f24523b5f53b2"]
source_packet_sha256: e6e3254d3827dfea6adce05c98567f4ef4ed39ff110ff5c7a83651396acaf307
verifier_run: 060b59b59f6643fc
target_match: null
---

## Statement

Let
\[
\Delta=\operatorname{conv}\{e_1,e_2,e_3\},\qquad |\Delta|=1,
\]
and define
\[
\mathcal C(z;\alpha)
=\left|\{\lambda\in\Delta:z\cdot\lambda\ge\alpha\}\right|.
\]
Assume the exact \(N=3\) triangular barycentric system of accepted facts
`64760c76cadff481` and `f74f24523b5f53b2` in its surviving orientation.
Thus \(U,V,L\in\mathbb R^{3\times3}\) and
\(\sigma\in\mathbb R^3\) satisfy
\[
\mathbf1^\top U=\mathbf1^\top,\qquad
\mathbf1^\top V=\mathbf1^\top,\qquad
\mathbf1^\top L=\mathbf1^\top,
\]
\[
\det U\ne0,\qquad \det V\ne0,\qquad \det L\ne0,
\]
\[
\min_jU_{kj}+\min_jV_{kj}\ge0\quad(k=1,2,3),
\qquad
\sum_{i=1}^3\sigma_i>1.
\]
Normalize
\[
A=|\det U|=r,\qquad B=|\det V|=1,
\qquad 0<r<\frac38,
\]
and put
\[
t_r=\frac{2(1+A+B)}9=\frac{2(2+r)}9.
\tag{1}
\]
For any \(\delta>0\), set
\[
R=\delta L,\qquad \tau=\delta\sigma.
\tag{2}
\]
Then the columns of \(R\) sum to \(\delta\),
\(\sum_i\tau_i>\delta\), and the exact row masses are
\[
M_i=
\mathcal C(R_{i*};0)
+r\,\mathcal C((RU)_{i*};-\tau_i)
+\mathcal C((RV)_{i*};\tau_i)
\qquad(i=1,2,3).
\tag{3}
\]

Put
\[
P=3I-\mathbf1\mathbf1^\top
=
\begin{pmatrix}
2&-1&-1\\
-1&2&-1\\
-1&-1&2
\end{pmatrix}.
\]
Suppose there are \(c>0\) and row and column permutation matrices
\(\Pi,\Gamma\) such that
\[
\max_{1\le i,j\le3}
\left|c^{-1}(\Pi R\Gamma)_{ij}-P_{ij}\right|
\le\frac r{100}.
\tag{4}
\]
Then
\[
\boxed{
\max_{1\le i\le3}(M_i-t_r)
\ge
\frac{r(81600+1193r+4r^2)}
{36(150+r)^2}>0.}
\tag{5}
\]
Consequently no strict counterexample in the stated tube exists.

## Proof

First audit the two positive scalings.  The scale \(\delta\) in (2)
multiplies each row functional and its corresponding threshold by the
same positive number.  Hence
\[
\mathcal C(\delta z;\delta\alpha)=\mathcal C(z;\alpha),
\]
so (3) is exactly the scale-free row-mass formula of accepted fact
`f74f24523b5f53b2`.

The scale \(c\) and the permutations in (4) will be used only for the
middle caps.  For \(a>0\),
\(\mathcal C(az;0)=\mathcal C(z;0)\), and permuting the entries of
\(z\) preserves its cap fraction on \(\Delta\).  A row permutation
only permutes the three caps.  Therefore, with
\[
\widehat R=c^{-1}\Pi R\Gamma,
\]
one has
\[
\sum_{i=1}^3\mathcal C(R_{i*};0)
=
\sum_{i=1}^3\mathcal C(\widehat R_{i*};0).
\tag{6}
\]
No such replacement is made in either endpoint term of (3): a column
permutation of \(R\) need not preserve \(RU\) or \(RV\), and scaling
\(R\) without scaling \(\tau\) need not preserve a nonzero-threshold
cap.

Set
\[
\varepsilon=\frac r{100}.
\]
Since \(0<r<3/8\), every row \(i\) of \(\widehat R\), with
\(\{i,j,k\}=\{1,2,3\}\), satisfies
\[
2-\varepsilon\le\widehat R_{ii}\le2+\varepsilon,
\qquad
-1-\varepsilon\le
\widehat R_{ij},\widehat R_{ik}
\le-1+\varepsilon.
\tag{7}
\]
In particular, the diagonal value is positive and the other two values
are negative.  The complete cap formula of accepted fact
`64760c76cadff481`, including the repeated-value case, gives
\[
\mathcal C(\widehat R_{i*};0)
=
\frac{\widehat R_{ii}^{\,2}}
{(\widehat R_{ii}-\widehat R_{ij})
 (\widehat R_{ii}-\widehat R_{ik})}.
\tag{8}
\]
The numerator in (8) is at least \((2-\varepsilon)^2\), while each
positive denominator factor is at most \(3+2\varepsilon\).  Thus the
worst-box middle-cap bound is
\[
\begin{aligned}
\mathcal C(\widehat R_{i*};0)
&\ge
\left(\frac{2-\varepsilon}{3+2\varepsilon}\right)^2\\
&=
\frac{(200-r)^2}{4(150+r)^2}
=:m(r).
\end{aligned}
\tag{9}
\]
Equations (6) and (9) yield
\[
\sum_{i=1}^3\mathcal C(R_{i*};0)\ge3m(r).
\tag{10}
\]

We next use the original \(R,U,\tau\) to check the endpoint cover.
The \(U\)-endpoint is the smaller endpoint and has coefficient \(r\)
in (3).  Define its three closed caps by
\[
E_i=
\{\lambda\in\Delta:(RU)_{i*}\cdot\lambda\ge-\tau_i\}.
\tag{11}
\]
If some \(\lambda\in\Delta\) lay outside all three caps, then
\[
(RU)_{i*}\cdot\lambda<-\tau_i
\qquad(i=1,2,3).
\tag{12}
\]
Because the columns of \(R\) sum to \(\delta\) and the columns of
\(U\) sum to one,
\[
\sum_{i=1}^3(RU)_{i*}
=\mathbf1^\top RU
=\delta\mathbf1^\top U
=\delta\mathbf1^\top.
\tag{13}
\]
Summing (12), using \(\mathbf1^\top\lambda=1\), and using
\(\sum_i\tau_i>\delta>0\), would give
\[
\delta<-\sum_{i=1}^3\tau_i<-\delta,
\]
a contradiction.  Therefore \(E_1\cup E_2\cup E_3=\Delta\), including
all boundary and repeated-projection cases, and pointwise integration
gives
\[
\sum_{i=1}^3
\mathcal C((RU)_{i*};-\tau_i)\ge1.
\tag{14}
\]

The \(V\)-endpoint terms in (3) are nonnegative.  Combining
(3), (10), and (14) therefore gives
\[
\sum_{i=1}^3M_i\ge3m(r)+r,
\qquad
\max_iM_i\ge m(r)+\frac r3.
\tag{15}
\]
Subtracting (1) from the endpoint-cover average in (15) yields
\[
\begin{aligned}
\max_i(M_i-t_r)
&\ge
\frac{(200-r)^2}{4(150+r)^2}
+\frac r3-\frac{2(2+r)}9\\
&=
\frac{9(200-r)^2-4(4-r)(150+r)^2}
{36(150+r)^2}.
\end{aligned}
\tag{16}
\]
The numerator has the exact symbolic factorization
\[
9(200-r)^2-4(4-r)(150+r)^2
=r(81600+1193r+4r^2).
\tag{17}
\]
Indeed, the two expanded terms on the left are
\[
360000-3600r+9r^2
\quad\text{and}\quad
360000-85200r-1184r^2-4r^3,
\]
whose difference is the right side of (17).  For every
\(0<r<3/8\), both the denominator in (16) and every factor on the
right side of (17) are positive.  This proves (5) symbolically.

The strict system of accepted fact `64760c76cadff481` would require
\(M_i<t_r\) for all three rows, hence
\(\max_i(M_i-t_r)<0\), contradicting (5).  Accepted fact
`291c24bb45bd4946` supplies the stated global counterexample
restriction \(r<3/8\); no ratio outside the registered tube and range
is asserted here.

## External sources

none
