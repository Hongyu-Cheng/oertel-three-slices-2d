---
fact_id: 8b2562c2cb1ccbfd
kind: lemma
author: "mp_r348_balanced_ratio_interval"
assurance: LLM-verified
subgoal_id: triangle-balanced-neighborhood-r-interval
depends_on: ["291c24bb45bd4946","64760c76cadff481","91028112118edaa8","f74f24523b5f53b2"]
source_packet_sha256: b341183aa4099519a88bb97ea9e28364179b777719aa3783bce33843c06c0687
verifier_run: 9d956668e05f4b34
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
Normalize the determinant parameters on this section as
\[
A=|\det U|=r,\qquad B=|\det V|=1,
\qquad
\frac{4207}{23104}\le r<\frac38,
\]
and put
\[
t_r=\frac{2(1+A+B)}9=\frac49+\frac{2r}{9}.
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

Let
\[
P=3I-\mathbf1\mathbf1^\top
=
\begin{pmatrix}
2&-1&-1\\
-1&2&-1\\
-1&-1&2
\end{pmatrix}.
\]
Suppose there are \(c>0\) and permutation matrices
\(\Pi,\Gamma\in\mathbb R^{3\times3}\) such that
\[
\left\|c^{-1}\Pi R\Gamma-P\right\|_\infty\le\frac1{50}.
\tag{4}
\]
Then
\[
\boxed{
\max_{1\le i\le3}(M_i-t_r)
\ge
\left(\frac{99}{152}\right)^2-\frac49+\frac r9
=\frac{23104r-4207}{207936}
\ge0.}
\tag{5}
\]
In particular, including at \(r=4207/23104\), no strict counterexample
witness from accepted fact `64760c76cadff481` lies in (4).

## Proof

We first audit the normalizations used below.  The middle triangle has
area one by the barycentric normalization in accepted fact
`64760c76cadff481`.  On the parameter section \(B=1\), the middle
coefficient is \(1\) and the two endpoint coefficients are \(r\) and
\(1\), which gives (1).  The scale
\(\delta\) in (2) multiplies each row functional and its corresponding
threshold by the same positive number.  Hence
\[
\mathcal C(\delta z;\delta\alpha)=\mathcal C(z;\alpha),
\]
so (3) is exactly the lossless parametrization of accepted fact
`f74f24523b5f53b2`.

The scale \(c\) and the permutations in (4) have a more limited role.
For \(a>0\),
\[
\mathcal C(az;0)=\mathcal C(z;0),
\]
and permuting the entries of \(z\) preserves its cap fraction on
\(\Delta\).  A row permutation merely permutes the three middle caps.
Consequently, if
\[
\widehat R=c^{-1}\Pi R\Gamma,
\]
then
\[
\sum_{i=1}^3\mathcal C(R_{i*};0)
=
\sum_{i=1}^3\mathcal C(\widehat R_{i*};0).
\tag{6}
\]
We use \(\widehat R\) only in (6).  We do not replace \(R\) by
\(\widehat R\) in either endpoint term of (3), since a column
permutation of \(R\) need not preserve \(RU\) or \(RV\), and scaling
\(R\) without scaling \(\tau\) need not preserve a nonzero-threshold
cap.  Thus no endpoint invariance is being assumed.

Fix row \(i\) of \(\widehat R\), and let \(j,k\) be the other two
column indices.  From (4),
\[
\frac{99}{50}\le\widehat R_{ii}\le\frac{101}{50},
\qquad
-\frac{51}{50}\le\widehat R_{ij},\widehat R_{ik}
\le-\frac{49}{50}.
\tag{7}
\]
This row has exactly one positive vertex value and two negative vertex
values.  The complete cap formula in accepted fact
`64760c76cadff481` gives
\[
\mathcal C(\widehat R_{i*};0)
=
\frac{\widehat R_{ii}^{\,2}}
{(\widehat R_{ii}-\widehat R_{ij})
 (\widehat R_{ii}-\widehat R_{ik})}.
\tag{8}
\]
Both denominator factors in (8) are positive and at most \(152/50\),
while the numerator is at least \((99/50)^2\).  Therefore
\[
\mathcal C(\widehat R_{i*};0)
\ge
\frac{(99/50)^2}{(152/50)^2}
=\left(\frac{99}{152}\right)^2
=\frac{9801}{23104}.
\tag{9}
\]
Summing (9) and using (6) yields
\[
\sum_{i=1}^3\mathcal C(R_{i*};0)
\ge\frac{29403}{23104}.
\tag{10}
\]

We next identify the endpoint family that covers the simplex.  It is
the \(U\)-family, whose coefficient in (3) is the smaller determinant
\(r\).  Define the three closed caps
\[
E_i=
\{\lambda\in\Delta:(RU)_{i*}\cdot\lambda\ge-\tau_i\}.
\tag{11}
\]
If some \(\lambda\in\Delta\) were outside every \(E_i\), closedness in
(11) would give the three strict inequalities
\[
(RU)_{i*}\cdot\lambda<-\tau_i
\qquad(i=1,2,3).
\tag{12}
\]
The column-sum identities give
\[
\sum_{i=1}^3(RU)_{i*}
=\mathbf1^\top RU
=\delta\mathbf1^\top U
=\delta\mathbf1^\top.
\tag{13}
\]
Summing (12), using \(\mathbf1^\top\lambda=1\), and then using
\(\sum_i\tau_i>\delta>0\), gives
\[
\delta<-\sum_{i=1}^3\tau_i<-\delta,
\]
which is impossible.  Hence the three \(U\)-caps cover all of
\(\Delta\), including their boundary points, and
\[
\sum_{i=1}^3
\mathcal C((RU)_{i*};-\tau_i)\ge|\Delta|=1.
\tag{14}
\]
No analogous covering assertion is used for the \(V\)-family.  Its
three contributions in (3) are only discarded as nonnegative.

Equations (3), (10), and (14) now give
\[
\sum_{i=1}^3M_i
\ge
3\left(\frac{99}{152}\right)^2+r.
\tag{15}
\]
The maximum is at least the average, so
\[
\max_iM_i
\ge
\left(\frac{99}{152}\right)^2+\frac r3.
\tag{16}
\]
Subtracting (1) gives the exact gap
\[
\begin{aligned}
\max_i(M_i-t_r)
&\ge
\left(\frac{99}{152}\right)^2+\frac r3
-\left(\frac49+\frac{2r}{9}\right)\\
&=
\left(\frac{99}{152}\right)^2-\frac49+\frac r9\\
&=
\frac{23104r-4207}{207936}.
\end{aligned}
\tag{17}
\]
Indeed,
\[
4-9\left(\frac{99}{152}\right)^2
=\frac{92416-88209}{23104}
=\frac{4207}{23104},
\tag{18}
\]
so (17) is nonnegative throughout the stated interval.
As a normalization check, at \(r=1/4\), (17) becomes
\[
\frac{1569}{207936}=\frac{523}{69312},
\]
which is the bound in accepted fact `91028112118edaa8`.

Accepted fact `291c24bb45bd4946` supplies the strict global upper
restriction \(r<3/8\) for any counterexample, which is the upper end of
the registered interval.  At the lower endpoint
\(r=4207/23104\), the right side of (17) is zero.  This still excludes
a strict witness: the strict system of accepted fact
`64760c76cadff481` requires \(M_i<t_r\) for all three rows, and hence
\(\max_i(M_i-t_r)<0\), contradicting (17).  Thus no positive margin is
needed at that endpoint, and (5) follows on the full stated interval.

## External sources

none
