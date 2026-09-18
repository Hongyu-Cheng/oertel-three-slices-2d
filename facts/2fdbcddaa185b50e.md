---
fact_id: 2fdbcddaa185b50e
kind: counterexample
author: "mp_r226_balanced_cover"
assurance: LLM-verified
subgoal_id: balanced-triple-covering-inequality
depends_on: ["8ad0785e5b4ae9ef","d2d117bcc58a1ba0"]
source_packet_sha256: 66a03880de94742056191949a02629fb78f88095b68b98b21e523b159ddcefbd
verifier_run: 1cea99bb2ce544a6
target_match: null
---

## Statement

Let
\[
\Delta=\operatorname{conv}\{(0,0),(1,0),(0,1)\},
\qquad D=|\Delta|=\frac12,
\]
and fix any rational number \(0<\varepsilon\leq1/2\). Put
\[
a=1+2\varepsilon^2,\qquad
b=\frac13-\frac{\varepsilon^2}{24},\qquad
d=1-3b=\frac{\varepsilon^2}{8},
\]
\[
A_0=a\Delta,\qquad A_1=\Delta,\qquad A_2=\varepsilon\Delta.
\]
Writing the affine barycentric coordinates of \(\Delta\) as
\[
\beta_1(x,y)=1-x-y,\qquad \beta_2(x,y)=x,\qquad
\beta_3(x,y)=y,
\]
define
\[
f_i(w)=\frac{b-\beta_i(w)}d,\qquad
s=\frac{b-2}{d},
\qquad
H_i=\{(h,w):f_i(w)+s(h-1)\leq0\}.
\]
Then all three \(A_j\) are rational two-dimensional polygons and
\[
\frac{A_0+A_2}{2}\subseteq A_1.
\]
By accepted fact `8ad0785e5b4ae9ef`, they are the three integer-height sections of a compact polytope.

The middle interiors \(\{f_i<0\}=\{\beta_i>b\}\) cover \(\mathbb R^2\). More precisely, with
\[
q_1=\frac{(1,1)}{\sqrt2},\qquad q_2=(-1,0),\qquad q_3=(0,-1),
\]
\[
\alpha_1=\frac{\sqrt2}{d},\qquad
\alpha_2=\alpha_3=\frac1d,
\]
\[
r_1=\frac{1-b}{\sqrt2},\qquad r_2=r_3=-b,
\qquad
\lambda_1=\frac{b-2}{\sqrt2},\qquad
\lambda_2=\lambda_3=b-2,
\]
one has
\[
f_i(w)=\alpha_i(q_i\cdot w-r_i),\qquad
s=\alpha_i\lambda_i,
\]
\[
\sum_{i=1}^3\alpha_iq_i=0,\qquad
\sum_{i=1}^3\alpha_i r_i=1.
\]
Thus the sections of \(H_i\) use exactly the paired thresholds
\(r_i+\lambda_i,r_i,r_i-\lambda_i\) at heights \(0,1,2\).

If
\[
S=(\{0\}\times A_0)\cup(\{1\}\times A_1)\cup(\{2\}\times A_2),
\]
\[
T=|A_0|+|A_1|+|A_2|,
\qquad t=\frac{2T}{9},
\]
then every same-index row violates the proposed conclusion:
\[
\mathcal H_2(S\cap H_i)
=D\left[\left(\frac23+\frac{\varepsilon^2}{24}\right)^2
+\varepsilon^2\right]
<\frac{2T}{9}
\qquad(i=1,2,3).
\]
For the profile thresholds \(\rho_q(t)\) of accepted fact
`d2d117bcc58a1ba0`, these same directions satisfy
\[
\sum_{i=1}^3\alpha_i\rho_{q_i}(t)>1.
\]
Consequently the middle \(t\)-depth region is empty, despite compatibility and the normalized balanced three-cap certificate.

## Proof

For nonnegative scalars \(u,v\), convexity of \(\Delta\) and \(0\in\Delta\) give
\[
u\Delta+v\Delta=(u+v)\Delta.
\]
Hence
\[
\frac{A_0+A_2}{2}
=\frac{1+\varepsilon+2\varepsilon^2}{2}\Delta.
\]
The function \(\varepsilon+2\varepsilon^2\) is increasing on
\((0,1/2]\) and equals \(1\) at \(\varepsilon=1/2\). Therefore the displayed scale factor is at most \(1\), proving the full containment in \(A_1=\Delta\). Rationality and two-dimensionality are immediate. Accepted fact `8ad0785e5b4ae9ef` now gives the asserted compact polytope.

Since \(\beta_1+\beta_2+\beta_3=1\),
\[
f_1+f_2+f_3
=\frac{3b-1}{d}=-1.
\]
The explicit formulas for \(q_i,\alpha_i,r_i\) give
\[
\alpha_1q_1+\alpha_2q_2+\alpha_3q_3
=\frac{(1,1)+(-1,0)+(0,-1)}d=0
\]
and
\[
\sum_{i=1}^3\alpha_i r_i
=\frac{1-b-b-b}{d}
=\frac{1-3b}{d}=1.
\]
They also give \(f_i=\alpha_i(q_i\cdot w-r_i)\). Direct substitution shows \(s=\alpha_i\lambda_i\) for every \(i\), so
\[
H_i
=\{(h,w):q_i\cdot w+\lambda_i(h-1)\leq r_i\}.
\]
This verifies the same-index threshold pairing and the strictly positive normal balance.

At height \(h\), the section condition is
\[
\beta_i(w)\geq b+(b-2)(h-1).
\]
Thus the three thresholds at \(h=0,1,2\) are respectively
\[
2,\qquad b,\qquad 2b-2.
\]
At height \(0\), all three caps miss \(A_0=a\Delta\). Indeed,
\[
\max_{a\Delta}\beta_1=1<2,\qquad
\max_{a\Delta}\beta_2=\max_{a\Delta}\beta_3=a
\leq\frac32<2.
\]
At height \(2\), all three caps contain \(A_2=\varepsilon\Delta\), because
\[
2b-2=-\frac43-\frac{\varepsilon^2}{12}<0,
\]
whereas on \(A_2\)
\[
\beta_2,\beta_3\geq0,\qquad
\beta_1\geq1-\varepsilon\geq\frac12.
\]

At height \(1\), the cap
\[
\Delta\cap\{\beta_i\geq b\}
\]
is a corner triangle linearly similar to \(\Delta\) with ratio
\[
1-b=\frac23+\frac{\varepsilon^2}{24}.
\]
Its area is therefore
\[
D\left(\frac23+\frac{\varepsilon^2}{24}\right)^2.
\]
The three slice contributions in the same row are consequently
\[
0,\qquad
D\left(\frac23+\frac{\varepsilon^2}{24}\right)^2,\qquad
\varepsilon^2D,
\]
which proves the asserted row-mass formula.

The total area and target are
\[
T
=D\left((1+2\varepsilon^2)^2+1+\varepsilon^2\right)
=D(2+5\varepsilon^2+4\varepsilon^4),
\]
\[
\frac{2T}{9}
=D\left(
\frac49+\frac{10}{9}\varepsilon^2
+\frac89\varepsilon^4
\right).
\]
On the other hand, every row has mass
\[
D\left(
\frac49+\frac{19}{18}\varepsilon^2
+\frac1{576}\varepsilon^4
\right).
\]
Their exact difference is
\[
\frac{2T}{9}-\mathcal H_2(S\cap H_i)
=D\left(
\frac{\varepsilon^2}{18}
+\frac{511\varepsilon^4}{576}
\right)>0.
\]

The target also satisfies the range hypothesis of accepted fact
`d2d117bcc58a1ba0`. Indeed,
\[
a_1+a_2-\frac{2T}{9}
=\frac D9(5-\varepsilon^2-8\varepsilon^4)>0
\]
for \(0<\varepsilon\leq1/2\), and \(a_0+a_1>a_1+a_2\).
The row mass just computed is a finite-slope value at the paired threshold
\(r_i\). Hence that accepted fact gives
\[
\Phi_{q_i}(r_i)
\leq\mathcal H_2(S\cap H_i)<t.
\]
Its exact superlevel identity
\(\{r:\Phi_{q_i}(r)\geq t\}=[\rho_{q_i}(t),\infty)\)
therefore implies
\[
r_i<\rho_{q_i}(t).
\]
All \(\alpha_i\) are positive, so the already verified normalization yields
\[
\sum_{i=1}^3\alpha_i\rho_{q_i}(t)
>\sum_{i=1}^3\alpha_i r_i=1.
\]

Finally, if the open middle caps failed to cover some \(w\in\mathbb R^2\), then
\(\beta_i(w)\leq b\) for all \(i\), and hence
\[
1=\sum_i\beta_i(w)\leq3b
=1-\frac{\varepsilon^2}{8}<1,
\]
a contradiction. Every \((1,w)\) therefore lies in the interior of one of the three halfspaces of mass below \(t\). In particular, every point of
\(\{1\}\times A_1\) has depth below \(t\), so the middle \(t\)-depth region is empty.

This does not disprove the locked centerpoint target, because
\[
|A_0|-|A_1|-|A_2|
=D(3\varepsilon^2+4\varepsilon^4)>0.
\]
Thus \(A_0\) is a large outer slice. For rational
\(\varepsilon\downarrow0\), however,
\[
\frac{|A_0|-|A_1|-|A_2|}{T}\longrightarrow0,
\]
so these exact counterexamples approach the residual boundary arbitrarily closely while retaining the full-plane balanced cover and all three strict row inequalities.

## External sources

none
