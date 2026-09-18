---
fact_id: fbd25afea87ffbac
kind: lemma
author: "mp_r221_midpoint_bm"
assurance: LLM-verified
subgoal_id: deep-midpoint-brunn-minkowski-transfer
depends_on: ["17ca54faa05ad878","2f9be517307232c7","66f17f4981c30108","8ad0785e5b4ae9ef","d2d117bcc58a1ba0"]
source_packet_sha256: 4525d69f53014cff406ca56662f02718ebf55908d0d0acde20c46a26052282af
verifier_run: 57ea55a9658344e7
target_match: null
---

## Statement

For a nonempty two-dimensional compact convex body \(A\subset\mathbb R^2\)
and \(x\in A\), write
\[
d_A(x)=\inf\{|A\cap P|:P\subset\mathbb R^2
\text{ is a closed halfplane containing }x\}.
\]
Let \(A_0,A_1,A_2\) be the slices of the locked problem, so that, by
accepted fact `8ad0785e5b4ae9ef`,
\[
\frac{A_0+A_2}{2}\subseteq A_1.
\tag{1}
\]
For \(i\in\{0,2\}\), let \(x_i\in A_i\) and let
\[
0\leq\beta_i\leq d_{A_i}(x_i),\qquad
z=\frac{x_0+x_2}{2}.
\tag{2}
\]
Then \(z\in A_1\) and
\[
d_{A_1}(z)\geq
\frac{(\sqrt{\beta_0}+\sqrt{\beta_2})^2}{4}.
\tag{3}
\]

For \(q\in\mathbb S^1\), put
\[
F_{i,q}(c)=|A_i\cap\{w:q\cdot w\leq c\}|,
\]
and let \(Q_{i,q}\) be its endpoint-normalized cap quantile in accepted
fact `17ca54faa05ad878`. For \(b>0\), let
\[
\mathcal E(b)=
\bigcap_{\substack{q\in\mathbb S^1\\0\leq u\leq b}}
\left\{w:
2q\cdot w\geq Q_{0,q}(u)+Q_{2,q}(b-u)\right\},
\tag{4}
\]
and use the exact convention
\[
\mathcal E(0)=\mathbb R^2
\tag{5}
\]
from accepted fact `66f17f4981c30108`. Then
\[
z\in\mathcal E(b)
\qquad
\left(0\leq b\leq\min\{\beta_0,\beta_2\}\right).
\tag{6}
\]

Now write \(a_i=|A_i|\), \(T=a_0+a_1+a_2\), let \(g_i\) be the centroid
of \(A_i\), and put
\[
M=\max\{a_0,a_2\},\qquad
m=\min\{a_0,a_2\},\qquad
z_0=\frac{g_0+g_2}{2}.
\tag{7}
\]
Then
\[
h_S((1,z_0))\geq
\min\left\{
a_0+a_1,\ a_1+a_2,\
\frac{(\sqrt M+\sqrt m)^2+4m}{9}
\right\}.
\tag{8}
\]
In particular, the locked target holds whenever
\[
2a_1\leq2\sqrt{Mm}+3m-M.
\tag{9}
\]

More explicitly, normalize by
\[
r=\frac mM,\qquad s=\frac{a_1}{M}.
\tag{10}
\]
The area regime (9) is exactly
\[
0<r\leq1,\qquad s>0,\qquad
2s\leq2\sqrt r+3r-1.
\tag{11}
\]
It is nonempty in \(s>0\) exactly for \(r>1/9\). The residual band left
after the large-slice criterion in accepted fact `2f9be517307232c7` is
\[
0<r\leq1,\qquad 1-r<s<1+r.
\tag{12}
\]
Thus the new part inside that band is exactly
\[
\boxed{
\frac9{25}<r\leq1,\qquad
1-r<s<1+r,\qquad
2s\leq2\sqrt r+3r-1.}
\tag{13}
\]

## Proof

We first prove the same-direction transfer and audit the cap orientation.
Let \(P\) be any closed planar halfplane containing \(z\). Choose
\(q\in\mathbb S^1\) and \(c\in\mathbb R\) so that
\[
P=\{w:q\cdot w\leq c\}.
\]
Since \(q\cdot z\leq c\), the parallel halfplane
\[
P_z=\{w:q\cdot w\leq q\cdot z\}
\tag{14}
\]
is contained in \(P\). Define the endpoint caps through the prescribed
points by
\[
B_i=A_i\cap\{w:q\cdot w\leq q\cdot x_i\},
\qquad i\in\{0,2\}.
\tag{15}
\]
Each cap is nonempty, compact, and convex. It contains \(x_i\), so (2)
gives
\[
|B_i|\geq\beta_i.
\tag{16}
\]
For \(w_i\in B_i\),
\[
q\cdot\left(\frac{w_0+w_2}{2}-z\right)
=\frac12q\cdot(w_0-x_0)+\frac12q\cdot(w_2-x_2)
\leq0.
\]
Combining this inequality with (1) yields the exact containment
\[
\frac{B_0+B_2}{2}\subseteq A_1\cap P_z\subseteq A_1\cap P.
\tag{17}
\]

The planar Brunn--Minkowski inequality, including its zero-area boundary
cases, says
\[
|B_0+B_2|^{1/2}\geq |B_0|^{1/2}+|B_2|^{1/2}.
\tag{18}
\]
Area scales quadratically, so the factor \(1/2\) in the midpoint set
becomes the factor \(1/4\) in area:
\[
\left|\frac{B_0+B_2}{2}\right|
=\frac14|B_0+B_2|
\geq
\frac{(\sqrt{|B_0|}+\sqrt{|B_2|})^2}{4}
\geq
\frac{(\sqrt{\beta_0}+\sqrt{\beta_2})^2}{4}.
\tag{19}
\]
Equations (17)--(19) hold for every \(P\) containing \(z\), and hence
prove (3). They also show explicitly that both endpoint caps use the same
lower-cap orientation; no opposite cap is inserted into the Minkowski sum.

We next prove the exact endpoint-region membership. Fix
\[
0<b\leq\min\{\beta_0,\beta_2\},
\]
\(q\in\mathbb S^1\), and \(u\in[0,b]\). The lower cap through \(x_i\)
contains \(x_i\), so
\[
F_{i,q}(q\cdot x_i)\geq d_{A_i}(x_i)\geq\beta_i.
\tag{20}
\]
The quantile properties in accepted fact `17ca54faa05ad878` therefore give
\[
Q_{0,q}(u)\leq q\cdot x_0,\qquad
Q_{2,q}(b-u)\leq q\cdot x_2.
\tag{21}
\]
This includes \(u=0\) and \(u=b\): at zero individual demand,
\(Q_{i,q}(0)=\min_{A_i}q\cdot w\), so (21) remains the finite
support-endpoint inequality. Adding (21) gives
\[
Q_{0,q}(u)+Q_{2,q}(b-u)
\leq q\cdot x_0+q\cdot x_2
=2q\cdot z.
\tag{22}
\]
Thus every constraint in (4) holds and \(z\in\mathcal E(b)\). If \(b=0\),
one must not substitute the two finite support endpoints into (4);
the total zero-demand convention is instead (5), which immediately gives
\(z\in\mathcal E(0)\). This proves (6) on its full closed interval.

For the centroid specialization, the planar Grünbaum content of accepted
fact `2f9be517307232c7` gives
\[
d_{A_i}(g_i)\geq\frac{4a_i}{9},
\qquad i\in\{0,2\}.
\tag{23}
\]
Taking \(\beta_i=4a_i/9\) in (3) gives
\[
d_{A_1}(z_0)\geq
\frac{(\sqrt{a_0}+\sqrt{a_2})^2}{9}
=\frac{(\sqrt M+\sqrt m)^2}{9}.
\tag{24}
\]
Taking
\[
b=\frac{4m}{9}
=\min\left\{\frac{4a_0}{9},\frac{4a_2}{9}\right\}
\tag{25}
\]
in (6) gives \(z_0\in\mathcal E(4m/9)\). Compatibility (1) also gives
\(z_0\in A_1\).

We now transfer the two payments to every three-dimensional halfspace and
check the slopes. For a fixed \(q\), use the endpoint infimal convolution
from accepted fact `17ca54faa05ad878`,
\[
I_q(s)=\inf_{c\in\mathbb R}
\left(F_{0,q}(c)+F_{2,q}(s-c)\right),
\tag{26}
\]
and its attained threshold
\[
R_q(b)=
\max_{0\leq u\leq b}
\left(Q_{0,q}(u)+Q_{2,q}(b-u)\right).
\tag{27}
\]
That fact proves the exact superlevel identity
\[
\{s:I_q(s)\geq b\}=[R_q(b),\infty)
\qquad(0<b\leq m).
\tag{28}
\]
By the definition of \(\mathcal E(b)\) in accepted fact
`66f17f4981c30108`, membership of \(z_0\) gives
\[
2q\cdot z_0\geq R_q(4m/9).
\]
Equations (25) and (28) therefore imply
\[
I_q(2q\cdot z_0)\geq\frac{4m}{9}.
\tag{29}
\]

To see directly which halfspaces (29) controls, a nonhorizontal closed
halfspace whose boundary contains \((1,z_0)\) can, after positive
normalization, be written
\[
H_{q,\lambda}=
\{(h,w):q\cdot w+\lambda(h-1)\leq q\cdot z_0\}.
\tag{30}
\]
Its cap thresholds at heights \(0,1,2\) are respectively
\[
q\cdot z_0+\lambda,\qquad
q\cdot z_0,\qquad
q\cdot z_0-\lambda.
\tag{31}
\]
The endpoint thresholds in (31) sum to \(2q\cdot z_0\), with the same
lower-cap orientation as (14)--(15). Hence (26) and (29) give, for every
\(\lambda\),
\[
F_{0,q}(q\cdot z_0+\lambda)
+F_{2,q}(q\cdot z_0-\lambda)
\geq\frac{4m}{9}.
\tag{32}
\]
The middle threshold in (31), together with (24), gives
\[
F_{1,q}(q\cdot z_0)
\geq\frac{(\sqrt M+\sqrt m)^2}{9}.
\tag{33}
\]
Thus every halfspace in (30) has total slice mass at least
\[
\frac{(\sqrt M+\sqrt m)^2+4m}{9}.
\tag{34}
\]

Any nonhorizontal halfspace containing \((1,z_0)\) contains the parallel
halfspace obtained by moving its boundary to \((1,z_0)\), so (34) also
holds without the boundary-incidence assumption. A horizontal halfspace
containing \((1,z_0)\) contains either both slices \(0,1\), or both slices
\(1,2\); its mass is therefore at least \(a_0+a_1\) or at least
\(a_1+a_2\), respectively. This is exactly the horizontal/nonhorizontal
decomposition in accepted fact `d2d117bcc58a1ba0`. Taking the infimum over
all containing halfspaces proves (8).

The third term in (8) is at least \(2T/9\) exactly when
\[
M+5m+2\sqrt{Mm}\geq2(M+m+a_1),
\]
which rearranges without relaxation to (9). If some \(a_i\geq T/2\),
accepted fact `2f9be517307232c7` already proves the locked target. Otherwise
all \(a_i<T/2\), so
\[
a_0+a_1=T-a_2>\frac T2>\frac{2T}{9},\qquad
a_1+a_2=T-a_0>\frac T2>\frac{2T}{9}.
\tag{35}
\]
Under (9), (8) and (35) show that \((1,z_0)\) itself has depth at least
\(2T/9\). This proves the claimed unconditional conclusion from (9).

It remains to audit the normalized region. Dividing (9) by \(M>0\) gives
(11). Its right-hand side permits \(s>0\) exactly when
\[
3r+2\sqrt r-1>0
\quad\Longleftrightarrow\quad
(3\sqrt r-1)(\sqrt r+1)>0
\quad\Longleftrightarrow\quad
r>\frac19.
\tag{36}
\]
If the large-slice criterion does not already apply, then \(M<T/2\) and
\(a_1<T/2\); after normalization these are exactly
\[
s>1-r,\qquad s<1+r,
\]
while \(m<T/2\) follows automatically from \(m\leq M<T/2\). This proves
(12).

Finally, the upper boundary in (11),
\[
U(r)=\sqrt r+\frac{3r-1}{2},
\]
lies above the strict lower residual boundary exactly when
\[
U(r)>1-r
\quad\Longleftrightarrow\quad
5r+2\sqrt r-3>0
\quad\Longleftrightarrow\quad
(5\sqrt r-3)(\sqrt r+1)>0
\quad\Longleftrightarrow\quad
r>\frac9{25}.
\tag{37}
\]
Also
\[
U(r)-(1+r)
=\frac{(\sqrt r-1)(\sqrt r+3)}2\leq0
\qquad(0<r\leq1),
\tag{38}
\]
with equality only at \(r=1\). Equations (37)--(38) prove the exact
intersection (13), including the strict residual upper boundary at
\(r=1\). The new curve meets the lower residual boundary at \(r=9/25\),
lies strictly between the two residual boundaries for \(9/25<r<1\), and
meets the upper residual boundary at \(r=1\).

## External sources

none
