---
fact_id: ee3a0b6f59ee7aeb
kind: counterexample
author: "r131-effective-segment"
assurance: LLM-verified
subgoal_id: r131-endpoint-or-centroid-segment
depends_on: ["15bb2c1680a0254e"]
source_packet_sha256: 4feea407c66a6d30c8afcc9ed27058302b7292ad5ce7530770ae1e97281b1c12
verifier_run: a724211c76574c13
target_match: null
---

## Statement

Use coordinates \((x,u,v)\), with integer-height coordinate \(x\), and define
\[
\begin{aligned}
\Delta&=\operatorname{conv}\{(0,0),(1,0),(0,1)\},\\
K&=\operatorname{conv}\left\{\left(\frac15,0\right),(1,0),
  \left(\frac{27}{40},\frac{13}{40}\right)\right\},\\
d_0&=\frac{509999}{260000},\qquad d_2=\frac{10001}{260000},\\
A_0&=d_0K,\qquad A_1=\Delta,\qquad A_2=d_2K.
\end{aligned}
\]
Let \(C\) be the convex hull of \(\bigcup_{i=0}^2(\{i\}\times A_i)\), and let \(S=C\cap(\mathbb Z\times\mathbb R^2)\). This is a compact rational polytope with exactly the displayed nonempty two-dimensional integer-height sections.

Use the canonical notation \(a_i=|A_i|\), \(T=a_0+a_1+a_2\), \(M=\max\{a_0,a_2\}\), \(m=\min\{a_0,a_2\}\), and \(t=2T/9\). Then
\[
\begin{aligned}
a_0&=\frac{260098980001}{520000000000},&
a_1&=\frac12,&
a_2&=\frac{100020001}{520000000000},\\
T&=\frac{260099500001}{260000000000},&
t&=\frac{260099500001}{1170000000000}.
\end{aligned}
\]
These areas lie in the full strict residual strip of accepted fact 15bb2c1680a0254e.

For the planar centroids \(g_i\) of \(A_i\), define \(g_{\mathrm{mid}}=(g_0+g_2)/2\) and \(z_\theta=(1-\theta)g_1+\theta g_{\mathrm{mid}}\), for \(0\leq\theta\leq1\). Every \(z_\theta\) belongs to \(A_1\). Both endpoint slices fail the target uniformly:
\[
\begin{aligned}
\sup_{z\in A_0}h_S((0,z))
&\leq\frac{4a_0}{9}=t-\frac1{2250000}<t,\\
\sup_{z\in A_2}h_S((2,z))
&\leq\frac{4a_2}{9}=t-\frac{499999}{2250000}<t.
\end{aligned}
\]
Define two fixed closed halfspaces by
\[
\begin{aligned}
H_v&=\{(x,u,v):730297x+2400000v\geq1529997\},\\
H_u&=\{(x,u,v):22857671x+14040000u\geq27539946\}.
\end{aligned}
\]
Their exact masses and segment intersections are
\[
\begin{aligned}
\mathcal H_2(S\cap H_v)
&=\frac{256096009}{1152000000}
=t-\frac{5308961}{3120000000000}<t,\\
\mathcal H_2(S\cap H_u)
&=\frac{829036849}{3732480000}
  +\frac{100020001}{520000000000}
=t-\frac{107377213}{151632000000000}<t,\\
(1,z_\theta)\in H_v
&\quad\Longleftrightarrow\quad 0\leq\theta\leq\frac1{1800},\\
(1,z_\theta)\in H_u
&\quad\Longleftrightarrow\quad \frac1{1800}\leq\theta\leq1.
\end{aligned}
\]
Consequently \(h_S((1,z_\theta))<t\) for every \(\theta\in[0,1]\), despite the actual failure of both endpoint slices.

## Proof

First verify compatibility and the integer-height sections. Each vertex of \(K\) has nonnegative coordinates with coordinate sum at most one, so \(K\subseteq\Delta\). Its horizontal base has length \(4/5\) and its height is \(13/40\), giving \(|K|=13/100>0\). Both dilation factors are positive and satisfy \(d_0+d_2=2\). For every convex set \(B\) and positive \(p,q\), convexity gives \(pB+qB=(p+q)B\). Hence
\[
\frac{A_0+A_2}{2}
=\frac{d_0+d_2}{2}K
=K\subseteq A_1.
\]
The convex hull \(C\) is rational, compact, and contained between heights zero and two. Its sections at heights zero and two are exactly \(A_0\) and \(A_2\). In a convex combination grouped by the three heights, write the weights as \(\lambda_0,\lambda_1,\lambda_2\). At height one, the height equation and the sum of the weights imply \(\lambda_0=\lambda_2\). The planar component therefore has the form
\[
\lambda_1p_1+2\lambda_0\frac{p_0+p_2}{2},
\qquad p_i\in A_i,\qquad \lambda_1+2\lambda_0=1.
\]
The midpoint containment places this point in \(A_1\); conversely all of \(A_1\) occurs in \(C\). There are no other integer heights. Thus \(S\) has exactly the claimed slices, and each has positive area.

Area scales quadratically under dilation. Applying this to \(|K|=13/100\) gives the displayed \(a_0,a_2,T,t\). Here \(M=a_0\) and \(m=a_2\), and direct subtraction gives
\[
a_1-(M-m)=\frac1{500000}>0,
\qquad
(M+m)-a_1=\frac{99500001}{260000000000}>0.
\]
In the notation of accepted fact 15bb2c1680a0254e,
\[
r=\frac mM=\left(\frac{10001}{509999}\right)^2<\frac9{25},
\qquad
s=\frac{a_1}{M}=\frac{260000000000}{260098980001}.
\]
The two positive margins are exactly \(1-r<s<1+r\) after division by \(M\). Accepted fact 15bb2c1680a0254e identifies these as the full strict residual-strip conditions when \(0<r\leq9/25\). This range lies below its upper endpoint \(\rho=(27-2\sqrt{26})/25\), since \(\sqrt{26}<9\). Thus the example lies in the required strict residual regime.

We next give actual finite covers of both endpoint slices. Define the three affine barycentric functions of \(K\) by
\[
\begin{aligned}
\psi_1(u,v)&=\frac54(1-u-v),\\
\psi_2(u,v)&=-\frac14+\frac54u-\frac{95}{52}v,\\
\psi_3(u,v)&=\frac{40}{13}v.
\end{aligned}
\]
They sum to one, and their values at the ordered vertices \((1/5,0),(1,0),(27/40,13/40)\) are respectively the three coordinate unit vectors. They are therefore nonnegative on \(K\). For any \(z\in d_iK\), at least one \(\psi_j(z/d_i)\) is at least \(1/3\). For every \(j\), the set \(d_iK\cap\{\psi_j(z/d_i)\geq1/3\}\) is a triangle obtained by dilation of \(d_iK\) by \(2/3\) about its \(j\)-th vertex. Its exact area is \(4a_i/9\).

For \(j=1,2,3\), use the following actual closed halfspaces in three dimensions:
\[
\begin{aligned}
E_{0,j}&=\{(x,z):\psi_j(z/d_0)-2x\geq1/3\},\\
E_{2,j}&=\{(x,z):\psi_j(z/d_2)+100(x-2)\geq1/3\}.
\end{aligned}
\]
The first three cover \(\{0\}\times A_0\), and the last three cover \(\{2\}\times A_2\). We verify that each contains no point of either unwanted slice.

Since \(0<d_2<1\), \(K\subseteq\Delta\), and \(0\in\Delta\), one has \(A_2\subseteq\Delta\). Therefore every \(z=(u,v)\in A_1\cup A_2\) has \(u,v\geq0\) and \(u,v\leq1\). Because \(d_0>20/13>1\),
\[
\psi_1(z/d_0)\leq\frac54<2,\qquad
\psi_2(z/d_0)\leq-\frac14+\frac{5}{4d_0}<2,\qquad
\psi_3(z/d_0)\leq\frac{40}{13d_0}<2.
\]
At height one or two, subtracting \(2x\) makes every left side in the definition of \(E_{0,j}\) strictly less than zero. Hence \(E_{0,j}\) excludes both unwanted slices.

Every \(z=(u,v)\in A_0\cup A_1\) has \(u,v\geq0\), \(u\leq2\), and \(v\leq1\). Indeed \(d_0<2\), the maximum \(u\) of \(K\) is one, and its maximum \(v\) is \(13/40\). Also \(d_2>1/26\), so
\[
\begin{aligned}
\psi_1(z/d_2)&\leq\frac54<100,\\
\psi_2(z/d_2)&\leq-\frac14+\frac{5}{2d_2}
<-\frac14+65<100,\\
\psi_3(z/d_2)&\leq\frac{40}{13d_2}<80<100.
\end{aligned}
\]
At height one, the additional term \(100(x-2)\) is \(-100\), and at height zero it is \(-200\). Thus \(E_{2,j}\) also excludes both unwanted slices.

It follows that the exact slice masses of these six halfspaces are
\[
\mathcal H_2(S\cap E_{0,j})=\frac{4a_0}{9},
\qquad
\mathcal H_2(S\cap E_{2,j})=\frac{4a_2}{9}
\quad(j=1,2,3).
\]
Their respective target deficits, computed from the displayed areas, are \(1/2250000\) and \(499999/2250000\). Every point of each endpoint slice is contained in one of the corresponding halfspaces. This proves both uniform strict endpoint depth bounds, including their boundary points.

For the centroid segment, the centroid of a triangle is the average of its vertices. Hence
\[
g_K=\left(\frac58,\frac{13}{120}\right),\qquad
g_1=\left(\frac13,\frac13\right),\qquad
g_{\mathrm{mid}}=\frac{d_0+d_2}{2}g_K=g_K.
\]
Both \(g_K\) and \(g_1\) belong to \(\Delta\), so the entire closed segment belongs to \(A_1\). Its exact parametrization is
\[
z_\theta
=\left(\frac13+\frac7{24}\theta,\,
        \frac13-\frac9{40}\theta\right).
\]
At height one, \(H_v\) is the halfplane \(v\geq7997/24000\), and \(H_u\) is the halfplane \(u\geq14407/43200\). Substituting this parametrization gives their asserted parameter intervals, since
\[
\frac13-\frac9{40}\frac1{1800}=\frac{7997}{24000},
\qquad
\frac13+\frac7{24}\frac1{1800}=\frac{14407}{43200}.
\]
The shared parameter belongs to both closed halfspaces.

It remains to verify the full masses of these two halfspaces. The thresholds for \(H_v\) at heights zero, one, and two are respectively
\[
v\geq\frac{509999}{800000},\qquad
v\geq\frac{7997}{24000},\qquad
v\geq\frac{69403}{2400000}.
\]
The first threshold equals the maximum \(v\)-coordinate \(d_0(13/40)\) of \(A_0\), so that intersection has area zero. The maximum \(v\)-coordinate of \(A_2\) is
\[
d_2\frac{13}{40}
=\frac{10001}{800000}
=\frac{30003}{2400000}
<\frac{69403}{2400000},
\]
so the height-two intersection is empty. For \(0\leq c\leq1\), the cap \(\Delta\cap\{v\geq c\}\) has area \((1-c)^2/2\). Thus
\[
\mathcal H_2(S\cap H_v)
=0+\frac12\left(1-\frac{7997}{24000}\right)^2+0
=\frac{256096009}{1152000000}.
\]
Exact subtraction from \(t\) gives \(5308961/3120000000000>0\).

The thresholds for \(H_u\) at heights zero, one, and two are respectively
\[
u\geq\frac{509999}{260000},\qquad
u\geq\frac{14407}{43200},\qquad
u\geq-\frac{4543849}{3510000}.
\]
The first threshold equals the maximum \(u\)-coordinate \(d_0\) of \(A_0\), so that intersection has area zero. Every point of \(A_2\) has \(u\geq d_2/5>0\), so the last halfplane contains all of \(A_2\). The middle cap has area \((1-14407/43200)^2/2\). Therefore
\[
\mathcal H_2(S\cap H_u)
=0+\frac12\left(1-\frac{14407}{43200}\right)^2+a_2
=\frac{829036849}{3732480000}
 +\frac{100020001}{520000000000}.
\]
Exact subtraction from \(t\) gives \(107377213/151632000000000>0\).

All intersections confined to support lines have zero planar area, despite the use of closed halfspaces. The two exact mass calculations therefore include the entire contribution from every slice. Their parameter intervals cover \([0,1]\); hence every point of the centroid segment belongs to an actual halfspace of mass strictly below \(t\). Combined with the verified finite endpoint covers, this proves the counterexample to the combined assertion.

As an independent arithmetic check, SageMath 10.8 was invoked with \(\texttt{sage --nodotsage --python -}\). Using \(\texttt{Polyhedron}\) over \(\mathbb Q\), it verified the areas, the strict residual margins, the centroid crossing, every slice intersection for \(H_v,H_u\), and every slice intersection for all six \(E_{i,j}\). Every assertion passed and the command exited zero. The explicit argument above proves the claims without relying on floating-point evidence.

## External sources

none
