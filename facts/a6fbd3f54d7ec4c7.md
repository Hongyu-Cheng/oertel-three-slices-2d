---
fact_id: a6fbd3f54d7ec4c7
kind: lemma
author: "mp_r261_five_cap"
assurance: LLM-verified
subgoal_id: five-cap-affine-normal-form
depends_on: ["2f9be517307232c7","9b0c3eb7dcfba2c2"]
source_packet_sha256: 12a62bc85d5447e5097f2cb232f6cd4463de9a4fcd646b0cfa99c03db10a4cd4
verifier_run: b1ef2c8c0bcf4ffa
target_match: null
---

## Statement

Assume the locked problem.  Put
\[
\mu(H)=\mathcal H_2(S\cap H),\qquad
q=\frac{2T}{9}.
\]
Suppose five closed halfspaces cover \(S\) and each has mass strictly
below \(q\).  Then, after replacing them by arbitrarily small outward
parallel perturbations, relabeling them, and possibly applying the
reflection \(h\mapsto2-h\), there are closed halfspaces
\(H_1,\ldots,H_5\) with the following properties.

First, their interiors form a minimal cover of \(S\).  Each \(H_j\) has
a private witness
\[
p_j\in S\cap\operatorname{int}H_j,\qquad
p_j\notin\bigcup_{\ell\ne j}\operatorname{int}H_\ell.
\tag{1}
\]
All five halfspaces have nonzero planar normals.

Write
\[
m=|A_0|,\qquad k=|A_1|,\qquad M=|A_2|,
\qquad T=m+k+M.
\tag{2}
\]
Then
\[
m<M,\qquad \frac T3<M<\frac T2,
\qquad |A_i|<\frac T2\quad(i=0,1,2).
\tag{3}
\]

There are pairwise nonparallel nonconstant affine functions
\(f_1,f_2,f_3:\mathbb R^2\to\mathbb R\) and real slopes
\(s_1,s_2,s_3\) such that
\[
f_1+f_2+f_3=-1,\qquad
\sigma:=s_1+s_2+s_3>1,
\tag{4}
\]
\[
H_j=\{(h,z):f_j(z)+(h-1)s_j\le0\},
\qquad j=1,2,3.
\tag{5}
\]
Consequently the first three interiors cover the whole planes at heights
\(0\) and \(1\).  At height \(2\), their common closed complementary
region
\[
Q=\bigcap_{j=1}^3\{z:f_j(z)+s_j\ge0\}
\tag{6}
\]
is a nondegenerate bounded triangle.

There are nonconstant affine functions \(g_4,g_5\) and real slopes
\(t_4,t_5\) such that
\[
H_j=\{(h,z):g_j(z)+(h-2)t_j\le0\},
\qquad j=4,5.
\tag{7}
\]
For
\[
R=A_2\cap Q
\tag{8}
\]
one has
\[
R\subseteq\{g_4<0\}\cup\{g_5<0\},
\qquad
\frac T3<|R|<\frac{4T}{9}.
\tag{9}
\]
The witnesses \(p_4,p_5\) lie in \(\{2\}\times R\).

The five mass inequalities are the literal section inequalities
\[
\begin{aligned}
&|A_0\cap\{f_j-s_j\le0\}|
+|A_1\cap\{f_j\le0\}|
+|A_2\cap\{f_j+s_j\le0\}|<q,
&&j=1,2,3,\\
&|A_0\cap\{g_j-2t_j\le0\}|
+|A_1\cap\{g_j-t_j\le0\}|
+|A_2\cap\{g_j\le0\}|<q,
&&j=4,5.
\end{aligned}
\tag{10}
\]

The normal form has the following exhaustive selection rule: use
alternative 1 when it holds; if it does not hold, alternative 2 holds.

1. The interiors of \(H_4,H_5\) cover \(A_2\).  Necessarily
   \[
   M<\frac{4T}{9}.
   \tag{11}
   \]
2. For some \(r\in\{1,2,3\}\), the height-\(2\) interiors of
   \(H_r,H_4,H_5\) cover the whole plane, no pair among them does, and
   there are positive constants \(\lambda_r,\lambda_4,\lambda_5\) such
   that
   \[
   \lambda_r(f_r+s_r)+\lambda_4g_4+\lambda_5g_5=-1.
   \tag{12}
   \]

In particular, only alternative 2 is possible when \(M\ge4T/9\).

Let \(N_{123}\) and \(N_{45}\) denote the closed-section multiplicities
of the indicated halfspace families.  Up to the null boundary lines of
\(Q\), the exact slice surpluses are
\[
\begin{aligned}
E_0&=\int_{A_0}(N_{123}-1)+\int_{A_0}N_{45},\\
E_1&=\int_{A_1}(N_{123}-1)+\int_{A_1}N_{45},\\
E_2&=\int_{A_2\setminus Q}(N_{123}-1)
    +\int_{A_2\setminus Q}N_{45}
    +\int_R(N_{45}-1).
\end{aligned}
\tag{13}
\]
Every integrand in (13) is nonnegative and
\[
E_0+E_1+E_2
=\sum_{j=1}^5\mu(H_j)-T
<\frac T9.
\tag{14}
\]

For \(j=1,2,3\), define
\[
\begin{aligned}
x_j&=|A_0\cap\{f_j-s_j\le0\}|,\\
b_j&=|A_1\cap\{f_j\le0\}|,\\
y_j&=|A_2\cap\{f_j+s_j\le0\}|,
\end{aligned}
\tag{15}
\]
and the same-index midpoint-graph mass
\[
d_j=
\int_{A_0\times A_2}
\mathbf 1_{\{f_j((z_0+z_2)/2)\le0\}}\,dz_0\,dz_2.
\tag{16}
\]
Then
\[
Mx_j+my_j\ge d_j,\qquad
\delta_j:=x_j+y_j-\frac{d_j}{M}\ge0.
\tag{17}
\]
If
\[
N(z)=\sum_{j=1}^3\mathbf 1_{\{f_j(z)\le0\}},
\qquad
\mathcal Q=
\int_{A_0\times A_2}
\left(N\left(\frac{z_0+z_2}{2}\right)-1\right)\,dz_0\,dz_2,
\tag{18}
\]
then
\[
\sum_{j=1}^3d_j=mM+\mathcal Q
\tag{19}
\]
and the first three masses satisfy the exact identity
\[
\sum_{j=1}^3\mu(H_j)
=k+m+
\left(\sum_{j=1}^3b_j-k\right)
+\frac{\mathcal Q}{M}
+\sum_{j=1}^3\delta_j.
\tag{20}
\]
Hence every such normal form necessarily satisfies
\[
\left(\sum_{j=1}^3b_j-k\right)
+\frac{\mathcal Q}{M}
+\sum_{j=1}^3\delta_j
<
\frac{2M-k-m}{3},
\tag{21}
\]
while its three individual inequalities are equivalently
\[
b_j+\frac{d_j}{M}+\delta_j<q
\qquad(j=1,2,3).
\tag{22}
\]

Conversely, suppose actual nonempty two-dimensional convex bodies
\(A_0,A_1,A_2\) satisfy
\[
\frac{A_0+A_2}{2}\subseteq A_1,
\tag{23}
\]
and actual affine functions and slopes satisfy (4)--(10).  Then the five
halfspaces (5) and (7) cover \(S\) by their interiors and have mass below
\(q\).  Thus any exact rational polygonal realization of these conditions
is a finite exact disproof of the locked theorem.

Moreover, in the range \(M<4T/9\), the last two halfspaces impose no
additional existence obstruction.  Given any realization of the first
three halfspaces in (4)--(6) and their three inequalities in (10), two
further halfspaces of mass below \(q\), empty on \(A_0,A_1\), can be
chosen whose height-\(2\) interiors cover the entire plane.

## Proof

### Interior-minimal perturbation

Apply the outward perturbation from accepted fact
`9b0c3eb7dcfba2c2` to each member of the original cover.  The offsets
may be chosen so small that every mass remains below \(q\), every point
which was in a closed halfspace is in the interior of its perturbed
halfspace, and no horizontal boundary is one of the support planes
\(h=0,1,2\).  Rename the perturbed halfspaces \(H_1,\ldots,H_5\).

No four interiors cover \(S\), because their closed halfspaces would give
\[
T\le\sum_{j=1}^4\mu(H_j)<4q=\frac{8T}{9}.
\tag{24}
\]
Thus all five are necessary.  Removing \(H_j\) from the interior cover
leaves some point uncovered; the full cover places that point in
\(\operatorname{int}H_j\).  This proves the private-witness assertion
(1).

For each slice \(i\), put
\[
P_{ij}=\{z:(i,z)\in\operatorname{int}H_j\},
\qquad
F_{ij}=\mathbb R^2\setminus P_{ij}.
\]
The family
\[
\{A_i,F_{i1},\ldots,F_{i5}\}
\tag{25}
\]
has empty intersection.  Planar Helly gives an empty subfamily of at
most three members.  If it contains \(A_i\), at most two of the
\(P_{ij}\) cover \(A_i\).  If it does not contain \(A_i\), at most three
of the \(P_{ij}\) cover the whole plane.  This proves the slice-wise
Helly alternative, including empty, full, and horizontal sections.

Every slice has area below \(T/2\).  Its centroid belongs to one of the
five halfspaces.  If that halfspace has nonzero planar normal, the planar
Grünbaum inequality in accepted fact `2f9be517307232c7` gives section
area at least \(4|A_i|/9\).  If its planar normal is zero, its section is
the whole slice and the same lower bound is immediate.  Therefore
\[
\frac49|A_i|\le\mu(H_j)<\frac{2T}{9},
\]
which proves the last part of (3).

### The middle Helly witness

No one or two interiors can cover \(A_1\).  Suppose a subfamily
\(\mathcal J\) of at most two does.  If it failed to cover both endpoint
bodies, choose \(z_0\in A_0,z_2\in A_2\) outside all interiors in
\(\mathcal J\).  For affine defining functions \(L_j\) oriented so that
\(\operatorname{int}H_j=\{L_j<0\}\),
\[
L_j(0,z_0)\ge0,\qquad L_j(2,z_2)\ge0.
\]
Compatibility puts \((z_0+z_2)/2\) in \(A_1\), while affinity gives
\[
L_j\left(1,\frac{z_0+z_2}{2}\right)
=\frac{L_j(0,z_0)+L_j(2,z_2)}2\ge0,
\]
a contradiction.  Thus \(\mathcal J\) also covers one endpoint body,
say \(A_\ell\), and
\[
|A_1|+|A_\ell|
\le\sum_{j\in\mathcal J}\mu(H_j)
<2q=\frac{4T}{9}.
\]
The remaining slice would have area greater than \(5T/9\), contradicting
(3).

The height-\(1\) instance of the Helly alternative therefore supplies
exactly three interiors which cover the whole plane.  Relabel them
\(H_1,H_2,H_3\).  No pair covers either the plane or \(A_1\).  A zero
planar normal would make its middle section empty or the whole plane,
both impossible here.

The three planar normals are pairwise nonparallel.  If two were positive
multiples, one negative halfplane would be redundant.  If they were
oppositely directed, their closed complements would be disjoint, a
strip, or a line.  The disjoint case gives a two-halfplane cover; a
third nonparallel closed halfplane meets every strip or line; and if all
three are parallel, one-dimensional Helly again supplies a two-member
cover.

The three closed complements have empty intersection, minimally.
Affine Farkas therefore gives strictly positive multipliers whose
weighted sum has zero linear part and a negative constant part.
Positive rescaling and a common normalization give (4).  Extending the
three middle defining functions in the height direction gives (5).

The midpoint argument shows that the first three interiors cover at
least one endpoint body.  They do not cover both, since otherwise three
halfspaces of total mass below \(3q=2T/3<T\) would cover \(S\).  Exchange
the endpoint labels if necessary so that they cover \(A_0\) and fail to
cover \(A_2\).

Their first two covered slices give
\[
m+k\le\sum_{j=1}^3\mu(H_j)<3q=\frac{2T}{3},
\]
so \(M>T/3\).  Compatibility and planar Brunn--Minkowski give
\[
\sqrt{k}\ge\frac{\sqrt m+\sqrt M}{2},
\qquad\text{hence}\qquad k\ge\sqrt{mM}.
\]
If \(m\ge M\), then \(m,k\ge M\), contradicting \(M>T/3\).
Thus \(m<M\).  The upper bound \(M<T/2\) was proved above, establishing
(3).

### Slope sum, the triangular hole, and the last two rows

Put \(\sigma=\sum_js_j\).  If \(\sigma\le1\), then
\[
\sum_{j=1}^3(f_j+s_j)=-1+\sigma\le0,
\]
so the three closed height-\(2\) sections cover the whole plane.  They
already cover \(A_0,A_1\), giving
\(\sum_{j=1}^3\mu(H_j)\ge T\), a contradiction.  Hence
\(\sigma>1\).  At heights \(0\) and \(1\),
\[
\sum_{j=1}^3(f_j-s_j)=-1-\sigma<0,\qquad
\sum_{j=1}^3f_j=-1<0,
\]
so their interiors cover both entire planes.

The affine map
\[
z\longmapsto(f_1(z),f_2(z),f_3(z))
\]
is a bijection from \(\mathbb R^2\) onto the plane
\(x_1+x_2+x_3=-1\).  Thus \(Q\) in (6) is the affine inverse image of
\[
\{x_1,x_2,x_3\ge0:x_1+x_2+x_3=\sigma-1\},
\]
a nondegenerate bounded triangle.

No point of \(R=A_2\cap Q\) belongs to the interior of any of the first
three halfspaces.  The full interior cover therefore makes
\(H_4,H_5\) cover \(R\).  The private witnesses for \(H_4,H_5\) cannot
lie on the first two slices, which the first three interiors cover
entirely.  Hence they lie in \(\{2\}\times R\).  A horizontal halfspace
has empty or full height-\(2\) interior.  The first option has no private
witness, and the second prevents the other remaining halfspace from
having one.  Thus both planar normals are nonzero, and (7)--(9) follow.

The first three halfspaces cover \(A_0,A_1,A_2\setminus Q\), whereas
the last two cover \(R\).  Therefore
\[
T-|R|\le\sum_{j=1}^3\mu(H_j)<3q=\frac{2T}{3},
\]
\[
|R|\le\mu(H_4)+\mu(H_5)<2q=\frac{4T}{9}.
\]
This proves the strict area window in (9).

Apply planar Helly to (25) at height \(2\).  Every resulting subcover of
\(A_2\) must contain both \(H_4,H_5\), because of their private witnesses.
If the Helly subfamily contains \(A_2\), at most two interiors cover
\(A_2\), so they are precisely \(H_4,H_5\), giving alternative 1 and
(11).  Otherwise at most three interiors cover the whole plane.  If
\(H_4,H_5\) alone do so, alternative 1 again applies.  In the remaining
case the plane cover is \(H_r,H_4,H_5\) for some \(r\le3\).  A pair
cannot cover the plane, since it would cover \(A_2\) while omitting one
of its private witnesses.  The same minimal affine Farkas argument gives
the positive normalization (12).  This proves the dichotomy.

### Exact surplus and midpoint identities

The five strict mass inequalities imply
\[
0\le\sum_{j=1}^5\mu(H_j)-T
<5q-T=\frac T9.
\]
On \(A_0,A_1\), \(N_{123}\ge1\).  On \(A_2\setminus Q\),
\(N_{123}\ge1\), and on \(R\), \(N_{45}\ge1\).  Splitting the
multiplicity integral over these regions proves the nonnegative
decomposition (13)--(14).

For \(j\le3\), if
\[
f_j\left(\frac{z_0+z_2}{2}\right)\le0,
\]
then
\[
\frac{(f_j(z_0)-s_j)+(f_j(z_2)+s_j)}2\le0.
\]
At least one endpoint slack is nonpositive.  Integrating the resulting
indicator inequality over \(A_0\times A_2\) gives
\[
Mx_j+my_j\ge d_j.
\]
Since \(m<M\),
\[
x_j+y_j
\ge x_j+\frac mM y_j
\ge\frac{d_j}{M},
\]
which proves (17).

Equation (4) gives \(N\ge1\).  Summing (16) over \(j\) and using the
definition of \(\mathcal Q\) gives
\[
\sum_jd_j
=\int_{A_0\times A_2}N\left(\frac{z_0+z_2}{2}\right)
=mM+\mathcal Q.
\]
Finally,
\[
\begin{aligned}
\sum_{j=1}^3\mu(H_j)
&=\sum_j b_j+\sum_j(x_j+y_j)\\
&=\sum_jb_j+\frac1M\sum_jd_j+\sum_j\delta_j,
\end{aligned}
\]
which is (20).  Combining (20) with
\(\sum_{j=1}^3\mu(H_j)<3q\) gives (21), and (22) is the memberwise
version of the same identity.

### Converse and the independent two-cap completion

Assume (4)--(10) and compatibility (23).  Equations (4) and
\(\sigma>1\) make the first three interiors cover the planes at heights
\(0,1\).  At height \(2\), every point outside \(Q\) satisfies
\(f_j+s_j<0\) for some \(j\le3\), while (9) covers every point of
\(R=A_2\cap Q\) by \(H_4\) or \(H_5\).  Thus the five interiors cover
\(S\), and (10) gives their strict masses.

For the last assertion, assume \(M<4T/9\).  Choose a nonzero vector \(u\)
and an area-bisecting line \(\{u\cdot z=c\}\) of \(A_2\).  Since
\[
\frac M2<q,
\]
continuity of cap area permits \(\varepsilon>0\) such that both
\[
A_2\cap\{u\cdot z\le c+\varepsilon\},
\qquad
A_2\cap\{u\cdot z\ge c-\varepsilon\}
\]
have area below \(q\).  Their interiors cover the whole plane.  Lift
them as
\[
u\cdot z\le c+\varepsilon+L(h-2),
\]
\[
-u\cdot z\le-c+\varepsilon+L'(h-2).
\]
For sufficiently large \(L,L'>0\), the height-\(0\) and height-\(1\)
sections miss the compact bodies \(A_0,A_1\).  The two three-dimensional
halfspaces therefore have mass below \(q\), are empty on the first two
slices, and cover the entire third slice by their interiors.

This completes the normal-form reduction and its converse.

LIMITATION

The lemma does not prove that the system (4)--(10) is infeasible.  When
\(M<4T/9\), exclusion still requires ruling out the first three
lifting-aware inequalities in (10); the independent completion above
then supplies the other two halfspaces.  When \(M\ge4T/9\), exclusion
must use the shared-row identity (12) together with the surplus
decomposition (13).  Neither branch is closed here.

## External sources

none
