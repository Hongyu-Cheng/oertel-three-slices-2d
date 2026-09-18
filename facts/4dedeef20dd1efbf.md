---
fact_id: 4dedeef20dd1efbf
kind: lemma
author: "/root/mp_r55_grunbaum_fan_rigidity"
assurance: LLM-verified
subgoal_id: canonical-all-double-sharp-escape-mod-shear
depends_on: ["043e84c0c8d6e05c","2f9be517307232c7","e1361027c1dda6fa","ecee03aff61db31e"]
source_packet_sha256: 24232e0648ea499dafa10c0a6d1186c698db960a26c6852030f19f946e947152
verifier_run: 08bc87b7c47e4fe6
target_match: null
---

## Statement

No genuine escape subsequence from accepted fact `043e84c0c8d6e05c`
exists.  More precisely, suppose such a subsequence is fixed, and let
\(\widehat K_n\) be its gauged middle bodies.  There are affine maps \(G_n\)
such that, after passing to a subsequence,
\[
K_n:=G_n\widehat K_n\longrightarrow K
\tag{1}
\]
in Hausdorff distance, where \(K\) is a two-dimensional compact convex body.
Compose the middle affine functions with \(G_n^{-1}\), retaining the notation
\(f_{i,n}\).  Then
\[
f_{1,n}+f_{2,n}+f_{3,n}=-1.
\tag{2}
\]
For \(H_{i,n}:=\{f_{i,n}\leq0\}\), every limiting marginal has area
\(4|K|/9\), and every limiting singleton cell has positive area.

In fact, if \(g\) is the centroid of \(K\), then \(K\) is a triangle and,
after relabeling its barycentric coordinates
\(\mu_1,\mu_2,\mu_3\),
\[
H_i=\{\mu_i\geq1/3\}\qquad(i=1,2,3).
\tag{3}
\]
The limiting singleton cells have area \(2|K|/9\), the limiting doubleton
cells have area \(|K|/9\), and the limiting triple cell has area zero.
Consequently,
\[
\rho=\lim_n\frac{r_n}{p_n}=0.
\tag{4}
\]

Moreover, there are common offsets \(a_n\to\infty\) such that
\[
K_n
\subseteq
\{f_{i,n}\leq a_n,\ i=1,2,3\}
\tag{5}
\]
and
\[
\frac{k_n}{r_n(1+3a_n)^2}\longrightarrow1.
\tag{6}
\]
Equation (6) contradicts accepted fact `043e84c0c8d6e05c`.  Therefore the
two diameter sequences in its shear gauge are both bounded.  Since the
gauged outer body contains the origin and the gauged middle body contains a
fixed disk, both families lie in fixed compact sets.  By accepted fact
`ecee03aff61db31e`, this shear preserves every slice area and halfspace
depth.

## Proof

We first justify the compact affine normalization in (1).  For every \(n\),
let \(E_n\) be the John ellipse of the two-dimensional convex body
\(\widehat K_n\).  Choose \(G_n\) to send \(E_n\) to the closed unit disk
\(B\).  The planar John inclusions give
\[
B\subseteq K_n\subseteq2B.
\tag{7}
\]
The family of nonempty compact convex subsets of \(2B\) is Hausdorff
precompact.  Pass to a convergent subsequence.  The inclusions in (7) pass to
the limit, so
\[
B\subseteq K\subseteq2B.
\tag{8}
\]
Thus the limit is compact and has nonempty interior.  Every \(G_n\) has one
constant nonzero area multiplier.  It preserves all cell-area ratios,
affine-function signs, the identity (2), and common-offset containments.

Accepted fact `043e84c0c8d6e05c` gives
\[
\frac{k_n}{p_n}\longrightarrow1,
\qquad
\frac{c_{i,n}}{p_n}\longrightarrow\frac49.
\tag{9}
\]
Since \(0\leq r_n\leq k_n\), pass to a further subsequence, if necessary,
so that \(r_n/p_n\) has a limit \(\rho\).  We prove below that this limit is
zero.  Therefore, after the affine normalization,
\[
\frac{|K_n\cap H_{i,n}|}{|K_n|}
\longrightarrow\frac49.
\tag{10}
\]
Let \(C_{i,n}\) be the exact singleton cell with index \(i\).  Equation (2)
makes the all-complement cell empty.  Hence, for
\(\{i,j,k\}=\{1,2,3\}\), inclusion-exclusion gives
\[
|C_{i,n}|
=|K_n|-|K_n\cap H_{j,n}|-|K_n\cap H_{k,n}|
+|K_n\cap H_{j,n}\cap H_{k,n}|,
\]
and consequently
\[
\liminf_n\frac{|C_{i,n}|}{|K_n|}\geq\frac19.
\tag{11}
\]
Thus both sides of every boundary line meet
\(\operatorname{int}K_n\).

Put
\[
L_{i,n}=\|\nabla f_{i,n}\|,\qquad
S_n=L_{1,n}+L_{2,n}+L_{3,n},
\]
\[
b_{i,n}=\frac{L_{i,n}}{S_n},\qquad
\phi_{i,n}=\frac{f_{i,n}}{L_{i,n}},\qquad
c_n=\frac1{S_n}.
\tag{12}
\]
The singleton bound (11) ensures \(L_{i,n}>0\).  Each \(\phi_{i,n}\) has
unit linear part, and (2) becomes
\[
\sum_{i=1}^3b_{i,n}\phi_{i,n}=-c_n,
\qquad
b_{i,n}>0,\qquad
\sum_{i=1}^3b_{i,n}=1.
\tag{13}
\]
Every zero line meets \(K_n\subseteq2B\), so the constant terms of the
\(\phi_{i,n}\) are bounded.  Evaluating (13) at the origin also bounds
\(c_n\).  Pass to a further subsequence on which
\[
\phi_{i,n}\longrightarrow\phi_i,\qquad
b_{i,n}\longrightarrow b_i,\qquad
c_n\longrightarrow c,
\tag{14}
\]
where \(b_i\geq0\), \(\sum_i b_i=1\), and \(c\geq0\).  The convergence of
the affine functions is locally uniform.  Away from \(\partial K\) and the
three limiting lines, body and halfplane membership stabilizes.  These sets
have planar area zero, so dominated convergence and (10) give
\[
|K\cap H_i|=\frac49|K|,
\qquad
H_i=\{\phi_i\leq0\}.
\tag{15}
\]

We next use only the inequality part of Grünbaum to locate the centroid.
Let \(g\) be the centroid of \(K\).  We claim
\[
\phi_i(g)\geq0\qquad(i=1,2,3).
\tag{16}
\]
If \(\phi_i(g)<0\), the parallel halfplane
\[
H_i'=\{\phi_i\leq\phi_i(g)\}
\]
has boundary through \(g\).  Accepted fact `2f9be517307232c7` gives
\(|K\cap H_i'|\geq4|K|/9\).  Since \(g\in\operatorname{int}K\), the strip
\(\{\phi_i(g)<\phi_i<0\}\) has positive intersection area with \(K\).
Therefore
\[
|K\cap H_i|>|K\cap H_i'|\geq\frac49|K|,
\]
contrary to (15).  This proves (16).

Passing (13) to the limit and evaluating at \(g\) gives
\[
\sum_i b_i\phi_i(g)=-c.
\tag{17}
\]
Equations (16)-(17) imply
\[
c=0,\qquad
\phi_i(g)=0\quad\text{for every }i\text{ with }b_i>0.
\tag{18}
\]
In particular, \(S_n\to\infty\).

We now audit all coefficient supports.  There cannot be only one positive
\(b_i\), since the limiting identity
\(\sum_i b_i\phi_i=0\) would make a nonconstant \(\phi_i\) identically
zero.  Suppose exactly two coefficients, say \(b_1,b_2\), are positive.
Then
\[
b_1\phi_1+b_2\phi_2=0.
\tag{19}
\]
The two linear parts have norm one.  Hence \(b_1=b_2=1/2\) and
\(\phi_2=-\phi_1\).  The halfplanes \(H_1,H_2\) are complementary and their
intersection is one line.  Thus
\[
|K\cap H_1|+|K\cap H_2|=|K|,
\]
whereas (15) makes the left side \(8|K|/9\).  This contradiction excludes,
in particular, the limit in which one normalized coefficient vanishes and
the other two lines become opposite parallel.  Therefore
\[
b_1b_2b_3>0.
\tag{20}
\]
By (18), all three lines pass through \(g\).

We now apply the equality characterization, with its hypotheses made
explicit.  Translate \(g\) to the origin.  For each \(i\), choose a unit
vector \(\theta_i\) so that \(H_i-g=\theta_i^+\).  In Corollary 8 of
Myroshnychenko, Stephen, and Zhang, take
\[
n=k=2,\qquad E=\mathbb R^2,\qquad \theta=\theta_i.
\]
The body \(K-g\) is a convex body, its centroid is the origin, and the
required condition
\[
g(K-g)\in E\cap\theta_i^\perp
\]
holds.  The denominator in that corollary is
\(\operatorname{area}(K-g)\), and (15) is equality in its bound
\((2/3)^2=4/9\).  The equality statement specializes to
\[
K-g=\operatorname{conv}\left(-\frac12z+D_0,\ z\right),
\tag{21}
\]
where \(\langle z,\theta_i\rangle>0\) and \(D_0\) is a one-dimensional
convex body in \(\theta_i^\perp\).  Hence \(K\) is a nondegenerate triangle,
\(-z/2+D_0\) is its side parallel to the boundary of \(H_i\), and \(z\) is
the opposite vertex lying in \(H_i\).  Thus \(H_i\) is a centroidal vertex
cap.  This argument applies to every \(i\).

A fixed triangle has exactly three centroidal vertex caps.  Let
\(\mu_1,\mu_2,\mu_3\) be its barycentric coordinates and put
\[
q_j=\frac13-\mu_j.
\tag{22}
\]
Then
\[
\{q_j\leq0\}=\{\mu_j\geq1/3\},
\qquad
q_1+q_2+q_3=0.
\tag{23}
\]
Each \(\phi_i\) is a positive multiple of one \(q_j\).  Grouping the terms
in \(\sum_i b_i\phi_i=0\) by \(j\), the only dependence among
\(q_1,q_2,q_3\) makes the three group coefficients equal.  They are
positive, so all three groups are nonempty.  There are exactly three
indices, hence every cap occurs once.  Relabeling gives (3).

The same argument fixes the scales inherited from (2).  Define
\[
\psi_{i,n}=\frac{f_{i,n}}{S_n}=b_{i,n}\phi_{i,n}.
\tag{24}
\]
For positive numbers \(\tau_i\),
\[
\psi_{i,n}\longrightarrow\tau_i\left(\frac13-\mu_i\right).
\tag{25}
\]
Since \(\sum_i\psi_{i,n}=-1/S_n\to0\), the unique dependence in (23)
gives
\[
\tau_1=\tau_2=\tau_3=:\tau>0.
\tag{26}
\]

The limiting cell areas are now exact.  For \(i\ne j\), the intersection of
caps \(i,j\) is the barycentric triangle
\[
\{\mu_i\geq1/3,\ \mu_j\geq1/3,\ \mu_i+\mu_j\leq1\},
\]
which has area \(|K|/9\).  Each cap has area \(4|K|/9\), so its singleton
part has area \(2|K|/9\).  The triple intersection is
\(\{\mu_1=\mu_2=\mu_3=1/3\}=\{g\}\).  Dominated convergence for the exact
cells gives
\[
\frac{r_n}{k_n}\longrightarrow0.
\tag{27}
\]
Together with \(k_n/p_n\to1\) from (9), this proves (4).

It remains to obtain the high-occupancy contradiction.  Set
\[
A_n=\max_{1\leq i\leq3}\ \max_{z\in K_n}\psi_{i,n}(z),
\qquad
a_n=S_nA_n.
\tag{28}
\]
Hausdorff convergence, (25)-(26), and \(\min_K\mu_i=0\) give
\[
A_n\longrightarrow\frac{\tau}{3}.
\tag{29}
\]
Since \(S_n\to\infty\), we have \(a_n\to\infty\).  By definition,
\[
K_n\subseteq T_n:=
\{f_{i,n}\leq a_n,\ i=1,2,3\}
=\{\psi_{i,n}\leq A_n,\ i=1,2,3\}.
\tag{30}
\]
The three limiting inequalities in (30) are
\[
\tau(1/3-\mu_i)\leq\tau/3,
\quad\text{equivalently}\quad
\mu_i\geq0.
\]
Their intersection is exactly \(K\).  The three limiting normals are
pairwise nonparallel and positively span the plane.  Hence, for all large
\(n\), the intersections \(T_n\) are bounded triangles and converge in
Hausdorff distance to \(K\).  Area continuity gives
\[
\frac{|K_n|}{|T_n|}\longrightarrow1.
\tag{31}
\]

The number \(a_n\) is unchanged when the affine normalization is undone,
because it is the maximum of the values of the original functions \(f_{i,n}\)
on the original middle body.  Undoing \(G_n\) also sends the containment in
(30) to
\[
\widehat K_n\subseteq
\{f_{i,n}\leq a_n,\ i=1,2,3\}
\]
for the original affine functions, which is the containment required in
accepted fact `043e84c0c8d6e05c`.  In the coordinates
\(\lambda_{i,n}=-f_{i,n}\), accepted fact `e1361027c1dda6fa` gives
\[
|T_n|=r_n(1+3a_n)^2
\tag{32}
\]
up to the common area multiplier.  Thus (31) is precisely (6).
Its limit is one, so its lower limit is larger than \(2/3\).  This is
forbidden for a genuine escape subsequence by accepted fact
`043e84c0c8d6e05c`.

We have excluded every genuine escape subsequence.  The diameter dichotomy in
that accepted fact now makes both gauged diameter sequences uniformly
bounded.  Its gauge also gives a fixed point in each body, so the diameter
bounds imply fixed compact containment.  This proves the lemma.

## External sources

S. Myroshnychenko, M. Stephen, and N. Zhang, "Grünbaum's inequality for
sections," Corollary 8, https://arxiv.org/pdf/1711.00998.
