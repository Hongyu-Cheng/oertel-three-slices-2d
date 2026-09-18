---
fact_id: dcf65c9de5a176bb
kind: theorem
author: "mp_r410_affine_selector_audit"
assurance: LLM-verified
subgoal_id: multislice-affine-selector-transfer
depends_on: ["446ebd1e738cf6dd","4dfa9b673b27fea1","9fa81a67fd2eaafc"]
source_packet_sha256: 5ff154bc34197f4fdde79903fcaea42aca754ea680ebb2974a30a368b9617495
verifier_run: b874bbffbbf04840
target_match: null
---

## Statement

Let \(C\subset\mathbb R\times\mathbb R^2\) be a compact convex polytope,
write \(C_z=\{w:(z,w)\in C\}\), and let
\[
I=\{z\in\mathbb Z:C_z\ne\varnothing\}
\]
be its nonempty finite integer slice set, and write \(A_z=C_z\) and
\[
S=C\cap(\mathbb Z\times\mathbb R^2)
 =\bigcup_{z\in I}(\{z\}\times A_z).
\]
For \(y\in S\), set
\[
h_S(y)=
\inf\{\mathcal H_2(S\cap H):
H\subset\mathbb R^3\text{ is a closed halfspace containing }y\}.
\]
Suppose
\[
q(z)=az+b\in A_z
\qquad(z\in I)
\]
for fixed \(a,b\in\mathbb R^2\).  Define
\[
\delta_z=
\inf\{|A_z\cap K|:
K\subset\mathbb R^2\text{ is a closed halfplane containing }q(z)\},
\qquad
D=\sum_{z\in I}\delta_z.
\]
For every \(r\in I\),
\[
h_S((r,q(r)))
\ge
\min\left\{
\sum_{\substack{z\in I\\z\le r}}\delta_z,
\sum_{\substack{z\in I\\z\ge r}}\delta_z
\right\}.
\]
Then
\[
\max_{z\in I}h_S((z,q(z)))\ge\frac D2.
\tag{1}
\]
More precisely, there is \(z^\star\in I\) such that
\[
\sum_{\substack{z\in I\\z\le z^\star}}\delta_z\ge\frac D2,
\qquad
\sum_{\substack{z\in I\\z\ge z^\star}}\delta_z\ge\frac D2,
\tag{2}
\]
and
\[
h_S((z^\star,q(z^\star)))
\ge
\min\left\{
\sum_{\substack{z\in I\\z\le z^\star}}\delta_z,
\sum_{\substack{z\in I\\z\ge z^\star}}\delta_z
\right\}.
\tag{3}
\]
Consequently, with \(T=\sum_{z\in I}|A_z|\), bound (1) proves
\[
\max_{z\in I}h_S((z,q(z)))\ge\frac{2T}{9}
\]
if and only if
\[
\sum_{z\in I}\delta_z\ge\frac{4T}{9}.
\tag{4}
\]
The sharper per-slice certificate reaches \(2T/9\) exactly when some
\(r\in I\) has both displayed one-sided sums at least \(2T/9\).  Condition
(4) is exactly when the advertised coarser numerical bound \(D/2\) reaches
\(2T/9\).  Neither equivalence asserts failure of the actual depth when
the corresponding sufficient condition fails.

The factor \(1/2\) is sharp for the weighted-median input: for the two
unit weights on \(\{0,1\}\), every support point lies in a closed base
halfline of weight exactly \(1=D/2\).

There is a compatible three-slice family satisfying (4) that is not
certified by the three accepted facts named above.  Let
\[
D_0=
\operatorname{conv}\left\{
\left(\frac{25}{24},0\right),
\left(-\frac{25}{24},0\right),
\left(0,\frac{12}{25}\right),
\left(0,-\frac{12}{25}\right)
\right\},
\tag{5}
\]
\[
A_0=4D_0,\qquad A_2=D_0,
\tag{6}
\]
and
\[
A_1=
\operatorname{conv}\left\{
\left(-4,-\frac65\right),
\left(4,-\frac65\right),
\left(0,\frac{14}{5}\right)
\right\}.
\tag{7}
\]
Put
\[
C=\operatorname{conv}\left(
(\{0\}\times A_0)\cup(\{1\}\times A_1)
\cup(\{2\}\times A_2)
\right).
\tag{8}
\]
Then the three integer slices of \(C\) are exactly the sets in
(6)-(7).  For the constant affine selector
\[
q(0)=q(1)=q(2)=(0,0),
\tag{9}
\]
the exact planar depths are
\[
\delta_0=8,\qquad
\delta_1=\frac{168}{25},\qquad
\delta_2=\frac12.
\tag{10}
\]
Hence
\[
T=33,\qquad
D=\frac{761}{50}
=\frac{4T}{9}+\frac{83}{150}.
\tag{11}
\]
Bound (1) gives
\[
\max_{z\in\{0,1,2\}}h_S((z,0))
\ge\frac{761}{100}
=\frac{2T}{9}+\frac{83}{300}.
\tag{12}
\]
The weighted median can in fact be chosen as the endpoint \(z^\star=0\),
and the sharper bound (3) gives
\[
h_S((0,0))\ge8>\frac{22}{3}=\frac{2T}{9}.
\tag{13}
\]

## Proof

If \(D=0\), any \(z^\star\in I\) satisfies (2), and all asserted lower
bounds are zero.  Assume \(D>0\), order \(I\), and choose the smallest
\(z^\star\in I\) such that
\[
\sum_{\substack{z\in I\\z\le z^\star}}\delta_z\ge\frac D2.
\]
The first inequality in (2) holds by construction.  Minimality gives
\[
\sum_{\substack{z\in I\\z<z^\star}}\delta_z<\frac D2,
\]
so
\[
\sum_{\substack{z\in I\\z\ge z^\star}}\delta_z
=D-\sum_{\substack{z\in I\\z<z^\star}}\delta_z
>\frac D2.
\]
This also covers the case in which \(z^\star\) is an endpoint of \(I\).
Zero weights do not affect either inequality.

Let \(H\) be an arbitrary proper closed ambient halfspace containing
\((z^\star,q(z^\star))\).  Write
\[
H=\{(x,w):
\alpha x+\langle u,w\rangle\le\beta\},
\qquad
(\alpha,u)\ne(0,0).
\tag{14}
\]
Its restriction to the affine graph of \(q\) is
\[
J_H
=
\left\{
z\in I:
\bigl(\alpha+\langle u,a\rangle\bigr)z+\langle u,b\rangle
\le\beta
\right\}.
\tag{15}
\]
This is the intersection of \(I\) with a closed halfline, or it is all of
\(I\).  It contains \(z^\star\).  If the coefficient of \(z\) in (15) is
positive, \(J_H\) contains every \(z\in I\) with \(z\le z^\star\).  If it
is negative, \(J_H\) contains every \(z\in I\) with \(z\ge z^\star\).  If
it is zero, containment of \(z^\star\) forces (15) to hold for every
\(z\in I\).  Because (15) uses a closed inequality, a graph point tied on
the boundary is included with its full weight.  Therefore
\[
\sum_{z\in J_H}\delta_z
\ge
\min\left\{
\sum_{\substack{z\in I\\z\le z^\star}}\delta_z,
\sum_{\substack{z\in I\\z\ge z^\star}}\delta_z
\right\}.
\tag{16}
\]

For \(z\in J_H\), the section of \(H\) on the \(z\)-fiber is
\[
H_z=\{w\in\mathbb R^2:
\alpha z+\langle u,w\rangle\le\beta\}.
\tag{17}
\]
If \(u\ne0\), this is a closed planar halfspace containing \(q(z)\), so
\[
|A_z\cap H_z|\ge\delta_z.
\tag{18}
\]
If \(u=0\), then (17) is all of \(\mathbb R^2\) for every \(z\in J_H\),
and
\[
|A_z\cap H_z|=|A_z|\ge\delta_z.
\tag{19}
\]
Thus (19) handles every horizontal ambient halfspace, including one whose
boundary contains an entire positive-area fiber.  Using (18)-(19) on the
fibers in \(J_H\), then applying (16), gives
\[
\mathcal H_2(S\cap H)
=\sum_{z\in I}|A_z\cap H_z|
\ge\sum_{z\in J_H}\delta_z
\ge
\min\left\{
\sum_{z\le z^\star}\delta_z,
\sum_{z\ge z^\star}\delta_z
\right\}.
\]
The same conclusion is immediate if the whole space is admitted as a
degenerate halfspace.  Taking the infimum over \(H\) proves (3), and (2)
then proves (1).  Nothing in the halfspace argument used (2), so replacing
\(z^\star\) by an arbitrary \(r\in I\) proves the stated per-slice bound.
Its exact threshold condition follows by taking the minimum of its two
one-sided sums.  The equivalence (4) is the arithmetic equivalence
\[
\frac D2\ge\frac{2T}{9}
\quad\Longleftrightarrow\quad
D\ge\frac{4T}{9}.
\]

It remains to verify the exact three-slice example and its
nonredundancy.  The diamond \(D_0\) has perpendicular diagonal lengths
\(25/12\) and \(24/25\), so
\[
|D_0|=\frac12\frac{25}{12}\frac{24}{25}=1.
\tag{20}
\]
Thus
\[
|A_0|=16,\qquad |A_2|=1.
\tag{21}
\]
The triangle \(A_1\) has base \(8\) and height \(4\), so
\[
|A_1|=16.
\tag{22}
\]

Because \(A_0=4D_0\) and \(A_2=D_0\),
\[
\frac{A_0+A_2}{2}=\frac52D_0.
\tag{23}
\]
The four vertices of the diamond on the right side of (23) are
\[
\left(\frac{125}{48},0\right),\quad
\left(-\frac{125}{48},0\right),\quad
\left(0,\frac65\right),\quad
\left(0,-\frac65\right).
\tag{24}
\]
The triangle in (7) is exactly
\[
A_1=
\left\{(x,y):
y\ge-\frac65,\quad
x+y\le\frac{14}{5},\quad
-x+y\le\frac{14}{5}
\right\}.
\tag{25}
\]
Every point in (24) satisfies (25); for the two horizontal vertices the
only nontrivial comparison is
\[
\frac{125}{48}<\frac{14}{5}.
\]
Consequently,
\[
\frac{A_0+A_2}{2}\subseteq A_1.
\tag{26}
\]

The first-coordinate projection of \(C\) is \([0,2]\), and its endpoint
sections are \(A_0,A_2\).  In a convex combination of the three generating
slices that has first coordinate \(1\), the coefficients of the height
\(0\) and height \(2\) terms are equal.  Its planar coordinate is therefore
a convex combination of a point in \((A_0+A_2)/2\) and a point in \(A_1\).
By (26) it lies in \(A_1\), while \(\{1\}\times A_1\subset C\).  Thus the
integer slices of \(C\) are exactly (6)-(7), and the example is compatible
with the locked problem.

The two outer diamonds are centrally symmetric about the selector point.
Every line through that point bisects their areas, and translating the
boundary of any halfplane containing the point toward it can only decrease
the cap.  Equations (20)-(21) therefore give
\[
\delta_0=8,\qquad \delta_2=\frac12.
\tag{27}
\]

The barycentric coordinates of \((0,0)\) in the triangle \(A_1\), in the
vertex order displayed in (7), are
\[
\left(\frac7{20},\frac7{20},\frac3{10}\right).
\tag{28}
\]
We compute its planar halfspace depth exactly.  It suffices to consider a
line through the point, because parallel translation to the point only
shrinks a halfplane containing it.  Such a line meets two edges of the
triangle and cuts off a corner triangle at their common vertex.

Fix that vertex and denote the other two barycentric coordinates of the
point by \(u,v\).  If the chord endpoints lie fractions \(r,s\in(0,1]\)
along the two incident edges, then
\[
\frac ur+\frac vs=1.
\tag{29}
\]
Putting \(x=u/r\) gives
\[
u\le x\le1-v,\qquad
\frac{\text{corner-cap area}}{|A_1|}
=rs=\frac{uv}{x(1-x)}.
\tag{30}
\]
For either of the first two vertices, \(\{u,v\}=\{7/20,3/10\}\).
The interval in (30) contains \(1/2\), and direct evaluation at its
endpoints and at \(1/2\) gives
\[
\frac{21}{50}
\le\frac{uv}{x(1-x)}
\le\frac12.
\tag{31}
\]
For the third vertex, \(u=v=7/20\), and similarly
\[
\frac{49}{100}
\le\frac{uv}{x(1-x)}
\le\frac7{13}.
\tag{32}
\]
The complementary cap in (31) has area fraction at least \(1/2\), and the
complementary cap in (32) has area fraction at least
\[
1-\frac7{13}=\frac6{13}>\frac{21}{50}.
\]
Thus every closed halfplane through the selector has area at least
\((21/50)|A_1|\).  Equality in (31) occurs at \(x=1/2\), with valid
intercepts \(r=7/10\) and \(s=3/5\).  Hence
\[
\delta_1=\frac{21}{50}|A_1|=\frac{168}{25}.
\tag{33}
\]
Equations (27) and (33) prove (10), and (21)-(22) prove (11).  Since
\(\delta_0=8>D/2\), the smallest weighted median is \(z^\star=0\);
(3) gives (13).

We finally compare the example to the three nearby accepted facts.  Its
slice centroids are
\[
c_0=c_2=(0,0),\qquad c_1=\left(0,\frac2{15}\right).
\tag{34}
\]
Also,
\[
\max_i|A_i|=16<\frac{33}{2}=\frac T2.
\tag{35}
\]
Thus neither hypothesis of accepted fact `4dfa9b673b27fea1` holds.
The scalar left side in the criterion of accepted fact
`9fa81a67fd2eaafc` is
\[
(\sqrt{16}+\sqrt1)^2+4\min\{16,1\}=29<66=2T,
\tag{36}
\]
so that fact does not certify the family.

For completeness, we bound the criterion of accepted fact
`446ebd1e738cf6dd` at every \(c\in A_1\), not only at the selector.
For any triangle \(K\) and any \(c\in K\),
\[
|K\cap(2c-K)|\le\frac23|K|.
\tag{37}
\]
Indeed, let \((\lambda_1,\lambda_2,\lambda_3)\) be the barycentric
coordinates of \(c\).  In barycentric coordinates,
\[
K\cap(2c-K)
=
\{r_1+r_2+r_3=1:0\le r_i\le2\lambda_i\}.
\]
Inclusion-exclusion in the standard triangle gives its area fraction
\[
F(\lambda)
=1-\sum_i(1-2\lambda_i)_+^2
+\sum_i(2\lambda_i-1)_+^2.
\tag{38}
\]
If every \(\lambda_i\le1/2\), then
\[
F(\lambda)=2-4\sum_i\lambda_i^2\le\frac23.
\]
If, say, \(\lambda_1>1/2\), then (38) simplifies to
\[
F(\lambda)=8\lambda_2\lambda_3<\frac12.
\]
This proves (37), including boundary cases by continuity.  Therefore the
quantity \(\Phi(c)\) in `446ebd1e738cf6dd` satisfies, for every \(c\in A_1\),
\[
\begin{aligned}
\Phi(c)
&=|A_1\cap(2c-A_1)|
  +2|A_2\cap(2c-A_0)|\\
&\le\frac23|A_1|+2|A_2|
=\frac{38}{3}
<\frac{44}{3}=\frac{4T}{9}.
\end{aligned}
\tag{39}
\]
Hence that accepted symmetric-overlap certificate does not cover this
family.  Equations (34)-(39) complete the exact nonredundancy check.

## External sources

none
