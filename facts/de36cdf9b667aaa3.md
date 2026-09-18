---
fact_id: de36cdf9b667aaa3
kind: lemma
author: "r109_nine_cover_transverse"
assurance: LLM-verified
subgoal_id: nine-cover-transverse-quarter-ratio-test
depends_on: ["8f5f00ddd4f22d2f"]
source_packet_sha256: e75066db5a627fe612859b526818301e3ab29b3aecc7237b994902e0de1edf03
verifier_run: 5236ae6795974a42
target_match: null
---

## Statement

Write points of \(\mathbb R^3\) as \((r,x,y)\), with \(r\) the integer-height coordinate, and let
\[
A_0=\operatorname{conv}\{(0,0),(1/2,0),(0,1/2)\},
\]
\[
A_2=\operatorname{conv}\{(0,0),(1,0),(-1,1)\},
\]
\[
A_1=(A_0+A_2)/2
=\operatorname{conv}\{(-1/2,1/2),(0,0),(3/4,0),(1/2,1/4),(-1/2,3/4)\}.
\]
For a closed halfspace \(H\subseteq\mathbb R^3\), put
\[
\mu(H)=\sum_{i=0}^2
\left|\{(x,y)\in A_i:(i,x,y)\in H\}\right|.
\]
Then \((|A_0|,|A_1|,|A_2|)=(1/8,13/32,1/2)\), so \(T=33/32\) and \(2T/9=11/48\).  The following statements hold.

1.  The proper rational halfspace
\[
H_{00}=\{(r,x,y):r\le 1/2\}
\]
has \(\mu(H_{00})=1/8<11/48\), and its interior contains \(\{0\}\times A_0\).

2.  On the plane of \(A_2\), define the barycentric affine functions
\[
\lambda_0(x,y)=1-x-2y,\qquad
\lambda_1(x,y)=x+y,\qquad
\lambda_2(x,y)=y.
\]
The three proper rational halfspaces
\[
H_{2k}=\{(r,x,y):r+\lambda_k(x,y)\ge 93/40\},
\qquad k=0,1,2,
\]
all have
\[
\mu(H_{2k})=\frac{729}{3200}
=\frac{11}{48}-\frac{13}{9600}<\frac{11}{48},
\]
and their interiors cover \(\{2\}\times A_2\).

3.  For \(z=(0,1/4)\) and \(p=(1,z)\), every proper closed halfspace \(H\) containing \(p\) satisfies
\[
\mu(H)\ge\frac14.
\]
Equality is attained, so \(h_S(p)=1/4\).  Consequently no proper rational closed halfspace of mass below \(11/48\) contains \(p\), and no finite family, in particular no family of at most three, of such trace interiors covers \(\{1\}\times A_1\).

Thus all rational cap-combinatorial cells and all planar Farkas cover bases for the middle slice are ruled out by the same exact feasible witness \(z\).  In particular, the fixed triple does not satisfy the all-three-slices cover condition in accepted fact \(8f5f00ddd4f22d2f\).

## Proof

Direct Minkowski edge merging gives
\[
A_0+A_2
=\operatorname{conv}\{(-1,1),(0,0),(3/2,0),(1,1/2),(-1,3/2)\},
\]
which verifies the displayed formula for \(A_1\).  The shoelace formula gives
\[
|A_0|=\frac18,\qquad |A_1|=\frac{13}{32},\qquad |A_2|=\frac12.
\]
Moreover
\[
C=\operatorname{conv}\bigl((\{0\}\times A_0)\cup(\{2\}\times A_2)\bigr)
\]
is a compact polytope whose height-\(r\) section, for \(0\le r\le2\), is
\[
\left(1-\frac r2\right)A_0+\frac r2 A_2.
\]
Its only integer-height sections are therefore \(A_0,A_1,A_2\), establishing exact compatibility and compact-polytope reconstruction.

For \(H_{00}\), the height-zero trace is the whole plane and lies in the interior because \(0<1/2\); the height-one and height-two traces are empty.  Thus
\[
\mu(H_{00})=|A_0|=\frac18,
\qquad
\frac{11}{48}-\mu(H_{00})=\frac5{48}.
\]
The closed trace-complement system on height zero is already infeasible by the scalar contradiction \(0\ge1/2\).

For the height-two cover, the functions \(\lambda_0,\lambda_1,\lambda_2\) are the barycentric coordinates of \(A_2\), so they are nonnegative on \(A_2\) and sum to one.  On \(A_0\), their respective maxima are \(1,1/2,1/2\); on \(A_1\), their respective maxima are \(1,3/4,3/4\).  Hence the height-zero trace condition for \(H_{2k}\), namely \(\lambda_k\ge93/40\), and the height-one trace condition, namely \(\lambda_k\ge53/40\), are both infeasible.  At height two the trace is
\[
\{(x,y)\in A_2:\lambda_k(x,y)\ge13/40\}.
\]
This is a triangle similar to \(A_2\) with linear ratio \(1-13/40=27/40\).  Its exact area is therefore
\[
\frac12\left(\frac{27}{40}\right)^2=\frac{729}{3200}.
\]
Thus all three clipping masses and their strict margins are exactly as stated.  If a point of \(A_2\) lay in none of the three trace interiors, it would satisfy
\[
\lambda_0\le\frac{13}{40},\qquad
\lambda_1\le\frac{13}{40},\qquad
\lambda_2\le\frac{13}{40}.
\]
Adding these inequalities to \(\lambda_0+\lambda_1+\lambda_2=1\) gives the exact Farkas contradiction
\[
1\le\frac{39}{40}.
\]
This proves the height-two interior cover and supplies its closed-complement infeasibility certificate.

It remains to prove the exhaustive middle-slice obstruction.  Let
\[
z=(0,1/4),\qquad R(w)=2z-w=(0,1/2)-w.
\]
Reflection sends \(A_0\) to
\[
R(A_0)=\operatorname{conv}\{(0,1/2),(-1/2,1/2),(0,0)\}\subseteq A_2.
\]
The inclusion follows directly from
\[
A_2=\{(x,y):y\ge0,\ x+y\ge0,\ x+2y\le1\},
\]
whose three inequalities hold at all three displayed vertices of \(R(A_0)\).

Also set
\[
Q=\operatorname{conv}\{(-1/2,1/2),(0,1/2),(1/2,0),(0,0)\}.
\]
The points \((0,1/2)\) and \((1/2,0)\) lie respectively on the edges
\[
[(1/2,1/4),(-1/2,3/4)]
\quad\hbox{and}\quad
[(0,0),(3/4,0)]
\]
of \(A_1\), while the other two vertices of \(Q\) are vertices of \(A_1\).  Hence \(Q\subseteq A_1\).  It is a parallelogram centered at \(z\), and the shoelace formula gives \(|Q|=1/4\).  Every line through \(z\) bisects \(Q\) in area, so every proper planar closed halfspace whose boundary passes through \(z\) captures at least
\[
\frac{|Q|}{2}=\frac18
\]
of \(A_1\).

Now let
\[
H=\{(r,w):a r+u\mathbin{\cdot}w\le b\}
\]
be any proper closed halfspace containing \(p=(1,z)\), where \((a,u)\ne0\).  Since \(b\ge a+u\mathbin{\cdot}z\), the boundary-through-\(p\) halfspace
\[
H'=\{(r,w):a r+u\mathbin{\cdot}w\le a+u\mathbin{\cdot}z\}
\]
satisfies \(H'\subseteq H\), hence \(\mu(H)\ge\mu(H')\).

If \(u=0\), the height-one trace of \(H'\) is the whole of \(A_1\), so
\[
\mu(H')\ge |A_1|=\frac{13}{32}>\frac14.
\]
Assume \(u\ne0\).  The middle trace of \(H'\) is
\[
B_1=A_1\cap\{w:u\mathbin{\cdot}w\le u\mathbin{\cdot}z\}.
\]
Its boundary passes through the center of \(Q\), so the preceding bisection argument gives \(|B_1|\ge1/8\).

The endpoint traces are
\[
B_0=A_0\cap\{w:u\mathbin{\cdot}w\le u\mathbin{\cdot}z+a\},
\]
\[
B_2=A_2\cap\{w:u\mathbin{\cdot}w\le u\mathbin{\cdot}z-a\}.
\]
For every \(w\in A_0\setminus B_0\),
\[
u\mathbin{\cdot}R(w)
=2u\mathbin{\cdot}z-u\mathbin{\cdot}w
<u\mathbin{\cdot}z-a.
\]
Because \(R(A_0)\subseteq A_2\), this implies \(R(w)\in B_2\).  Reflection preserves area, and therefore
\[
|B_0|+|B_2|
\ge |B_0|+|R(A_0\setminus B_0)|
=|A_0|=\frac18.
\]
Consequently
\[
\mu(H)\ge\mu(H')=|B_0|+|B_1|+|B_2|
\ge\frac18+\frac18=\frac14.
\]

The lower bound is sharp.  The rational halfspace
\[
G=\{(r,x,y):r/2+x+2y\le1\}
\]
contains \(p\) on its boundary.  Its height-zero trace contains all of \(A_0\), its height-one clipping polygon is
\[
\operatorname{conv}\{(-1/2,1/2),(0,0),(1/2,0)\}
\]
of area \(1/8\), and its height-two trace has area zero.  Hence
\[
\mu(G)=\frac18+\frac18=\frac14,
\]
proving \(h_S(p)=1/4\).  Its exact excess above the target is
\[
\frac14-\frac{11}{48}=\frac1{48}.
\]

The preceding split \(u=0\) or \(u\ne0\) exhausts every proper three-dimensional halfspace, including every rational direction, every clipping combinatorial cell, every vertex-order boundary, and every degenerate trace.  It uses no open-cell or generic-position assumption.  For any halfspace of mass below \(11/48\), the point \(p\) is not even in the closed halfspace.  Thus \(z\) belongs to every closed height-one trace complement in any proposed family.  Their intersection is feasible at \(z\), so every possible one-, two-, or three-complement planar Farkas basis is feasible and cannot certify a cover.  This exactly rules out the middle-slice cover required by accepted fact \(8f5f00ddd4f22d2f\).

## External sources

none
