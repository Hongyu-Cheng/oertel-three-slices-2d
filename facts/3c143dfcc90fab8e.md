---
fact_id: 3c143dfcc90fab8e
kind: lemma
author: "r096_nine_cell_endpoints"
assurance: LLM-verified
subgoal_id: nine-cover-transverse-quarter-ratio-test
depends_on: []
source_packet_sha256: 5df3e88c7333e9651edefb7e1bd7cebb84c088fe7a91db858bea2d77e6426d62
verifier_run: 926b1d670e114c00
target_match: null
---

## Statement

Let
\[
\begin{aligned}
A_0&=\operatorname{conv}\{(0,0),(1/2,0),(0,1/2)\},\\
A_1&=\operatorname{conv}\{(-1/2,1/2),(0,0),(3/4,0),
                         (1/2,1/4),(-1/2,3/4)\},\\
A_2&=\operatorname{conv}\{(0,0),(1,0),(-1,1)\}.
\end{aligned}
\]
Their areas are \(1/8,13/32,1/2\), respectively, and the strict target is
\(11/48\).  For
\[
u_1=(1,2),\qquad u_2=(-1,0),\qquad u_3=(0,-1),
\]
define
\[
M_r(c)=\inf_{k\in\mathbb R}\sum_{i=0}^2
\left|A_i\cap\{w:u_r\cdot w\le c+k(i-1)\}\right|
\]
and
\[
R_r=\sup\{c\in\mathbb R:M_r(c)<11/48\}.
\]
Then
\[
R_1=\frac23-\frac{\sqrt6}{12},\qquad
R_2=-1+\frac{\sqrt{78}}{12},\qquad
R_3=-\frac56+\frac{\sqrt{26}}{12}.
\]
In particular,
\[
R_1+R_2+2R_3
=-2+\frac{\sqrt{78}+2\sqrt{26}-\sqrt6}{12}
<-\frac14<0.
\]
Consequently, there do not exist real \(c_r,k_r\), \(r=1,2,3\), such that
all three halfspaces
\[
H_r=\{(h,w):u_r\cdot w\le c_r+k_r(h-1)\}
\]
have total three-slice mass strictly below \(11/48\) and their height-\(1\)
trace interiors cover all of \(\mathbb R^2\).

## Proof

For \(r=1,2,3\), \(i=0,1,2\), put
\[
F_{ri}(t)=|A_i\cap\{w:u_r\cdot w\le t\}|.
\]
The following is a complete exact clipping enumeration.  If
\(B=(b_1,\ldots,b_m)\) is an increasing breakpoint list, its associated
intervals are
\[
I_0=(-\infty,b_1),\quad I_j=(b_j,b_{j+1})\ (1\le j<m),
\quad I_m=(b_m,\infty).
\]
In the table, the displayed polynomials are the values of \(F_{ri}\) on
\(I_0,\ldots,I_m\), in that order:
\[
\begin{array}{c|c|c|l}
r&i&B_{ri}&(F_{ri}|_{I_0},\ldots,F_{ri}|_{I_m})\\ \hline
1&0&(0,\frac12,1)&
\left(0,\frac{t^2}{4},\frac{-2t^2+4t-1}{8},\frac18\right)\\
1&1&(0,\frac12,\frac34,1)&
\left(0,\frac{t^2}{2},\frac{4t^2+4t-1}{16},
\frac{-8t^2+32t-11}{32},\frac{13}{32}\right)\\
1&2&(0,1)&
\left(0,\frac{t^2}{2},\frac12\right)\\[2pt] \hline
2&0&(-\frac12,0)&
\left(0,\frac{(2t+1)^2}{8},\frac18\right)\\
2&1&(-\frac34,-\frac12,0,\frac12)&
\left(0,\frac{(4t+3)^2}{32},\frac{8t^2+16t+7}{32},
\frac{-8t^2+16t+7}{32},\frac{13}{32}\right)\\
2&2&(-1,0,1)&
\left(0,\frac{(t+1)^2}{4},\frac{-t^2+2t+1}{4},\frac12\right)\\[2pt] \hline
3&0&(-\frac12,0)&
\left(0,\frac{(2t+1)^2}{8},\frac18\right)\\
3&1&(-\frac34,-\frac12,-\frac14,0)&
\left(0,\frac{(4t+3)^2}{16},\frac{8t^2+16t+7}{16},
\frac{24t+13}{32},\frac{13}{32}\right)\\
3&2&(-1,0)&
\left(0,\frac{(t+1)^2}{2},\frac12\right).
\end{array}
\tag{1}
\]
For completeness, these entries follow directly from exact polygon clipping.
If an edge \([p,q]\) crosses \(u_r\cdot w=t\), its new vertex is
\[
p+\frac{t-u_r\cdot p}{u_r\cdot(q-p)}(q-p).
\]
Thus every clipped vertex is rational-affine in \(t\) on each interval in
(1).  Substitution in the shoelace formula gives the displayed quadratic or
linear polynomial.  Adjacent entries agree at every breakpoint, including the
constant values \(0,1/8,13/32,1/2\) at the two unbounded ends, so (1) also
gives every boundary value.

Here is an explicit enumeration of every nonempty open clipping cell in the
\((c,k)\)-plane.  For fixed \(r\), let \(I_{ri,j}\) be the intervals determined
by \(B_{ri}\) in (1), and set
\[
\mathcal C^{(r)}_{abd}
=\{(c,k):c-k\in I_{r0,a},\ c\in I_{r1,b},\
                 c+k\in I_{r2,d}\}.
\tag{2}
\]
For each middle-interval index \(b\), the nonempty cells are exactly the
following pairs \((a,d)\):
\[
\begin{array}{c|c|l}
r&b&\{(a,d):\mathcal C^{(r)}_{abd}\ne\varnothing\}\\ \hline
1&0&\{(0,0),(0,1),(0,2),(1,0),(2,0),(3,0)\}\\
1&1&\{(0,1),(0,2),(1,0),(1,1),(2,0),(2,1),(3,0)\}\\
1&2&\{(0,2),(1,1),(1,2),(2,1),(3,0),(3,1)\}\\
1&3&\{(0,2),(1,2),(2,1),(2,2),(3,0),(3,1)\}\\
1&4&\{(0,2),(1,2),(2,2),(3,0),(3,1),(3,2)\}\\[2pt] \hline
2&0&\{(0,0),(0,1),(0,2),(0,3),(1,0),(2,0)\}\\
2&1&\{(0,1),(0,2),(0,3),(1,0),(1,1),(2,0)\}\\
2&2&\{(0,1),(0,2),(0,3),(1,1),(1,2),(2,0),(2,1)\}\\
2&3&\{(0,2),(0,3),(1,2),(1,3),(2,0),(2,1),(2,2)\}\\
2&4&\{(0,3),(1,3),(2,0),(2,1),(2,2),(2,3)\}\\[2pt] \hline
3&0&\{(0,0),(0,1),(0,2),(1,0),(2,0)\}\\
3&1&\{(0,1),(0,2),(1,0),(1,1),(2,0)\}\\
3&2&\{(0,1),(0,2),(1,1),(2,0),(2,1)\}\\
3&3&\{(0,2),(1,1),(1,2),(2,0),(2,1)\}\\
3&4&\{(0,2),(1,2),(2,0),(2,1),(2,2)\}.
\end{array}
\tag{3}
\]
Indeed, the affine change of variables
\[
a=c-k,\qquad d'=c+k,\qquad
c=\frac{a+d'}2,\qquad k=\frac{d'-a}2
\tag{4}
\]
is bijective.  Hence \(\mathcal C^{(r)}_{abd}\) is nonempty exactly when
\[
(I_{r0,a}+I_{r2,d})\cap 2I_{r1,b}\ne\varnothing.
\]
Interval addition gives precisely (3), so no open clipping cell is omitted.
Every lower-dimensional cell is obtained by replacing one or more interval
conditions in (2) by equality to a listed breakpoint.  The adjacent
polynomials in (1) agree there, so these faces require no additional mass
formula.

It remains to minimize the exact polynomial on these cells.  With
\[
a=c-k,\qquad b=c+k=2c-a,
\]
write
\[
G_r(c)=\inf_{a\in\mathbb R}
\bigl(F_{r0}(a)+F_{r2}(2c-a)\bigr).
\tag{5}
\]
Then
\[
M_r(c)=F_{r1}(c)+G_r(c).
\tag{6}
\]
The endpoint values fall in the rational intervals
\[
\begin{aligned}
\frac38&<\frac23-\frac{\sqrt6}{12}<\frac12,\\
-\frac3{10}&<-1+\frac{\sqrt{78}}{12}<-\frac14,\\
-\frac5{12}&<-\frac56+\frac{\sqrt{26}}{12}<-\frac25.
\end{aligned}
\tag{7}
\]
These inequalities follow, respectively, from
\[
2<\sqrt6<\frac72,\qquad
\frac{42}{5}<\sqrt{78}<9,\qquad
5<\sqrt{26}<\frac{26}{5},
\]
after squaring positive quantities.

We now calculate \(G_r\) on the three intervals in (7), checking all cells
from (3).

For \(r=1\), take \(3/8<c<1/2\) and put \(s=2c\).  The breakpoints for the
one-variable expression in (5), in increasing order, are
\[
s-1,\quad 0,\quad \frac12,\quad s,\quad 1.
\]
On the six resulting intervals its expressions are
\[
\begin{array}{c|c}
\text{interval for }a&
F_{10}(a)+F_{12}(s-a)\\ \hline
(-\infty,s-1)&\frac12\\
(s-1,0)&\frac{(s-a)^2}{2}\\
(0,\frac12)&\frac{a^2}{4}+\frac{(s-a)^2}{2}\\
(\frac12,s)&\frac{-2a^2+4a-1}{8}+\frac{(s-a)^2}{2}\\
(s,1)&\frac{-2a^2+4a-1}{8}\\
(1,\infty)&\frac18.
\end{array}
\tag{8}
\]
The second and third entries decrease up to their right endpoints, and the
fifth increases from its left endpoint.  The fourth is strictly convex and
has its unique minimum at
\[
a=2s-1=4c-1,\qquad s-a=1-2c.
\]
It is no larger than the adjacent boundary values.  Its value is
\[
-\frac{(4c-3)(4c-1)}8
=\frac18-2\left(c-\frac12\right)^2<\frac18,
\]
so it is also smaller than the last entry and hence than every entry in (8).
Therefore
\[
G_1(c)=-\frac{(4c-3)(4c-1)}8
\qquad(3/8<c<1/2).
\tag{9}
\]

For \(r=2\), take \(-3/10<c<-1/4\), so
\(-3/5<s=2c<-1/2\).  The breakpoints are
\[
s-1,\quad s,\quad-\frac12,\quad0,\quad s+1.
\]
The only possible interior minimum below the boundary values occurs on
\(-1/2<a<0\), where
\[
F_{20}(a)+F_{22}(s-a)
=\frac{(2a+1)^2}{8}+\frac{(s-a+1)^2}{4}.
\]
This strictly convex quadratic has its minimum at \(a=s/3\), with value
\[
\frac{(2s+3)^2}{24}=\frac{(4c+3)^2}{24}.
\tag{10}
\]
The intervals to its left decrease toward its left boundary.  On
\(0<a<s+1\), the value decreases to \(1/8\), and it is identically \(1/8\)
for \(a>s+1\).  Thus the complete cell comparison gives
\[
G_2(c)=\min\left\{\frac{(4c+3)^2}{24},\frac18\right\}.
\]
Here \(4c+3>9/5\), so the first entry is larger than
\[
\frac{(9/5)^2}{24}=\frac{27}{200}>\frac18.
\]
Consequently,
\[
G_2(c)=\frac18
\qquad(-3/10<c<-1/4).
\tag{11}
\]
For example, the value \(1/8\) is attained by
\[
a=2c+1,\qquad s-a=-1.
\]

For \(r=3\), take \(-5/12<c<-2/5\), so
\(-5/6<s=2c<-4/5\).  The breakpoints are
\[
s,\quad-\frac12,\quad0,\quad s+1.
\]
The only possible interior minimum below the boundary values occurs on
\(-1/2<a<0\), where
\[
F_{30}(a)+F_{32}(s-a)
=\frac{(2a+1)^2}{8}+\frac{(s-a+1)^2}{2}.
\]
It is strictly convex and has its minimum at
\[
a=\frac{s}{2}+\frac14=c+\frac14,\qquad
s-a=c-\frac14,
\]
with value
\[
\frac{(4c+3)^2}{16}.
\tag{12}
\]
The intervals to its left decrease toward it.  The intervals to its right
either increase away from its right boundary or decrease to the constant
competitor \(1/8\).  Hence the complete comparison is
\[
G_3(c)=\min\left\{\frac{(4c+3)^2}{16},\frac18\right\}.
\]
On the present interval, \(4c+3<7/5\), and therefore
\[
\frac{(4c+3)^2}{16}<\frac{(7/5)^2}{16}
=\frac{49}{400}<\frac18.
\]
It follows that
\[
G_3(c)=\frac{(4c+3)^2}{16}
\qquad(-5/12<c<-2/5).
\tag{13}
\]

Combining (1), (6), (9), (11), and (13) gives
\[
\begin{array}{c|c|c}
r&\text{interval}&M_r(c)\\ \hline
1&(3/8,1/2)&
\displaystyle\frac{-12c^2+16c-3}{8}\\[3pt]
2&(-3/10,-1/4)&
\displaystyle\frac{8c^2+16c+11}{32}\\[3pt]
3&(-5/12,-2/5)&
\displaystyle\frac{(c+1)(3c+2)}{2}.
\end{array}
\tag{14}
\]
Each displayed function is strictly increasing on its listed interval.  Its
equation \(M_r(c)=11/48\), after clearing positive denominators, is,
respectively,
\[
72c^2-96c+29=0,\qquad
24c^2+48c+11=0,\qquad
72c^2+120c+37=0.
\tag{15}
\]
The unique roots of (15) in the intervals in (14) are
\[
\frac23-\frac{\sqrt6}{12},\qquad
-1+\frac{\sqrt{78}}{12},\qquad
-\frac56+\frac{\sqrt{26}}{12}.
\tag{16}
\]

For every fixed \(k\), the mass in the definition of \(M_r(c)\) is
nondecreasing in \(c\).  Taking the infimum over \(k\) shows that each
\(M_r\) is nondecreasing.  The strict increase in (14) shows that immediately
to the left of the corresponding value in (16), \(M_r(c)<11/48\), while at
that value equality holds.  Monotonicity then gives \(M_r(c)<11/48\) for
every smaller \(c\) and \(M_r(c)\ge11/48\) for every larger \(c\).
Thus (16) are exactly \(R_1,R_2,R_3\).

Their Farkas-weighted sum is
\[
R_1+R_2+2R_3
=-2+\frac{\sqrt{78}+2\sqrt{26}-\sqrt6}{12}.
\]
Since \(\sqrt{78}<9\), \(\sqrt{26}<6\), and \(-\sqrt6<0\),
\[
R_1+R_2+2R_3
<-2+\frac{9+12}{12}=-\frac14.
\tag{17}
\]

Finally, suppose three halfspaces in the statement all have mass below
\(11/48\).  Since \(M_r(c_r)\) is the infimum over their slopes,
\[
M_r(c_r)<\frac{11}{48},
\]
and hence \(c_r<R_r\).  Therefore (17) gives
\[
c_1+c_2+2c_3<R_1+R_2+2R_3<0.
\tag{18}
\]
The closed complements of the height-\(1\) trace interiors have the system
\[
x+2y\ge c_1,\qquad x\le -c_2,\qquad y\le -c_3.
\tag{19}
\]
This system is feasible exactly when
\[
c_1+c_2+2c_3\le0:
\]
necessity follows by adding the three inequalities with weights \(1,1,2\),
and sufficiency follows by taking \((x,y)=(-c_2,-c_3)\).  Thus (18) makes
(19) feasible.  The three trace interiors cannot cover the middle plane.
This proves exact infeasibility of the entire fixed middle-plane Farkas normal
cell.

## External sources

none
