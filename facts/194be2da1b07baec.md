---
fact_id: 194be2da1b07baec
kind: lemma
author: "r099_nine_y_dominant"
assurance: LLM-verified
subgoal_id: nine-cover-y-dominant-normal-wedge
depends_on: ["3c143dfcc90fab8e","8b8d446672f7036b"]
source_packet_sha256: 1933434733a65aea55390872d5ff4024b65dd782de9e8c08169d52d5320d8dd8
verifier_run: 78853bf3d9994ab6
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
Use strict target \(11/48\).  For
\[
u_1(\theta)=(\theta,1),\qquad u_2=(-1,0),\qquad u_3=(0,-1),
\qquad 0\leq\theta\leq\frac12,
\]
define
\[
M_\theta(c)=\inf_{k\in\mathbb R}\sum_{i=0}^2
\left|A_i\cap
\{w:u_1(\theta)\cdot w\leq c+k(i-1)\}\right|
\]
and
\[
R_1(\theta)=\sup\{c\in\mathbb R:M_\theta(c)<11/48\}.
\]
Let \(R_2,R_3\) be the corresponding strict-low endpoints for
\(u_2,u_3\).  Then
\[
R_1(\theta)\leq\frac38
\]
and
\[
R_1(\theta)+\theta R_2+R_3
\leq\frac{2\sqrt{26}-11}{24}<0
\qquad\left(0\leq\theta\leq\frac12\right).
\]
Consequently, no three halfspaces with these three middle-plane normals,
each of total three-slice mass strictly below \(11/48\), have height-one
trace interiors covering \(\mathbb R^2\).

## Proof

Put
\[
F_\theta(t)
=\left|A_1\cap\{(x,y):\theta x+y\leq t\}\right|.
\]
Write the vertices of \(A_1\), in counterclockwise order, as
\[
\begin{aligned}
p&=(-1/2,1/2),&q&=(0,0),&r&=(3/4,0),\\
s&=(1/2,1/4),&v&=(-1/2,3/4).
\end{aligned}
\]
Their \(\theta x+y\) values are
\[
\frac{1-\theta}{2},\qquad 0,\qquad\frac{3\theta}{4},
\qquad\frac{2\theta+1}{4},\qquad\frac{3-2\theta}{4},
\tag{1}
\]
respectively.  The complete support-order boundary list on
\([0,1/2]\) is
\[
\theta=0,\qquad \theta=\frac14,\qquad
\theta=\frac25,\qquad\theta=\frac12.
\tag{2}
\]
At \(\theta=0\), \(q\) and \(r\) tie.  At \(\theta=1/4\), \(p\) and
\(s\) tie.  At \(\theta=2/5\), \(p\) and \(r\) tie.  At
\(\theta=1/2\), \(s\) and \(v\) tie.  There are no other equalities
among the five expressions in (1) on this interval.

We now clip at \(t=3/8\).  The vertex \(q\) is below this level for the
whole interval, while \(v\) is above it.  The vertices \(p\) and \(s\)
meet the level simultaneously at \(\theta=1/4\), and \(r\) meets it at
\(\theta=1/2\).  The support crossing at \(\theta=2/5\) exchanges \(p\)
and \(r\), but both are then strictly below the clipping level.  The tie
at \(\theta=0\) is also strictly below the clipping level, and the
\(\theta=1/2\) tie between \(s\) and \(v\) is strictly above it.
Therefore there are exactly two clipping cells.

For \(0\leq\theta\leq1/4\), the cutting line meets \([p,q]\) at
\[
i_\theta=
\left(-\frac{3}{8(1-\theta)},\frac{3}{8(1-\theta)}\right).
\tag{3}
\]
If
\[
\tau_\theta=\frac{1-4\theta}{4(1-2\theta)},
\]
then its intersection with \([s,v]\) is
\[
j_\theta=
\left(\frac12-\tau_\theta,\frac14+\frac{\tau_\theta}{2}\right).
\tag{4}
\]
Thus, with endpoint coincidences allowed,
\[
A_1\cap\{\theta x+y\leq3/8\}
=\operatorname{conv}\{i_\theta,q,r,s,j_\theta\}.
\]
The shoelace formula gives
\[
F_\theta(3/8)
=\frac{56\theta^2-100\theta+35}
       {128(1-\theta)(1-2\theta)}
\qquad\left(0\leq\theta\leq\frac14\right).
\tag{5}
\]
Its derivative is
\[
\frac{(4\theta-1)(8\theta-5)}
     {128(1-\theta)^2(1-2\theta)^2}\geq0
\qquad\left(0\leq\theta\leq\frac14\right).
\tag{6}
\]
Hence this piece increases from \(35/128\) to \(9/32\).
Formula (3) gives an ordinary edge point at \(\theta=0\), and (3)--(5)
remain finite there, so the vertical endpoint is included without a
limit argument.

For \(1/4\leq\theta\leq1/2\), set
\[
\alpha_\theta=\frac{3(1-2\theta)}{2(1-\theta)},\qquad
\delta_\theta=\frac{4\theta-1}{2}.
\]
The cutting line meets \([r,s]\) and \([p,v]\), respectively, at
\[
k_\theta=
\left(\frac34-\frac{\alpha_\theta}{4},
      \frac{\alpha_\theta}{4}\right),
\qquad
\ell_\theta=
\left(-\frac12,\frac12+\frac{\delta_\theta}{4}\right).
\tag{7}
\]
Therefore
\[
A_1\cap\{\theta x+y\leq3/8\}
=\operatorname{conv}\{p,q,r,k_\theta,\ell_\theta\},
\]
again allowing endpoint coincidences.  Exact shoelace evaluation yields
\[
F_\theta(3/8)
=\frac{35-28\theta-16\theta^2}{128(1-\theta)}
\qquad\left(\frac14\leq\theta\leq\frac12\right).
\tag{8}
\]
Its derivative is
\[
\frac{(4\theta-7)(4\theta-1)}
     {128(1-\theta)^2}\leq0
\qquad\left(\frac14\leq\theta\leq\frac12\right).
\tag{9}
\]
This piece decreases from \(9/32\) to \(17/64\).  The two formulas agree
at \(\theta=1/4\); at \(\theta=1/2\), \(k_\theta=r\), so (8) also
includes that clipping boundary.  Equations (1)--(9) account for every
support-order boundary, every clipping boundary, and both endpoints of
the compact parameter interval.  In particular,
\[
F_\theta(3/8)\geq\frac{17}{64}
=\frac{11}{48}+\frac{7}{192}
>\frac{11}{48}.
\tag{10}
\]

For \(j=0,2\), let
\[
F_{\theta,j}(t)
=\left|A_j\cap\{(x,y):\theta x+y\leq t\}\right|.
\]
Writing \(a=c-k\) in the definition of \(M_\theta(c)\) gives
\[
M_\theta(c)=F_\theta(c)+
\inf_{a\in\mathbb R}
\left(F_{\theta,0}(a)+F_{\theta,2}(2c-a)\right).
\tag{11}
\]
Both terms inside the infimum are nonnegative.  Consequently, (10)
implies
\[
M_\theta(3/8)\geq F_\theta(3/8)>\frac{11}{48}
\qquad\left(0\leq\theta\leq\frac12\right).
\tag{12}
\]
For each fixed \(k\), all three slice thresholds increase with \(c\), so
the corresponding mass is nondecreasing in \(c\).  Taking the infimum
over \(k\) preserves this monotonicity.  Equation (12) therefore gives
\[
R_1(\theta)\leq\frac38
\qquad\left(0\leq\theta\leq\frac12\right).
\tag{13}
\]

Accepted facts `3c143dfcc90fab8e` and `8b8d446672f7036b` give
\[
R_2=-1+\frac{\sqrt{78}}{12},\qquad
R_3=-\frac56+\frac{\sqrt{26}}{12}.
\tag{14}
\]
Since \(78<9^2\), we have \(R_2<-1/4<0\).  Thus (13), (14), and
\(\theta\geq0\) imply
\[
\begin{aligned}
R_1(\theta)+\theta R_2+R_3
&\leq\frac38+\theta R_2+R_3\\
&\leq\frac38+R_3
=\frac{2\sqrt{26}-11}{24}<0,
\end{aligned}
\tag{15}
\]
where the last strict inequality follows from
\(26<(11/2)^2\).  This proves the endpoint inequality uniformly,
including \(\theta=0\).

Finally, suppose three halfspaces with the displayed normals have
height-one thresholds \(c_1,c_2,c_3\) and total masses strictly below
\(11/48\).  By the definitions of the three strict-low endpoints,
\[
c_1\leq R_1(\theta),\qquad c_2\leq R_2,\qquad c_3\leq R_3.
\]
Because all Farkas weights are nonnegative, (15) gives
\[
c_1+\theta c_2+c_3<0.
\tag{16}
\]
The closed complements of the height-one trace interiors are
\[
\theta x+y\geq c_1,\qquad x\leq-c_2,\qquad y\leq-c_3.
\tag{17}
\]
The point \((-c_2,-c_3)\) satisfies (17) exactly when
\(c_1+\theta c_2+c_3\leq0\), which holds by (16).  Hence the three trace
interiors cannot cover the plane.  When \(\theta=0\), the same point
works and the second inequality simply has zero Farkas weight; no
positive rescaling or limiting argument is used.

## External sources

none
