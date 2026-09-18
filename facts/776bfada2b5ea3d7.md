---
fact_id: 776bfada2b5ea3d7
kind: lemma
author: "r098_tail_unequal_triangle"
assurance: LLM-verified
subgoal_id: tail-row-aligned-triangle-unequal-supports
depends_on: ["15bb2c1680a0254e"]
source_packet_sha256: 6e5e23571222cf5c403f5332a8b0f19e1209296459fb8dee899cffba0703304a
verifier_run: 08c1962afbc844b9
target_match: null
---

## Statement

Let \(g_i,g_\ell,g_q\) be affine functions on one affine plane with
\[
g_i+g_\ell+g_q=1,
\]
and use affine coordinates
\[
x=g_i,\qquad y=g_\ell.
\]
Let \(a,b,c\in\mathbb Q\), put
\[
L=a+b+c>0,
\]
and let
\[
K=\{(x,y):x\ge-a,\ y\ge-b,\ x+y\le c\}.
\tag{1}
\]
Let \(A_0,A_2\) be arbitrary nonempty two-dimensional rational convex
polygons satisfying
\[
\frac{A_0+A_2}{2}\subseteq K.
\tag{2}
\]
After interchanging the endpoint labels if necessary, write
\[
M=|A_0|\ge m=|A_2|,\qquad k=|K|,\qquad
t=\frac{2(M+m+k)}9.
\tag{3}
\]
Assume that \((M,m,k)\) lies in the exact strict residual area domain of
accepted fact `15bb2c1680a0254e`, and assume
\[
D_0:=3t-k-m>m.
\tag{4}
\]
For \(j\in\{i,\ell,q\}\), put
\[
c_j=|K\cap\{g_j\ge0\}|.
\tag{5}
\]
For \(r\in\{0,2\}\) and \(j\in\{i,\ell\}\), define
\[
\alpha_{rj}=\min_{A_r}g_j,\qquad
\beta_{rj}=\max_{A_r}g_j,\qquad
w_{rj}=\beta_{rj}-\alpha_{rj},
\tag{6}
\]
\[
R_j=\beta_{0j}+\beta_{2j},\qquad
\sigma_j=\frac{w_{0j}^2}{M}+\frac{w_{2j}^2}{m},
\tag{7}
\]
and
\[
\Psi_j(R)=
\begin{cases}
0,&R\le0,\\
\min\{R^2/\sigma_j,m\},&R>0.
\end{cases}
\tag{8}
\]
If
\[
c_q+m<t,
\tag{9}
\]
then
\[
\Psi_i(R_i)+\Psi_\ell(R_\ell)>2t-c_i-c_\ell.
\tag{10}
\]
The conclusion includes every feasible middle-cap cell, every support-contact
boundary, and every zero, quadratic, and plateau boundary in (8).
Rationality and polygonality are not used beyond compactness, positive area,
and the existence of the displayed supports and widths.

## Proof

Let
\[
\Delta=\left|\det(\nabla g_i,\nabla g_\ell)\right|>0.
\]
Coordinate area in \((x,y)\) is \(\Delta\) times planar area.  Make the
change of variables
\[
X=\frac{x}{L},\qquad Y=\frac{y}{L},
\]
and multiply every planar area and every value of \(\Psi_j\) by
\(\Delta/L^2\).  Explicitly,
\[
\widetilde M=\frac{\Delta M}{L^2},\qquad
\widetilde m=\frac{\Delta m}{L^2},\qquad
\widetilde k=\frac{\Delta k}{L^2},
\]
\[
\widetilde R_j=\frac{R_j}{L},\qquad
\widetilde w_{rj}=\frac{w_{rj}}L,\qquad
\widetilde\sigma_j=\frac{\sigma_j}{\Delta},
\]
and
\[
\widetilde\Psi_j(\widetilde R_j)
=\frac{\Delta}{L^2}\Psi_j(R_j).
\]
Thus the strict residual inequalities, (4), (9), and the sign of the
difference in (10) are unchanged.  Put
\[
\alpha=\frac aL,\qquad
\beta=\frac bL,\qquad
z=\frac1L,\qquad
S=\alpha+\beta.
\tag{11}
\]
After dropping tildes and again writing \(x,y\) for the normalized
coordinates, the middle triangle is
\[
K=\operatorname{conv}\{
(-\alpha,-\beta),
(1-\alpha,-\beta),
(-\alpha,1-\beta)\},
\tag{12}
\]
and
\[
k=\frac12.
\tag{13}
\]
The \(q\)-cap is now cut out by
\[
x+y\le z.
\tag{14}
\]

The strict residual area domain in accepted fact `15bb2c1680a0254e`
contains
\[
1-\frac mM<\frac kM<1+\frac mM.
\]
Using (13), this is
\[
M-m<\frac12<M+m.
\tag{15}
\]
In particular,
\[
M<\frac12+m.
\tag{16}
\]

We first enumerate the \(q\)-cap cells.  On (12), the coordinate \(x+y\)
ranges from \(-S\) to \(1-S\).  If
\[
h:=S+z,
\tag{17}
\]
then direct clipping gives
\[
c_q=
\begin{cases}
0,&h\le0,\\[2pt]
\dfrac{h^2}{2},&0\le h\le1,\\[6pt]
\dfrac12,&h\ge1.
\end{cases}
\tag{18}
\]
The formulas agree at \(h=0\) and \(h=1\).

The full-\(q\)-cap cell \(h\ge1\), including its boundary, is infeasible.
Indeed, (16) gives
\[
t=\frac{2(M+m+1/2)}9
<\frac{4(m+1/2)}9
<m+\frac12=c_q+m,
\]
contrary to (9).  Hence
\[
h<1.
\tag{19}
\]

The tail also gives the first support estimate
\[
S<\sqrt M.
\tag{20}
\]
If \(h\le0\), then \(S=h-z<0\), so (20) is immediate.  If \(0<h<1\),
then (9) and (18) give
\[
h^2<\frac{4M-14m+2}{9}.
\tag{21}
\]
The right side of (21) is strictly smaller than \(M\), because the right
inequality in (15) yields
\[
5M+14m=5(M+m)+9m>\frac52>2.
\]
Thus \(h<\sqrt M\).  Since \(z>0\), one has \(S=h-z<h\), proving (20)
also in the proper-\(q\)-cap cell.

We next obtain the scalar bound needed for the two remaining middle caps:
\[
S<\frac23.
\tag{22}
\]
There is nothing to prove if \(S\le0\).  If \(S>0\), then
\(h=S+z>S>0\), so (19) places the \(q\)-cap in its proper cell.  Equations
(9) and (18) give
\[
m+\frac{S^2}{2}
<m+\frac{h^2}{2}
<t.
\]
By (16),
\[
t<\frac{2(1+2m)}9.
\]
Consequently
\[
\frac{S^2}{2}<\frac{2-5m}{9}<\frac29,
\]
which proves (22).

For a real parameter \(\theta\), direct clipping of (12) by the
corresponding coordinate halfspace gives
\[
C(\theta)=
\begin{cases}
\dfrac12,&\theta\le0,\\[4pt]
\dfrac{(1-\theta)^2}{2},&0\le\theta\le1,\\[6pt]
0,&\theta\ge1.
\end{cases}
\tag{23}
\]
The formulas agree at both boundaries.  In particular,
\[
c_i=C(\alpha),\qquad c_\ell=C(\beta).
\tag{24}
\]
If either \(\alpha\le0\) or \(\beta\le0\), one of the two caps is full,
and hence
\[
c_i+c_\ell\ge\frac12>\frac49.
\tag{25}
\]
Otherwise \(\alpha,\beta>0\).  Equation (22) then implies
\(0<\alpha,\beta<1\), so both caps are proper and
\[
\begin{aligned}
c_i+c_\ell
&=\frac{(1-\alpha)^2+(1-\beta)^2}{2}\\
&=1-S+\frac{\alpha^2+\beta^2}{2}\\
&\ge1-S+\frac{S^2}{4}
=\left(1-\frac S2\right)^2
>\frac49.
\end{aligned}
\tag{26}
\]
Equations (25)-(26) cover the full, proper, and empty cells of both
coordinate caps, including \(\alpha,\beta\in\{0,1\}\), and prove
\[
c_i+c_\ell>\frac49.
\tag{27}
\]

It remains to prove the endpoint payment without assuming
\(\alpha=\beta\).  For \(r\in\{0,2\}\), write
\[
\underline x_r=\min_{A_r}x,\qquad
\overline x_r=\max_{A_r}x,
\]
and define \(\underline y_r,\overline y_r\) analogously.  The first two
facet inequalities in (12), together with midpoint compatibility (2),
give
\[
\underline x_0+\underline x_2\ge-2\alpha,\qquad
\underline y_0+\underline y_2\ge-2\beta.
\tag{28}
\]
Therefore
\[
R_i\ge w_{0i}+w_{2i}-2\alpha,\qquad
R_\ell\ge w_{0\ell}+w_{2\ell}-2\beta.
\tag{29}
\]
No common center or endpoint symmetry is used in (28)-(29).

Each endpoint body is contained in its coordinate bounding rectangle.
Hence
\[
w_{0i}w_{0\ell}\ge M,\qquad
w_{2i}w_{2\ell}\ge m.
\tag{30}
\]
All four widths are positive because the endpoint bodies are
two-dimensional.

Put
\[
p=\sqrt M,\qquad q=\sqrt m,\qquad \rho=\frac pq\ge1,
\tag{31}
\]
and normalize the four widths by
\[
u_i=\frac{w_{0i}}p,\qquad
u_\ell=\frac{w_{0\ell}}p,\qquad
v_i=\frac{w_{2i}}q,\qquad
v_\ell=\frac{w_{2\ell}}q.
\tag{32}
\]
Equation (30) becomes
\[
u_i u_\ell\ge1,\qquad v_i v_\ell\ge1.
\tag{33}
\]
Let
\[
U=u_i+u_\ell,\qquad V=v_i+v_\ell,
\]
\[
d_i^2=u_i^2+v_i^2,\qquad
d_\ell^2=u_\ell^2+v_\ell^2,\qquad
D^2=d_i^2+d_\ell^2.
\tag{34}
\]
By (33), \(U,V\ge2\), and
\[
D^2
=U^2+V^2-2(u_i u_\ell+v_i v_\ell)
\le U^2+V^2-4.
\tag{35}
\]
Set
\[
X=U-2\ge0,\qquad Y=V-2\ge0,\qquad
H=\rho(U-2)+V=\rho X+Y+2.
\tag{36}
\]
An exact expansion gives
\[
\begin{aligned}
H^2-(U^2+V^2-4)
&=(\rho^2-1)X^2+2\rho XY+4(\rho-1)X\\
&\ge0.
\end{aligned}
\tag{37}
\]
Since \(H>0\), equations (35)-(37) imply
\[
H\ge D.
\tag{38}
\]

Now put
\[
s_i=\frac{R_i}{q},\qquad s_\ell=\frac{R_\ell}{q}.
\tag{39}
\]
Adding (29), using (20), and then using (31)-(32) gives the strict joint
support estimate
\[
\begin{aligned}
s_i+s_\ell
&\ge \rho U+V-\frac{2S}{q}\\
&>\rho U+V-2\rho\\
&=H
\ge D.
\end{aligned}
\tag{40}
\]
This is the point at which the unequal lower supports are coupled: only
their sum \(S\) enters (40).

By (7)-(8) and (32)-(34),
\[
\frac{\Psi_j(R_j)}m
=\min\left\{\frac{[s_j]_+^2}{d_j^2},1\right\},
\qquad j\in\{i,\ell\},
\tag{41}
\]
where \([s]_+=\max\{s,0\}\).  We check every clamp cell directly.  If
\(s_i\le0\), then (40) gives
\[
s_\ell>D>d_\ell,
\]
so the \(\ell\)-profile is on its plateau.  The same argument with the
indices exchanged covers \(s_\ell\le0\).  If both supports are positive
and either \(s_i\ge d_i\) or \(s_\ell\ge d_\ell\), the corresponding
profile is again on its plateau.  In the only remaining cell,
\[
0<s_i<d_i,\qquad 0<s_\ell<d_\ell.
\]
Weighted Cauchy and (40) give
\[
\frac{s_i^2}{d_i^2}+\frac{s_\ell^2}{d_\ell^2}
\ge
\frac{(s_i+s_\ell)^2}{d_i^2+d_\ell^2}
>1.
\tag{42}
\]
Thus (41)-(42), including all equality boundaries between the clamp cells,
prove
\[
\Psi_i(R_i)+\Psi_\ell(R_\ell)\ge m.
\tag{43}
\]

Finally, define
\[
\eta=\frac12+m-M>0,
\tag{44}
\]
where positivity is the left inequality in (15).  Then
\[
t=\frac{2(1+2m-\eta)}9.
\tag{45}
\]
Using (27), (43), and (45), one obtains
\[
\begin{aligned}
c_i+c_\ell+\Psi_i(R_i)+\Psi_\ell(R_\ell)-2t
&>\frac49+m-\frac{4(1+2m-\eta)}9\\
&=\frac{m+4\eta}{9}\\
&>0.
\end{aligned}
\tag{46}
\]
Equation (46) is exactly (10).

For completeness, the full-\(q\)-cap cell and its boundary were excluded
before (20); the empty-\(q\)-cap cell, including \(h=0\), is included in
(20)-(22); and the proper-\(q\)-cap cell is treated by its exact area in
(18).  Formula (23) covers all nine pairs of full, proper, and empty
\((i,\ell)\)-cap cells and their boundaries.  Equalities in midpoint
support (28), width products (30), and the transitions
\(s_j=0,d_j\) in (41) are retained throughout.  The strict conclusion in
(46) comes from (22), (27), and \(\eta,m>0\), so no support or clamp
boundary is lost.

## External sources

none
