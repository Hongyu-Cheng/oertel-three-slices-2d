---
fact_id: f37aced9de558c8d
kind: lemma
author: "mp_r152_regime_a_homothetic_strip"
assurance: LLM-verified
subgoal_id: canonical-root-tail-regime-a-residual-alternatives
depends_on: ["0688f679297c8baa","6e68b44550cac3c8","879a3c45b5f50670"]
source_packet_sha256: 3d5a60c1777f640a251b121d5e57a126c8ad7571bf2ce0ed0a1d50289507aff6
verifier_run: 8ce312ab980e41f1
target_match: null
---

## Statement

Assume the normalized Regime A and Alternative 1 setting of accepted fact `879a3c45b5f50670`. Thus
\[
|A_0|=1,\qquad |A_2|=r,\qquad |K|=s,\qquad
t=\frac{2(1+r+s)}9,
\]
\[
\begin{cases}
0<r\le1/5,\quad 1-r<s<1+r,\\
\text{or}\\
1/5<r<1/3,\quad 1-r<s<2-4r,
\end{cases}
\tag{1}
\]
and there are distinct \(i,j,\ell\), nonconstant affine functions with pairwise nonparallel linear parts,
\[
f_i+f_j+f_\ell=-1,
\tag{2}
\]
and actual low shifts \(a_i,a_\ell\). Put
\[
u_i=|A_0\cap\{f_i\le a_i\}|,\qquad
u_\ell=|A_0\cap\{f_\ell\le a_\ell\}|,
\tag{3}
\]
\[
c_m=|K\cap\{f_m\le0\}|
\qquad(m=i,j,\ell).
\tag{4}
\]

Use the common two-cut coordinates
\[
x=f_i-a_i,\qquad y=f_\ell-a_\ell
\quad\hbox{on }A_0,
\]
\[
x=f_i+a_i,\qquad y=f_\ell+a_\ell
\quad\hbox{on }A_2,
\tag{5}
\]
and assume the endpoint bodies are genuinely homothetic in these coordinates:
\[
A_2=hA_0
\qquad(h>0).
\tag{6}
\]
Then
\[
r=h^2,
\tag{7}
\]
and the actual middle body satisfies
\[
\frac{A_0+A_2}{2}=\frac{1+h}{2}A_0\subseteq K.
\tag{8}
\]
If
\[
h\ge h_0:=\frac{2\sqrt{71}-9}{29},
\tag{9}
\]
then
\[
\boxed{
\max\left\{
c_i+(1+h^2)u_i,\
c_\ell+(1+h^2)u_\ell,\
c_j+h^2
\right\}
\ge
\frac{2(1+h^2+s)}9.}
\tag{10}
\]
This includes empty or full endpoint cut cells, zero mixed or simultaneous-low cells, cutting lines supporting an endpoint body, the case where a middle cutting line passes through the centroid, and all cap-empty, cap-full, and support-face boundaries.

## Proof

We first record the exact homothetic normalization. In the coordinates (5), homothety multiplies every planar area by \(h^2\). Therefore (7) holds, and
\[
|A_2\cap\{x\le0\}|=h^2u_i,\qquad
|A_2\cap\{y\le0\}|=h^2u_\ell.
\tag{11}
\]
If
\[
P=A_0\cap\{x>0,\ y>0\},
\qquad p=|P|,
\]
then its Alternative 1 counterpart is \(hP\), of area
\[
q=h^2p>0.
\tag{12}
\]
Thus the two side expressions in (10) are exactly the two actual low masses. At a midpoint the shifts in (5) cancel, so the middle coordinates are \(x=f_i\), \(y=f_\ell\). Equation (2) becomes
\[
f_j=-1-x-y.
\tag{13}
\]
Compatibility retained in accepted fact `879a3c45b5f50670` gives (8).

Suppose for contradiction that all three expressions in (10) are strictly below
\[
t=\frac{2(1+h^2+s)}9.
\tag{14}
\]
In particular,
\[
c_i<t,\qquad c_\ell<t,\qquad c_j+h^2<t.
\tag{15}
\]
We next prove, from the actual middle body, the estimate
\[
c_i+c_\ell\ge\frac{8s}{9}.
\tag{16}
\]

Let \(g\) be the centroid of \(K\). We use the planar centroid halfspace inequality proved in accepted fact `6e68b44550cac3c8`: every closed halfplane containing \(g\) cuts from \(K\) area at least \(4s/9\). The Regime A lower bound \(s>1-h^2\) gives
\[
\frac{4s}{9}-(t-h^2)
=\frac{2s+7h^2-2}{9}
>\frac{5h^2}{9}>0.
\tag{17}
\]
Consequently \(f_j(g)>0\), since otherwise the \(j\)-cap would have area at least \(4s/9>t-h^2\), contradicting (15).

Equation (2) now gives
\[
f_i(g)+f_\ell(g)=-1-f_j(g)<-1.
\]
After interchanging \(i,\ell\), assume
\[
f_i(g)\le0.
\tag{18}
\]
The centroid halfspace inequality gives
\[
c_i\ge\frac{4s}{9}.
\tag{19}
\]
Also \(t<s\). Indeed, (1) gives \(s>1-h^2\) and \(h^2<1/3\), so
\[
7s>7(1-h^2)>2(1+h^2).
\tag{20}
\]

Define
\[
F(x)=2\sqrt{sx}-2x.
\tag{21}
\]
It is decreasing on \([4s/9,s]\). A direct substitution of (14) gives
\[
4st-(3t-h^2)^2
=
\frac{
4(s-1+h^2)(s+1+2h^2)+h^2(8-9h^2)
}{9}>0.
\tag{22}
\]
Both factors used for the sign are strict by (1). Since \(3t-h^2>0\), equation (22) yields
\[
F(t)>t-h^2>c_j.
\tag{23}
\]

If \(f_\ell(g)\le0\), the centroid halfspace inequality and the monotonicity of \(F\) give
\[
c_\ell\ge\frac{4s}{9}
=F\left(\frac{4s}{9}\right)
\ge F(c_i).
\tag{24}
\]
If \(f_\ell(g)>0\), apply accepted theorem `0688f679297c8baa` with
\[
(f_1,f_2,f_3)=(f_\ell,f_j,f_i).
\]
Its two required centroid signs are \(f_\ell(g)>0\) and \(f_j(g)>0\), and it gives
\[
\max\{c_\ell,c_j\}\ge F(c_i).
\tag{25}
\]
Equations (15), (19), and (20) put
\[
\frac{4s}{9}\le c_i<t<s.
\]
Hence \(F(c_i)>F(t)>c_j\) by (23), so (25) forces
\[
c_\ell\ge F(c_i).
\tag{26}
\]
Thus (26) also holds in the case (24).

The function
\[
x+F(x)=2\sqrt{sx}-x
\]
is increasing for \(0<x<s\). Equations (19), (20), and (26) therefore give
\[
c_i+c_\ell
\ge c_i+F(c_i)
\ge \frac{4s}{9}+F\left(\frac{4s}{9}\right)
=\frac{8s}{9}.
\]
This proves (16). Notice that every inequality is nonstrict at
\(f_i(g)=0\), \(f_\ell(g)=0\), and \(c_i=4s/9\), so no centroid or support boundary has been discarded.

Now use the actual homothetic midpoint body. Put
\[
\lambda=\frac{1+h}{2},\qquad d=\lambda^2,
\qquad D=\lambda A_0.
\tag{27}
\]
By (8), \(D\subseteq K\), and \(|D|=d\). Since \(\lambda>0\),
\[
|D\cap\{x\le0\}|=d\,u_i,\qquad
|D\cap\{y\le0\}|=d\,u_\ell.
\tag{28}
\]
Moreover, all affine cutting lines have planar area zero, and the union bound gives
\[
p\ge1-u_i-u_\ell.
\tag{29}
\]
Every point of \(\lambda P\) has \(x>0,y>0\), so (13) puts it in the actual \(j\)-cap \(\{x+y\ge-1\}\). Therefore
\[
c_j\ge d\,p\ge d(1-u_i-u_\ell).
\tag{30}
\]
Equations (28)-(30) remain valid if any cut cell is empty, if a cutting line supports \(A_0\), or if the simultaneous-low cell has zero area.

Adding the two strict side inequalities from the assumed failure of (10), and then using (16), yields
\[
(1+h^2)(u_i+u_\ell)
<
2t-c_i-c_\ell
\le
2t-\frac{8s}{9}
=\frac{4(1+h^2-s)}9.
\tag{31}
\]
Combining (30) and (31),
\[
c_j>
d\left(
1-\frac{4(1+h^2-s)}{9(1+h^2)}
\right).
\tag{32}
\]
The root inequality in (15) is therefore impossible whenever
\[
G(h,s):=
d\left(
1-\frac{4(1+h^2-s)}{9(1+h^2)}
\right)
-(t-h^2)
\ge0.
\tag{33}
\]
Exact simplification gives
\[
G(h,s)=
\frac{
33h^4+10h^3+30h^2+10h-3-4(1-h)^2s
}{36(1+h^2)}.
\tag{34}
\]
For \(0<h<1\),
\[
\frac{\partial G}{\partial s}
=-\frac{(1-h)^2}{9(1+h^2)}<0.
\tag{35}
\]

We now check both Regime A upper endpoints from accepted fact `879a3c45b5f50670`.

First suppose \(h^2\le1/5\). Then \(s<1+h^2\), and (34) gives
\[
G(h,1+h^2)=\frac{29h^2+18h-7}{36}.
\tag{36}
\]
The quadratic numerator is strictly increasing for \(h>0\), and its positive root is
\[
\frac{-18+\sqrt{18^2+4\cdot29\cdot7}}{58}
=\frac{2\sqrt{71}-9}{29}
=h_0.
\tag{37}
\]
Thus (9), (35), and the strict inequality \(s<1+h^2\) imply
\[
G(h,s)>G(h,1+h^2)\ge0.
\tag{38}
\]

Now suppose \(1/5<h^2<1/3\). Then \(s<2-4h^2\), and
\[
G(h,2-4h^2)
=
\frac{
49h^4-22h^3+38h^2+26h-11
}{36(1+h^2)}.
\tag{39}
\]
On \(1/\sqrt5<h<1/\sqrt3\),
\[
49h^4+\!38h^2-22h^3
\ge
\frac{49}{25}+\frac{38}{5}-\frac{22}{3\sqrt3}>0,
\tag{40}
\]
because \(3\sqrt3>5\), and
\[
26h-11>\frac{26}{\sqrt5}-11>0.
\tag{41}
\]
Hence the numerator in (39) is positive. Equations (35) and
\(s<2-4h^2\) give
\[
G(h,s)>G(h,2-4h^2)>0.
\tag{42}
\]

Thus \(G(h,s)\ge0\) in every Regime A branch under (9). Equations
(32)-(33) give \(c_j>t-h^2\), contradicting (15). Therefore the three expressions in (10) cannot all be strictly below \(t\), which proves (10).

The proof used cell areas only through inclusions and union bounds whose boundary lines have area zero. It never divided by a cell area, a chord length, or a support distance. Hence all empty-cell, full-cell, supporting-line, collinear-contact, centroid-on-cut, and cap-boundary degeneracies stated above are included.

## External sources

none
