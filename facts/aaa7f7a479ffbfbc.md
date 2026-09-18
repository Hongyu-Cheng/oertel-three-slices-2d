---
fact_id: aaa7f7a479ffbfbc
kind: lemma
author: "mp_r92_regime_a_residual_alternatives"
assurance: LLM-verified
subgoal_id: canonical-root-tail-regime-a-residual-alternatives
depends_on: ["756b87a16a89ea8f"]
source_packet_sha256: 68e4c4fd4fa68121ab63f6e89d182435af41a620118a13b8a2bede618c1b722a
verifier_run: 9768688d6061439c
target_match: null
---

## Statement

Use the coordinates
\[
\sigma=x+y,\qquad \tau=x-y.
\tag{1}
\]
Consider an admissible member of the following exact rational triangle
family. For rational \(A,D,\lambda>0\), put
\[
z=\frac{6}{200(A^2+D^2)-3(A+D+1)^2},
\qquad x_0=\lambda,\qquad y_0=\frac z\lambda,
\tag{2}
\]
\[
U_0=(-Ax_0,(1+A)y_0),\qquad
V_0=((1+D)x_0,-Dy_0),
\tag{3}
\]
\[
\eta_0=y_0+\frac{3}{100Ax_0},
\qquad
\xi_0=x_0+\frac{3}{100Dy_0},
\tag{4}
\]
and let \(W_0\) be the intersection of the line through
\(U_0,(0,\eta_0)\) and the line through \(V_0,(\xi_0,0)\). Set
\[
A_0=\operatorname{conv}\{U_0,V_0,W_0\}.
\tag{5}
\]

For rational \(\mu>0\), put
\[
X=\mu,\qquad Y=\frac1{100\mu},
\tag{6}
\]
and choose rational \(A',D'>1\) satisfying
\[
82A'^2-36A'D'+36A'+82D'^2+36D'-243=0.
\tag{7}
\]
Define
\[
U_2=(-A'X,(A'-1)Y),\qquad
V_2=((D'-1)X,-D'Y),
\tag{8}
\]
\[
\eta_2=-Y+\frac9{400A'X},
\qquad
\xi_2=-X+\frac9{400D'Y},
\tag{9}
\]
and let \(W_2\) be the intersection of the line through
\(U_2,(0,\eta_2)\) and the line through \(V_2,(\xi_2,0)\). Set
\[
A_2=\operatorname{conv}\{U_2,V_2,W_2\}.
\tag{10}
\]
Admissible means that all displayed denominators are positive, both
triangles are nondegenerate, \(W_0,W_2\) lie in the open first
quadrant, and the stated line incidences give the four quadrant cells.
Then the resulting exact cell areas are
\[
\begin{array}{c|cccc}
&(+,+)&(-,+)&(+,-)&(-,-)\\ \hline
A_0&97/100&3/200&3/200&0\\
A_2&9/200&1/160&1/160&1/200.
\end{array}
\tag{11}
\]
In particular,
\[
|A_0|=1,\qquad |A_2|=\frac1{16}.
\tag{12}
\]
Let
\[
P=A_0\cap\{x\ge0,y\ge0\},\qquad
Q=A_2\cap\{x\ge0,y\ge0\},
\tag{13}
\]
and retain the high-high constraint
\[
\left|\frac{P+Q}{2}\right|<\frac{29}{80}.
\tag{14}
\]

Suppose the following support order holds:
\[
\sigma(U_h)<\sigma(V_h)<\sigma(W_h)
\qquad(h=0,2),
\tag{15}
\]
and define its support-position subchamber by
\[
\sigma(U_0)+\sigma(U_2)\ge-2.
\tag{16}
\]
Write
\[
T_{h1}=U_h,\qquad T_{h2}=V_h,\qquad T_{h3}=W_h,
\]
\[
\alpha_{hk}=\sigma(T_{hk}),\qquad
\beta_{hk}=\tau(T_{hk}),\qquad
a_0=1,\quad a_2=\frac1{16}.
\tag{17}
\]
For \(1\le p<q\le3\), define the affine edge function
\[
L_{h,pq}(s)
=
\beta_{hp}
+
\frac{\beta_{hq}-\beta_{hp}}{\alpha_{hq}-\alpha_{hp}}
(s-\alpha_{hp}).
\tag{18}
\]
If
\[
I_h(s)=
\{\tau:(x,y)\in A_h,\ x+y=s,\ x-y=\tau\},
\]
then its two endpoints are \(L_{h,13}(s)\) and \(L_{h,12}(s)\) for
\(\alpha_{h1}\le s\le\alpha_{h2}\), and \(L_{h,13}(s)\) and
\(L_{h,23}(s)\) for
\(\alpha_{h2}\le s\le\alpha_{h3}\). Consequently its \(\tau\)-width is
\[
w_h(s)=
\frac{4a_h}{\alpha_{h3}-\alpha_{h1}}
\begin{cases}
\dfrac{s-\alpha_{h1}}{\alpha_{h2}-\alpha_{h1}},
&\alpha_{h1}\le s\le\alpha_{h2},\\[6pt]
\dfrac{\alpha_{h3}-s}{\alpha_{h3}-\alpha_{h2}},
&\alpha_{h2}\le s\le\alpha_{h3},\\[6pt]
0,&\text{otherwise}.
\end{cases}
\tag{19}
\]

Put
\[
B=\frac{A_0+A_2}{2},
\qquad
s_-=\frac{\alpha_{01}+\alpha_{21}}2,
\qquad
s_+=\frac{\alpha_{03}+\alpha_{23}}2.
\tag{20}
\]
Let \(\ell_h(s)\) and \(u_h(s)\) be the smaller and larger endpoints of
\(I_h(s)\), as given by (18). For \(s\in[s_-,s_+]\), put
\[
J_s=
[\alpha_{01},\alpha_{03}]
\cap
[2s-\alpha_{23},\,2s-\alpha_{21}].
\tag{21}
\]
The exact endpoints of the \(\tau\)-section of \(B\) are
\[
\ell_B(s)
=
\frac12
\min_{t\in J_s}
\bigl(\ell_0(t)+\ell_2(2s-t)\bigr),
\tag{22}
\]
\[
u_B(s)
=
\frac12
\max_{t\in J_s}
\bigl(u_0(t)+u_2(2s-t)\bigr).
\tag{23}
\]
Therefore
\[
\left|B\cap\{x+y\ge-1\}\right|
=
\frac12
\int_{\max\{-1,s_-\}}^{s_+}
\bigl(u_B(s)-\ell_B(s)\bigr)\,ds.
\tag{24}
\]
Under (11), (14), (15), and (16),
\[
\left|B\cap\{x+y\ge-1\}\right|
\ge\frac{25}{64}
=\frac{29}{80}+\frac9{320}
>\frac{29}{80}.
\tag{25}
\]

This chamber contains the exact calibration
\[
A=\frac12,\qquad D=\frac35,\qquad \lambda=1,\qquad
\mu=\frac37,
\]
\[
A'=\frac{58689}{57928},\qquad
D'=\frac{70929}{57928}.
\tag{26}
\]

## Proof

Fix \(h\in\{0,2\}\). Condition (15) says that every line
\(\{\sigma=s\}\) between the first and second vertex meets the two
edges \(T_{h1}T_{h2}\) and \(T_{h1}T_{h3}\), while every such line
between the second and third vertex meets the two edges
\(T_{h1}T_{h3}\) and \(T_{h2}T_{h3}\). Linear interpolation along an
edge gives (18) and the endpoint assertion preceding (19).

The absolute difference of the two endpoint functions is linear on
each of the intervals
\([\alpha_{h1},\alpha_{h2}]\) and
\([\alpha_{h2},\alpha_{h3}]\), vanishes at the outer endpoint, and has
the same value \(H_h\) at \(\alpha_{h2}\). Since the Jacobian of
\((x,y)\mapsto(\sigma,\tau)\) is \(2\),
\[
a_h
=
\frac12\int_{\alpha_{h1}}^{\alpha_{h3}}w_h(s)\,ds
=
\frac{H_h(\alpha_{h3}-\alpha_{h1})}{4}.
\]
Thus \(H_h=4a_h/(\alpha_{h3}-\alpha_{h1})\), which proves (19).

A point in the section of \(B\) at \(\sigma=s\) is the average of a
point in the section of \(A_0\) at \(\sigma=t\) and a point in the
section of \(A_2\) at \(\sigma=2s-t\). The feasible values of \(t\)
are exactly (21). For each such \(t\), the attainable \(\tau\)-values
form the interval
\[
\frac{
[\ell_0(t),u_0(t)]
+
[\ell_2(2s-t),u_2(2s-t)]
}{2}.
\]
Their union is the section of the convex set \(B\), hence is itself an
interval. Its lower and upper endpoints are exactly (22) and (23).
Finally \(dx\,dy=\frac12\,d\sigma\,d\tau\), which proves (24).
This also makes the calculation on every fixed support-order chamber
finite: the functions in (22)-(23) are extrema of piecewise-affine
functions on an interval. For each fixed \(s\), an extremum is attained
at an endpoint of \(J_s\), or where \(t\) or \(2s-t\) reaches a middle
vertex. Evaluating this finite list and taking its lower or upper
envelope makes \(\ell_B,u_B\) piecewise affine.

By (15),
\[
\min_{A_0}\sigma=\sigma(U_0),\qquad
\min_{A_2}\sigma=\sigma(U_2).
\]
Support functions add under Minkowski addition, so (16) is exactly the
containment
\[
B\subseteq\{x+y\ge-1\}.
\tag{27}
\]
Thus the left side of (25) equals \(|B|\). Applying the planar
Brunn--Minkowski inequality recorded in accepted fact
`756b87a16a89ea8f` to the saturated full bodies gives
\[
\sqrt{|B|}
\ge
\frac{\sqrt{|A_0|}+\sqrt{|A_2|}}2
=
\frac{1+1/4}{2}
=\frac58.
\]
Using (12) proves
\[
|B|\ge\frac{25}{64}
=\frac{29}{80}+\frac9{320}.
\]
The high-high condition (14) is retained but is not needed for this
stronger full-body contradiction.

For completeness, the cell vector is forced by the displayed family,
not an additional numerical specialization. The line \(U_0V_0\) has
axis intercepts \((x_0,0)\) and \((0,y_0)\). The two mixed-cell areas
are
\[
\frac{Ax_0(\eta_0-y_0)}2
=
\frac{Dy_0(\xi_0-x_0)}2
=\frac3{200},
\tag{28}
\]
and the negative-negative cell has area zero. Direct evaluation of the
triangle determinant gives
\[
|A_0|
=
\frac{3z(A+D+1)^2}
{2\left(100z(A^2+D^2)-3\right)}
=1
\tag{29}
\]
by (2). Hence its positive-positive cell has area \(97/100\).

Similarly, the line \(U_2V_2\) has axis intercepts
\((-X,0)\) and \((0,-Y)\). Its negative-negative cell has area
\[
\frac{XY}{2}=\frac1{200},
\]
and each mixed cell has area
\[
\frac{A'X(\eta_2+Y)}2-\frac1{200}
=
\frac{D'Y(\xi_2+X)}2-\frac1{200}
=\frac1{160}.
\tag{30}
\]
Another determinant evaluation gives
\[
|A_2|
=
\frac{9(A'+D'-1)^2}
{200(4A'^2+4D'^2-9)}
=\frac1{16},
\tag{31}
\]
where the last equality is equivalent to (7). The remaining
positive-positive cell therefore has area \(9/200\), proving (11).

It remains to verify that (26) lies in the stated chamber. Substitution
gives
\[
\begin{aligned}
A_0=\operatorname{conv}\Bigl\{&
\left(-\frac12,\frac{900}{10877}\right),
\left(\frac85,-\frac{360}{10877}\right),
\left(\frac{937}{126},\frac{45480}{76139}\right)
\Bigr\},
\end{aligned}
\tag{32}
\]
\[
\begin{aligned}
A_2=\operatorname{conv}\Bigl\{&
\left(-\frac{176067}{405496},\frac{5327}{17378400}\right),
\left(\frac{39003}{405496},-\frac{165501}{5792800}\right),\\
&
\left(
\frac{1119610053}{726750206},
\frac{1333772559}{10382145800}
\right)
\Bigr\}.
\end{aligned}
\tag{33}
\]
For \(A_0\), the three \(\sigma\)-values are respectively negative,
strictly between \(1\) and \(2\), and greater than \(7\). For \(A_2\),
they are respectively negative, strictly between \(0\) and \(1\), and
greater than \(3/2\). Hence (15) holds. Direct addition of the two
lower support values gives
\[
s_-=
-\frac{1126221714047}{2646347995200}
>-1,
\tag{34}
\]
with exact gap
\[
1+s_-=
\frac{1520126281153}{2646347995200}>0.
\]
Thus (16) holds strictly. The defining intercept and determinant
identities give the cell vector (11). Clipping (32)-(33) at the two
coordinate axes gives
\[
\begin{aligned}
P=\operatorname{conv}\Bigl\{&
\left(0,\frac{600}{10877}\right),(1,0),
\left(\frac{22877}{12000},0\right),\\
&
\left(\frac{937}{126},\frac{45480}{76139}\right),
\left(0,\frac{62631}{543850}\right)
\Bigr\},
\end{aligned}
\tag{35}
\]
\[
\begin{aligned}
Q=\operatorname{conv}\Bigl\{&
(0,0),\left(\frac{943}{2627},0\right),
\left(
\frac{1119610053}{726750206},
\frac{1333772559}{10382145800}
\right),\\
&
\left(0,\frac{55727}{1956300}\right)
\Bigr\}.
\end{aligned}
\tag{36}
\]
Taking the convex hull of the pairwise vertex sums and using the
shoelace formula gives
\[
\left|\frac{P+Q}{2}\right|
=
\frac{41921418197405626773}
{116290005717026814400}
<\frac{29}{80},
\tag{37}
\]
whose exact slack is
\[
\frac{233708875016593447}
{116290005717026814400}>0.
\]
Therefore the calibration satisfies every hypothesis and belongs to
the excluded chamber.

## External sources

none
