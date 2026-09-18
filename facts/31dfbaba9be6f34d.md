---
fact_id: 31dfbaba9be6f34d
kind: lemma
author: "r123-quadratic-envelope"
assurance: LLM-verified
subgoal_id: triangle-b-ge-quadratic-envelope
depends_on: ["27ae487131bcd122","6986d9aa136ba907","83ae76262528a9f8","89f1aef98e9b8915"]
source_packet_sha256: 2894af08017737295fdb1d0655f0ea09ae32646ada4eda93b94888be16c3f8c6
verifier_run: 8fd041af31ca47cb
target_match: null
---

## Statement

Assume the surviving transformed triangular \(N=3\) system, residual area chamber, incidence orbit, and literal cap convention of accepted facts `89f1aef98e9b8915`, `6986d9aa136ba907`, and `83ae76262528a9f8`.  In particular,
\[
0<A<B,\qquad 1-A<B<1+A,\qquad
t=\frac{2(1+A+B)}9\leq\frac12,
\]
the endpoint matrices are compatible, all three row masses are strictly below \(t\), and, after the allowed fixed relabeling, the all-nine-nonzero middle matrix has supports
\[
J_1=\{2\},\qquad J_2=\{2,3\},\qquad J_3=\{1\}.
\]
Suppose \(B>1\).  Write
\[
L_{3*}=(p,-a,-b),\qquad d=\max\{a,b\},\quad e=\min\{a,b\},
\]
\[
C=c_3=\frac{p^2}{(p+a)(p+b)},\qquad
\eta=t-C,
\]
and use the accepted quantities
\[
h=\frac{d-e}{p+d},\qquad
\mu=A-\sqrt{A\eta},\qquad
\nu=B-\sqrt{B\eta}.
\]
For every actual row-minimum normalization
\[
x\in[\sqrt A,2-\sqrt B]
\]
satisfying at least one quadratic switch condition
\[
\frac\mu{x^2}\leq h
\quad\text{or}\quad
\frac\nu{(2-x)^2}\leq h,
\]
one has
\[
G_\eta(x)>0.
\]
The weak switch inequalities are intentional: they include both switch equalities, where the two formulas agree.  Consequently a strict third row is impossible on every quadratic-quadratic or mixed branch.  By accepted fact `6986d9aa136ba907`, the same conclusion holds on every zero-middle-entry boundary stratum.

## Proof

We first extract the constraint supplied by the first two strict rows.  In the open chamber write
\[
L_{1*}=(-X,Y,-Z),\qquad
L_{2*}=(-D,U,W),\qquad
L_{3*}=(p,-a,-b),
\]
where all nine displayed magnitudes are positive.  The centroid incidence in accepted fact `6986d9aa136ba907` says that the first two small-endpoint caps contain the centroid.  A halfplane cap of a triangle containing its centroid has normalized area at least \(4/9\): moving its boundary to the centroid can only decrease the cap, and a line through the centroid cuts off at most \(5/9\), with equality when it is parallel to a side.  Therefore the first two strict row inequalities give
\[
c_i+\frac{4A}{9}<t\qquad(i=1,2),
\]
where \(c_i=\mathcal C(L_{i*};0)\).  Thus
\[
c_1,c_2<\kappa:=\frac{2(1+B-A)}9<\frac49. \tag{1}
\]
The last inequality uses the strict residual inequality \(B<1+A\).

The literal one-positive and two-positive cap formulas give
\[
c_1=\frac{Y^2}{(X+Y)(Z+Y)},
\qquad
c_2=1-\frac{D^2}{(D+U)(D+W)}. \tag{2}
\]
Set
\[
r=\frac XY,\quad s=\frac ZY,\quad
u=\frac UD,\quad v=\frac WD,\quad
\lambda=\frac YD,
\]
and put
\[
\alpha=\frac{6\sqrt5-9}{4},\qquad \beta=\frac54. \tag{3}
\]
By (1)--(2),
\[
(1+r)(1+s)>\frac94,qquad
(1+u)(1+v)<\frac95. \tag{4}
\]
The first inequality implies
\[
r+\beta s>
\frac{5-4s}{4(1+s)}+\frac54s
=\alpha+\frac{5(s+1-3/\sqrt5)^2}{4(1+s)}
\geq\alpha. \tag{5}
\]
For the second inequality, \(0<u<4/5\) and
\[
v<\frac{4-5u}{5(1+u)}.
\]
Consequently
\[
\alpha u+\beta v
<\alpha u+\frac{4-5u}{4(1+u)}\leq1. \tag{6}
\]
The last function is convex on \([0,4/5]\); its endpoint values are \(1\) and \(4\alpha/5<1\).

The column-sum identities are
\[
p=X+D+1,qquad a=Y+U-1,qquad b=W-Z-1.
\]
After division by \(D\), (5)--(6) give the exact identity and strict bound
\[
\begin{aligned}
\frac{p-\alpha a-\beta b}{D}
={}&1-\alpha u-\beta v
+\lambda(r-\alpha+\beta s)
+\frac{1+\alpha+\beta}{D}>0.
\end{aligned} \tag{7}
\]
Since \(\beta>\alpha\), sorting \(a,b\) in (7) yields
\[
p>\alpha d+\beta e. \tag{8}
\]

Put \(P=p+d\) and \(\delta=d/P\).  Then \(e/P=\delta-h\), and (8), together with
\(1+\alpha+\beta=3\sqrt5/2\), becomes
\[
6\sqrt5\,\delta<4+5h. \tag{9}
\]
Also \(p>d+e\), so \(0\leq h<\delta<1/2\).  If \(h=0\), neither positive capacity argument can be below the join, so only \(h>0\) matters below.  Directly,
\[
C=\frac{(1-\delta)^2}{1-h}. \tag{10}
\]
Equations (9)--(10) imply
\[
C>C_*(h):=
\frac{(6\sqrt5-4-5h)^2}{180(1-h)}. \tag{11}
\]
On \(0<h<1/2\), \(C_*\) decreases up to
\[
h_0=\frac{14-6\sqrt5}{5}
\]
and then increases, and
\[
\min C_*=C_*(h_0)=\frac{2\sqrt5}{3}-1. \tag{12}
\]

We next show that the large endpoint is always on the linear branch.  Define
\[
E(h)=\frac12-C_*(h),qquad
A_*(h)=\frac94C_*(h)-1. \tag{13}
\]
The strict third row gives \(C<t\leq1/2\).  Hence (11) gives
\[
0<\eta=t-C<E(h). \tag{14}
\]
Moreover \(B<1+A\) implies
\(t<4(1+A)/9\), and therefore
\[
A>A_*(h),\qquad B>1. \tag{15}
\]
The functions \(z\mapsto z-\sqrt{zq}\) are increasing throughout the ranges in (14)--(15).  Thus
\[
\mu>m(h):=A_*(h)-\sqrt{A_*(h)E(h)},
\qquad
\nu>n(h):=1-\sqrt{E(h)}. \tag{16}
\]
Here positivity and monotonicity follow already from (12):
\(C_*(h)>49/100\), so \(A_*(h)>41/400\) and \(E(h)<1/100\).

Since \(x\geq\sqrt A\), (16) yields
\[
\frac{\nu}{(2-x)^2}>
\frac{n(h)}{(2-\sqrt{A_*(h)})^2}. \tag{17}
\]
For \(h\leq1/4\), (12) gives \(n(h)>9/10\) and
\(\sqrt{A_*(h)}>3/10\), so the right side of (17) is larger than
\[
\frac{9/10}{(17/10)^2}=\frac{90}{289}>\frac14\geq h. \tag{18}
\]
For \(h>1/4\), monotonicity of \(C_*\) and the exact inequality
\[
C_*(1/4)>\frac{247}{500}
\]
give \(E(h)<3/500\), \(A_*(h)>223/2000>1/9\), and hence
\[
\frac{n(h)}{(2-\sqrt{A_*(h)})^2}
>\frac{461/500}{(5/3)^2}
=\frac{4149}{12500}>\frac{329}{1000}. \tag{19}
\]
Finally, \(C_*(329/1000)>1/2\); since \(C>C_*(h)\) and \(C<1/2\), monotonicity gives \(h<329/1000\).  Equations (17)--(19) prove
\[
\frac\nu{(2-x)^2}>h. \tag{20}
\]
Thus a quadratic \(B\)-branch, including its switch equality, is impossible.

It remains to prove positivity on the \(A\)-quadratic/\(B\)-linear branch.  We include the \(A\)-switch by assuming
\[
\frac\mu{x^2}\leq h.
\]
Put \(y=\sqrt{\mu/h}\).  Since \(B>1\), one has \(x<1\), so
\[
0<y\leq x<1. \tag{21}
\]
The branch formula of accepted fact `83ae76262528a9f8`, divided by \(P=p+d\), is
\[
\frac{G_\eta(x)}P
=-2\delta+\sqrt{\mu h}+\frac\nu{2-x}. \tag{22}
\]
By (9), (16), (21), and monotonicity in \(\mu,\nu\), the right side of (22) is strictly larger than
\[
\Phi(h):=
\sqrt{m(h)h}
+\frac{n(h)}{2-\sqrt{m(h)/h}}
-\frac{4+5h}{3\sqrt5}. \tag{23}
\]
If this branch is nonempty, then \(h>\mu>m(h)\).  From (12), the exact comparison
\[
\left(\frac{6\sqrt5-13}{4}-\frac{73}{1000}\right)^2
>\frac{6\sqrt5-13}{4}\cdot\frac{9-4\sqrt5}{6}
\]
shows \(m(h)>73/1000\).  Together with the upper bound already proved,
\[
\frac{73}{1000}<h<\frac{329}{1000}. \tag{24}
\]

For completeness, the following is an exact finite certificate that \(\Phi(h)>0\) throughout (24).  In a row let \([l,u]\) be the interval, and interpret \(c\) in units \(10^{-6}\), and \(m,n,s,y_0\) in units \(10^{-4}\).
\[
\begin{array}{c|c|r|r|r|r|r|r}
l&u&c&m&n&s&y_0&k\\ \hline
73/1000&1/10&490755&731&9038&730&8549&191435\\
1/10&1/8&490711&730&9036&854&7641&127051\\
1/8&3/20&490722&730&9036&955&6976&81186\\
3/20&9/50&490892&736&9045&1050&6394&39309\\
9/50&19/100&491390&754&9072&1164&6299&40616\\
19/100&1/5&491632&763&9085&1204&6176&32211\\
1/5&21/100&491916&774&9100&1244&6071&24880\\
21/100&11/50&492241&786&9119&1284&5977&18402\\
11/50&23/100&492611&800&9140&1326&5897&12949\\
23/100&6/25&493026&816&9164&1369&5830&8424\\
6/25&1/4&493489&835&9193&1415&5779&5290\\
1/4&13/50&494001&856&9225&1462&5737&2877\\
13/50&27/100&494565&880&9262&1512&5708&1699\\
27/100&7/25&495182&907&9305&1564&5691&1681\\
7/25&29/100&495854&937&9356&1619&5684&2971\\
29/100&3/10&496585&973&9415&1679&5695&6144\\
3/10&31/100&497377&1014&9487&1744&5719&11338\\
31/100&8/25&498231&1063&9579&1815&5763&19500\\
8/25&329/1000&499152&1128&9708&1899&5855&34687
\end{array} \tag{25}
\]
Here is the literal verification rule for the table.  For every row,
\[
C_*(h)>\frac c{10^6},qquad
m(h)>\frac m{10^4},qquad
n(h)>\frac n{10^4}, \tag{26}
\]
\[
\sqrt{\frac m{10^4}l}>\frac s{10^4},qquad
\sqrt{\frac{m/10^4}{u}}>\frac{y_0}{10^4}, \tag{27}
\]
and
\[
\frac s{10^4}
+\frac{n/10^4}{2-y_0/10^4}
-\frac{(4+5u)250}{1677}
>\frac{k}{10^6}>0. \tag{28}
\]
All quantities in (26)--(28) are rational after the indicated squarings.  To audit (26), use the derivative of \(C_*\), the unique minimum (12), and
\[
\frac{2236067977}{10^9}<\sqrt5<\frac{1118033989}{500000000};
\]
then use
\((A_i-m/10^4)^2>A_iE_i\) and
\((1-n/10^4)^2>E_i\), where
\[
A_i=\frac94\frac c{10^6}-1,qquad E_i=\frac12-\frac c{10^6}.
\]
Equations (27)--(28) are direct integer cross-multiplications; the weaker bound \(\sqrt5>559/250\) gives the last term in (28).  Thus (25) is an entirely rational interval certificate, not a numerical optimization.  From (26)--(28), for \(h\in[l,u]\),
\[
\Phi(h)>
\frac s{10^4}
+\frac{n/10^4}{2-y_0/10^4}
-\frac{(4+5u)250}{1677}>0.
\]
The rows cover (24), so \(\Phi(h)>0\) everywhere there.  Equations (22)--(23) prove \(G_\eta(x)>0\).

Accepted fact `83ae76262528a9f8` proves pointwise that a third endpoint contribution strictly below \(\eta\) would imply \(G_\eta(x)<0\) at the actual normalization.  This contradicts the preceding positivity, so the third row cannot be strict on a mixed or quadratic branch.

Finally, if a middle entry is zero, accepted fact `6986d9aa136ba907` perturbs only the first two middle rows while leaving \(U,V,A,B,t\), the third row \((p,-a,-b)\), and hence \(x,h,\mu,\nu,G_\eta(x)\), unchanged.  It preserves all three strict literal row masses and enters one fixed all-nine-nonzero contained chamber.  The open-chamber contradiction therefore excludes every zero-entry boundary stratum as well.  Accepted fact `27ae487131bcd122` already excludes \(B\leq1\), including its boundary cases.

## External sources

none
