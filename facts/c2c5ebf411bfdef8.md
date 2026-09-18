---
fact_id: c2c5ebf411bfdef8
kind: lemma
author: "mp_r17_support_clearance"
assurance: LLM-verified
subgoal_id: minkowski-support-clearance
depends_on: ["15bb2c1680a0254e","756b87a16a89ea8f","c415ce7703455561","f8a1649f7072dce1"]
source_packet_sha256: 563100ef3190a328385661913e7121df6c8bad4ddde5da4c59a9f39ed59942d0
verifier_run: b82011e049ca4cc3
target_match: null
---

## Statement

Let \(A_0,A_2\subset\mathbb R^2\) be nonempty two-dimensional convex bodies, with
\[
M=|A_0|\ge |A_2|=m>0,\qquad
B=\frac{A_0+A_2}{2},\qquad b=|B|,
\]
and let \(g_B\) be the centroid of \(B\). Fix \(q\in\mathbb S^1\). For \(i=0,2\), write
\[
\ell_i=\min_{z\in A_i}\langle q,z\rangle,\qquad
w_i=\max_{z\in A_i}\langle q,z\rangle-\ell_i.
\]
Then
\[
\ell_B=\frac{\ell_0+\ell_2}{2},\qquad
w_B=\frac{w_0+w_2}{2}.
\]
Define the signed lower-support clearance
\[
\delta_q=\langle q,g_B\rangle-\ell_B>0.
\]
For \(\lambda\in\mathbb R\), let
\[
x_\lambda=
\left|
A_0\cap
\{\langle q,z-g_B\rangle\le\lambda\}
\right|,
\qquad
y_\lambda=
\left|
A_2\cap
\{\langle q,z-g_B\rangle\le-\lambda\}
\right|.
\]
Then
\[
x_\lambda+y_\lambda
\ge
\min\left\{
m,\,
\frac{4\delta_q^2Mm}{mw_0^2+Mw_2^2}
\right\}.
\tag{1}
\]
This bound is attained when \(A_0=A_2\) is a triangle whose section density in direction \(q\) increases linearly from the lower support, and \(\lambda=0\).

If \(x_\lambda=0\), then the sharper empty-cap estimate is
\[
y_\lambda
\ge
m\min\left\{
1,\left(\frac{2\delta_q}{w_2}\right)^2
\right\}.
\tag{2}
\]
The symmetric assertion holds with \(0\) and \(2\) exchanged.

Moreover,
\[
\delta_q\ge\frac{w_0+w_2}{6}.
\tag{3}
\]
Consequently, with
\[
r=\frac mM,\qquad
\theta_q=\frac{w_0}{w_2},
\]
equation (1) gives
\[
\frac{x_\lambda+y_\lambda}{M}
\ge
\Psi_r(\theta_q)
:=
\min\left\{
r,\,
\frac{r(1+\theta_q)^2}
{9(1+r\theta_q^2)}
\right\}
\ge\frac r9.
\tag{4}
\]
The identity \(B=(A_0+A_2)/2\) also gives the mixed-area width restriction
\[
4b\ge
M+m+\frac{M}{\theta_q}+m\theta_q.
\tag{5}
\]
Thus, with \(s=b/M\), \(C=4s-1-r\), and
\[
\theta_\pm=
\frac{C\pm\sqrt{C^2-4r}}{2r},
\]
one has
\[
\theta_-\le\theta_q\le\theta_+,
\qquad
\Psi_r(\theta_q)\ge
\underline\Psi(r,s):=
\min\{\Psi_r(\theta_-),\Psi_r(\theta_+)\}.
\tag{6}
\]

Now suppose \(A_0,A_2\) are polytopes and set
\[
S=(\{0\}\times A_0)\cup(\{1\}\times B)\cup(\{2\}\times A_2).
\]
Define
\[
H(r,s)=
\max\left\{
0,\,
r-
\left(
\max\left\{0,\,2\sqrt{\frac{5s}{9}}-1\right\}
\right)^2
\right\}.
\]
Then
\[
h_S((1,g_B))
\ge
M\min\left\{
1+s,\,
s+r,\,
\frac{4s}{9}
+\max\{H(r,s),\underline\Psi(r,s)\}
\right\}.
\tag{7}
\]
In particular,
\[
b\ge M+\frac m2
\quad\Longrightarrow\quad
h_S((1,g_B))\ge\frac{2(M+b+m)}9.
\tag{8}
\]

The implication (8) covers a nonempty part of the residual area domain in accepted fact `15bb2c1680a0254e` that is not certified by accepted fact `f8a1649f7072dce1`. One exact point is
\[
M=1,\qquad m=\frac25,\qquad b=\frac65.
\tag{9}
\]

## Proof

Accepted fact `756b87a16a89ea8f` gives the section description used below: after translating a lower projection support to \(0\), the section-length function of a planar convex body is nonnegative and concave on its projection interval, its integral is the area, and its cumulative integral is the corresponding cap area.

We first record two one-dimensional consequences. Let \(f\) be a nonzero nonnegative concave function on \([0,w]\), let
\[
A=\int_0^w f(t)\,dt,\qquad
\mu=\frac1A\int_0^w t f(t)\,dt,
\]
and let
\[
F(z)=\int_0^z f(t)\,dt
\]
for \(0\le z\le w\). Rescale the probability density \(f/A\) by its mean:
\[
h(u)=\frac{\mu}{A}f(\mu u),
\qquad
0\le u\le L:=\frac w\mu.
\]
Then \(h\) is a nonnegative concave probability density with mean \(1\). Accepted fact `c415ce7703455561` gives
\[
\frac32\le L\le3,
\]
and therefore
\[
\frac w3\le\mu\le\frac{2w}{3}.
\tag{10}
\]

The same accepted tent decomposition gives
\[
\frac{F(z)}A\ge\left(\frac zw\right)^2.
\tag{11}
\]
Indeed, for a common-support tent \(h_{L,\tau}\), write \(P_{L,\tau}(t)=1-Q_{L,\tau}(t)\) for its lower cumulative mass. If \(0\le t\le\tau\), then
\[
P_{L,\tau}(t)=\frac{t^2}{L\tau}\ge\frac{t^2}{L^2}.
\]
If \(\tau\le t\le L\), then
\[
P_{L,\tau}(t)
=
1-\frac{(L-t)^2}{L(L-\tau)}
\ge\frac tL
\ge\frac{t^2}{L^2}.
\]
Integrating over the tent mixture and undoing the rescaling proves (11). The inequality is sharp for the increasing triangular density \(f(t)=2At/w^2\).

Apply (10) to the section density of \(B\). Its mean measured from its lower support is exactly \(\delta_q\). Since its width is
\[
w_B=\frac{w_0+w_2}{2},
\]
equation (10) proves (3).

Put
\[
u=\frac{\langle q,g_B\rangle+\lambda-\ell_0}{w_0},
\qquad
v=\frac{\langle q,g_B\rangle-\lambda-\ell_2}{w_2}.
\]
The support identity gives
\[
w_0u+w_2v=2\delta_q.
\tag{12}
\]
Define
\[
\varphi(t)=
\begin{cases}
0,&t\le0,\\
t^2,&0\le t\le1,\\
1,&t\ge1.
\end{cases}
\]
Equation (11), including empty and saturated thresholds, gives
\[
x_\lambda\ge M\varphi(u),
\qquad
y_\lambda\ge m\varphi(v).
\tag{13}
\]

If \(u\ge1\) or \(v\ge1\), the right side of (13) is at least \(M\) or \(m\), respectively, and hence at least \(m\). Suppose instead that \(u<1\) and \(v<1\). With \(u_+=\max\{u,0\}\) and \(v_+=\max\{v,0\}\), equation (12) implies
\[
w_0u_++w_2v_+\ge2\delta_q.
\]
Weighted Cauchy-Schwarz gives
\[
Mu_+^2+mv_+^2
\ge
\frac{(w_0u_++w_2v_+)^2}
{w_0^2/M+w_2^2/m}
\ge
\frac{4\delta_q^2Mm}
{mw_0^2+Mw_2^2}.
\]
Together with the saturated case, this proves (1).

If \(x_\lambda=0\), two-dimensionality and positivity of the section density on the interior of its support force \(u\le0\). Equation (12) then gives
\[
v\ge\frac{2\delta_q}{w_2}.
\]
Equations (11) and (13) prove (2). Combining (1) with (3), and then dividing by \(M\), proves the first inequality in (4). Finally,
\[
(1+\theta)^2-(1+r\theta^2)
=
2\theta+(1-r)\theta^2\ge0,
\]
so both entries in the minimum defining \(\Psi_r\) are at least \(r/9\). This proves the last inequality in (4).

To verify sharpness of (1), take \(A_0=A_2=K\), where the section density of \(K\) is
\[
f(t)=\frac{2|K|}{w^2}t,\qquad 0\le t\le w.
\]
Then \(B=K\), \(\delta_q=2w/3\), and for \(\lambda=0\) each outer cap has area \(4|K|/9\). Thus both sides of (1) equal \(8|K|/9\).

We next prove (5) directly from sections. Translate the two lower supports to \(0\), and let \(f_0,f_2,f_B\) be the section lengths. For \(0\le t\le1\), the average of the sections at \(w_0t\) and \(w_2t\) is contained in the section of \(B\) at \(w_Bt\). Hence
\[
f_B(w_Bt)
\ge
\frac{f_0(w_0t)+f_2(w_2t)}2.
\]
Integration gives
\[
b
\ge
\frac{w_B}{2}
\left(\frac{M}{w_0}+\frac{m}{w_2}\right)
=
\frac14
\left(
M+m+\frac{M}{\theta_q}+m\theta_q
\right),
\]
which is (5). Aligned rectangles attain equality.

After normalization, (5) becomes
\[
r\theta_q^2-C\theta_q+1\le0.
\]
It implies \(C^2\ge4r\) and \(\theta_q\in[\theta_-,\theta_+]\). Before truncation at \(r\), the derivative of
\[
\frac{r(1+\theta)^2}{9(1+r\theta^2)}
\]
has the sign of \(1-r\theta\). Thus \(\Psi_r\) is increasing and then decreasing, possibly with a flat truncated maximum, so its minimum on \([\theta_-,\theta_+]\) occurs at an endpoint. This proves (6).

For a tilted halfspace through \((1,g_B)\), let \(c\) be its middle cap area. Accepted fact `f8a1649f7072dce1` gives
\[
c\ge\frac{4b}{9}
\]
and, independently, the area-only lower bound
\[
c+x_\lambda+y_\lambda
\ge
M\left(\frac{4s}{9}+H(r,s)\right).
\]
Equations (4) and (6) give the second bound
\[
c+x_\lambda+y_\lambda
\ge
M\left(\frac{4s}{9}+\underline\Psi(r,s)\right).
\]
Every tilted halfspace therefore has mass at least
\[
M\left(
\frac{4s}{9}
+\max\{H(r,s),\underline\Psi(r,s)\}
\right).
\]
The two slice-parallel halfspaces through \((1,g_B)\) have masses \(M+b=M(1+s)\) and \(b+m=M(s+r)\). This proves (7).

The coarse last inequality in (4) gives every tilted halfspace mass at least
\[
\frac{4b+m}{9}.
\]
If \(b\ge M+m/2\), then
\[
4b+m\ge2(M+b+m).
\]
The slice-parallel masses also exceed the target: \(M+b\) does so because \(M\ge m\), while
\[
9(b+m)-2(M+b+m)=7b+7m-2M>0
\]
under \(b\ge M+m/2\). This proves (8).

It remains to verify that the advance is nonempty and genuinely exceeds the area-only envelope. At (9),
\[
r=\frac25,\qquad s=\frac65.
\]
Accepted fact `15bb2c1680a0254e` gives
\[
L(r)=\frac1{10}+\sqrt{\frac25}
<
\frac65
<
\frac75=U(r),
\]
so this point lies strictly in its residual area domain. Moreover,
\[
\frac{20s}{9}=\frac83
>
\left(1+\sqrt{\frac25}\right)^2,
\]
because
\[
\left(\frac{19}{15}\right)^2
>
\frac85.
\]
Thus the third branch of accepted fact `f8a1649f7072dce1` applies and yields only
\[
\frac{\Phi}{M}=\frac{4s}{9}=\frac8{15}
<
\frac{26}{45}
=
\frac{2(1+r+s)}9.
\]
The support-clearance term supplies
\[
\frac r9=\frac{2}{45},
\]
so (8) reaches the target exactly.

For an explicit compatible realization, take
\[
A_0=
\{(x,y):|x|\le1/2,\ |y|\le1/2\},
\]
and
\[
A_2=
\{(x,y):|x|\le1/2,\ |y-2x|\le1/5\}.
\]
These centrally symmetric parallelograms have areas \(1\) and \(2/5\). Their Minkowski sum is the zonotope generated by
\[
(1,0),\qquad (1,2),\qquad (0,7/5),
\]
and hence has area
\[
2+\frac75+\frac75=\frac{24}{5}.
\]
Therefore
\[
\left|\frac{A_0+A_2}{2}\right|=\frac65.
\]
The convex hull of \(\{0\}\times A_0\) and \(\{2\}\times A_2\) has these three integer slices, completing the realization.

## External sources

none
