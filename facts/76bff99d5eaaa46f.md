---
fact_id: 76bff99d5eaaa46f
kind: lemma
author: "r118-triangle-chamber"
assurance: LLM-verified
subgoal_id: triangle-chamber-one-two
depends_on: ["09393c6edf1fc4e2","64760c76cadff481","f8e871d10dac1791"]
source_packet_sha256: 9528256f8566e8e3c6839707ac95e69441dc0974da8798fd926138f9f1e3f234
verifier_run: 3601d980edb34db4
target_match: null
---

## Statement

Let
\[
\Delta=\operatorname{conv}\{e_1,e_2,e_3\},\qquad
\mathcal C(z;\tau)=\left|\{\lambda\in\Delta:z\cdot\lambda\geq\tau\}\right|,
\]
with \(|\Delta|=1\).  Suppose \(U,V,L\in\mathbb R^{3\times3}\) and \(\sigma=(\sigma_1,\sigma_2,\sigma_3)^\top\) satisfy the full exact \(N=3\) system of accepted facts `64760c76cadff481` and `09393c6edf1fc4e2`:
\[
\mathbf1^\top U=\mathbf1^\top V=\mathbf1^\top L=\mathbf1^\top,
\qquad \det U\det V\det L\ne0,
\]
\[
\min_jU_{ij}+\min_jV_{ij}\geq0\quad(i=1,2,3).
\]
Put
\[
A=|\det U|,\qquad B=|\det V|,\qquad
t=\frac{2(1+A+B)}9.
\]
After the lossless endpoint exchange of `09393c6edf1fc4e2`, assume
\[
0<A<B,\qquad q:=\sigma_1+\sigma_2+\sigma_3>1,\qquad 1+A<2B,
\]
and the strict residual strip of `64760c76cadff481`: with \(\rho=A/B\) and \(\eta=1/B\),
\[
0<\rho<\frac{27-2\sqrt{26}}{25},\qquad L_0(\rho)<\eta<U_0(\rho),
\]
where
\[
L_0(\rho)=
\begin{cases}
1-\rho,&0<\rho\leq9/25,\\
(3\rho+2\sqrt\rho-1)/2,&9/25<\rho,
\end{cases}
\quad
U_0(\rho)=
\begin{cases}
1+\rho,&0<\rho\leq1/2,\\
2-\rho,&1/2<\rho.
\end{cases}
\]
Define the transformed triangles and their centroids by
\[
P_0=LU\Delta+\sigma,\qquad P_1=L\Delta,\qquad
P_2=LV\Delta-\sigma,\qquad g_k=\operatorname{centroid}(P_k).
\]
Assume
\[
t\leq\frac12,\qquad
\{i:(g_0)_i\geq0\}=\{1,2\},\qquad
\{i:(g_1)_i\geq0\}=\{3\},
\]
and, with \(J_i=\{j:L_{ij}>0\}\), assume the open chamber
\[
J_1=\{2\},\qquad J_2=\{1,3\},\qquad J_3=\{1\}.
\]
Then the three strict full row inequalities
\[
\mathcal C(L_{i*};0)
+A\mathcal C((LU)_{i*};-\sigma_i)
+B\mathcal C((LV)_{i*};\sigma_i)<t
\qquad(i=1,2,3)
\]
cannot hold simultaneously.

## Proof

Assume that a full compatible witness exists.  Accepted fact `09393c6edf1fc4e2` identifies the displayed data with nondegenerate compatible triangles \(P_0,P_1,P_2\), preserves every independent shift, and guarantees that this is a genuine three-row system.  In the stated incidence orbit with \(t\leq1/2\), accepted fact `f8e871d10dac1791` gives
\[
c_1,c_2<\kappa:=\frac{2(1+B-A)}9<\frac49,
\qquad c_3<t\leq\frac12,
\tag{1}
\]
where \(c_i=\mathcal C(L_{i*};0)\), and it gives strictly negative sums for rows \(1,2\).  (It also gives the stronger third-row mean used in its chamber reduction, but that strengthening will not be needed.)

The open signs allow the unique parametrization
\[
L=
\begin{pmatrix}
-\alpha&\beta&-\gamma\\
u&-\varphi&v\\
p&-a&-b
\end{pmatrix},
\qquad
\alpha,\beta,\gamma,u,\varphi,v,p,a,b>0.
\tag{2}
\]
The column-sum identity \(\mathbf1^\top L=\mathbf1^\top\) is exactly
\[
\alpha=p+u-1,\qquad
\beta=a+\varphi+1,\qquad
\gamma=v-b-1.
\tag{3}
\]
The exact one-positive and two-positive cap formulas of accepted fact `64760c76cadff481` give
\[
c_1=\frac{\beta^2}{(\alpha+\beta)(\beta+\gamma)},
\qquad
c_2=1-\frac{\varphi^2}{(\varphi+u)(\varphi+v)},
\qquad
c_3=\frac{p^2}{(p+a)(p+b)}.
\tag{4}
\]
Thus there is no unresolved ordering choice in any middle cap.

We prove the stronger algebraic implication
\[
c_2\leq\frac49,\quad c_3\leq\frac12
\quad\Longrightarrow\quad c_1>\frac49
\tag{5}
\]
under (2), (3), and the two strictly negative row sums.

Set
\[
x=\frac{u}{\varphi},\qquad y=\frac{v}{\varphi},
\qquad d=1-x-y.
\]
The negative second-row sum gives \(d>0\), and the second formula in (4) together with \(c_2\leq4/9\) gives
\[
(1+x)(1+y)\leq\frac95,\qquad
d=1-x-y\geq\frac15+xy>\frac15.
\tag{6}
\]
Put
\[
h=p-a-b,\qquad E=\frac h\varphi.
\]
The negative first-row sum is \(\beta<\alpha+\gamma\).  Substitution from (3) gives the exact strict comparison
\[
h>\varphi-u-v+3=\varphi d+3,
\qquad E>d+\frac3\varphi>\frac15.
\tag{7}
\]
In particular \(h>0\).  Define
\[
\mu=\frac ah,\qquad \nu=\frac bh.
\]
Then \(p=h(1+\mu+\nu)\).  The third formula in (4) and \(c_3\leq1/2\) imply
\[
2(1+\mu+\nu)^2
\leq(1+2\mu+\nu)(1+\mu+2\nu),
\]
or equivalently
\[
\mu\nu\geq1+\mu+\nu.
\tag{8}
\]
Consequently \(\mu>1\), \(\nu>1\), and
\[
\mu\geq\mu_0:=\frac{\nu+1}{\nu-1}.
\tag{9}
\]

The numerator in the first formula of (4) is \((a+\varphi+1)^2>(a+\varphi)^2\), whereas its two denominators, by (3), are
\[
\alpha+\beta=p+u+a+\varphi,\qquad
\beta+\gamma=a+\varphi+v-b.
\]
It is therefore enough to prove
\[
\widetilde c_1:=
\frac{(a+\varphi)^2}
{(p+u+a+\varphi)(a+\varphi+v-b)}
>\frac49.
\tag{10}
\]
Using \(a=\varphi E\mu\), \(b=\varphi E\nu\), and
\(p=\varphi E(1+\mu+\nu)\), write the denominator of (10) as
\[
\varphi^2(C+x)(D+y),
\quad
C=1+E(2\mu+\nu+1),
\quad
D=1+E(\mu-\nu).
\tag{11}
\]
Let \(s=x+y\).  For fixed \(s\), differentiation of the product in (11) gives
\[
\frac{d}{dx}(C+x)(D+s-x)
=s-E(\mu+2\nu+1)-2x<0,
\tag{12}
\]
because (6) gives \(s<4/5\), while (7)-(8) give
\(E>1/5\) and \(\mu+2\nu+1>4\).  Hence, using again \(s<4/5\),
\[
(C+x)(D+y)
<C\left(D+\frac45\right)
=\bigl(1+E(2\mu+\nu+1)\bigr)
 \left(\frac95+E(\mu-\nu)\right).
\tag{13}
\]
The last factor is positive because it is strictly larger than the positive factor \(D+y\) occurring in (11).

It remains to compare the right side of (13) with the numerator in (10).  Define
\[
Q(E,\mu,\nu)
=9(1+E\mu)^2
-4\bigl(1+E(2\mu+\nu+1)\bigr)
 \left(\frac95+E(\mu-\nu)\right).
\tag{14}
\]
Direct differentiation gives
\[
\frac{\partial Q}{\partial\mu}
=\frac{2E}{5}\bigl(5E\mu+10E\nu-10E-1\bigr)
=\frac{2E}{5}\bigl(5E(\mu+2\nu-2)-1\bigr)>0.
\tag{15}
\]
Thus (9) gives
\[
Q(E,\mu,\nu)\geq Q(E,\mu_0,\nu)=:Q_0(E,\nu).
\tag{16}
\]
The following three exact identities certify that \(Q_0(E,\nu)>0\) for \(E>1/5\), \(\nu>1\):
\[
Q_0\left(\frac15,\nu\right)
=\frac{4(\nu^2-2\nu+2)^2}{25(\nu-1)^2}>0,
\tag{17}
\]
\[
\left.\frac{\partial Q_0}{\partial E}\right|_{E=1/5}
=\frac{4H(\nu)}{5(\nu-1)^2},
\qquad
\frac{\partial^2 Q_0}{\partial E^2}
=\frac{2(\nu+1)^2\bigl(4(\nu-1)^2+1\bigr)}{(\nu-1)^2}>0,
\tag{18}
\]
where, for \(r=\nu-1>0\),
\[
H(\nu)=2r^4+4r^3-5r^2+r+2>0.
\tag{19}
\]
For \(0<r\leq1\), the last positivity has the exact Bernstein certificate
\[
H(\nu)=2(1-r)^4+9r(1-r)^3+10r^2(1-r)^2
+5r^3(1-r)+4r^4>0;
\]
for \(r\geq1\), it follows from
\[
H(\nu)=r^2(2r^2+4r-5)+r+2>0.
\]
Equations (17)-(19) show that \(Q_0\) is already positive at \(E=1/5\), has positive derivative there, and has positive second derivative thereafter.  Hence (7), (16) give
\[
Q(E,\mu,\nu)>0.
\tag{20}
\]

Combining (13), (14), and (20) yields
\[
4(C+x)(D+y)<9(1+E\mu)^2.
\]
This is exactly \(\widetilde c_1>4/9\), so (10) proves (5).  But (1) has \(c_2<4/9\), \(c_3<1/2\), and \(c_1<4/9\), contradicting (5).

The contradiction began with an arbitrary full \((U,V,L,\sigma)\) witness.  No endpoint cap was divided by or assumed positive, and no relation among the three shifts beyond the accepted normal form was imposed.  Therefore zero endpoint demands, every endpoint cap-order or repeated-value stratum, both determinant signs of \(U,V,L\), and all independent shifts are included.  Equality \(t=1/2\) is also included because the full third row is strict, so \(c_3<t=1/2\); the algebraic implication (5) itself permits the weak cap boundaries.  Thus the entire stated open chamber is eliminated from the complete \(N=3\) matrix system.

## External sources

none
