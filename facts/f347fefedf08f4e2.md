---
fact_id: f347fefedf08f4e2
kind: lemma
author: "mp_r254_joint_chain_global"
assurance: LLM-verified
subgoal_id: indexed-chain-common-coupling-duality
depends_on: ["a2a1f8532c91018f"]
source_packet_sha256: 1505ae2421b1f0362624e05dcbf59164dd34ef191eab428f55a62cde7d1ffc6f
verifier_run: 327a50e8f2254c33
target_match: null
---

## Statement

Let \(A_0,A_2\subset\mathbb R^2\) be compact two-dimensional convex bodies,
write
\[
M=|A_0|\ge |A_2|=m>0,
\]
and let \(\mu_0,\mu_2\) be planar Lebesgue measure restricted to
\(A_0,A_2\), respectively.  Define
\[
\Pi_m=
\left\{\pi\ge0:
\begin{array}{l}
\pi\text{ is a finite Borel measure on }A_0\times A_2,\\
\pi(A_0\times A_2)=m,\quad
\pi_0\le\mu_0,\quad
\pi_2=\mu_2
\end{array}
\right\}.
\tag{1}
\]
For an affine function \(f:\mathbb R^2\to\mathbb R\), put
\[
E_f=
\left\{(x_0,x_2)\in A_0\times A_2:
f\left(\frac{x_0+x_2}{2}\right)<0
\right\}
\tag{2}
\]
and
\[
\tau(E_f)=
\inf\left\{
|U|+|V|:
\begin{array}{l}
U\subseteq A_0,\ V\subseteq A_2\text{ are measurable},\\
E_f\subseteq(U\times A_2)\cup(A_0\times V)
\end{array}
\right\}.
\tag{3}
\]
Then
\[
\boxed{\tau(E_f)=\sup_{\pi\in\Pi_m}\pi(E_f).}
\tag{4}
\]
For a constant \(f\equiv c\), the two sides of (4) are both \(m\) if
\(c<0\), and both zero if \(c\ge0\).  Thus (4) includes the strict-graph
case \(f\equiv0\), although the closed-cap quantity in accepted fact
`a2a1f8532c91018f` has a different value there.

Now let \(A_1\subset\mathbb R^2\) be a compact two-dimensional convex body
satisfying
\[
\frac{A_0+A_2}{2}\subseteq A_1,
\]
and let affine functions \(f_1,f_2,f_3\) satisfy
\[
f_1+f_2+f_3=-1.
\]
Define
\[
B_i=A_1\cap\{f_i\le0\},\qquad b_i=|B_i|,\qquad E_i=E_{f_i}.
\tag{5}
\]
Then
\[
\boxed{
\max_i\bigl(b_i+\tau(E_i)\bigr)
=
\sup_{\pi\in\Pi_m}
\max_i\bigl(b_i+\pi(E_i)\bigr).}
\tag{6}
\]
If
\[
\Delta_3=\{\lambda\in\mathbb R_+^3:\lambda_1+\lambda_2+\lambda_3=1\},
\]
then the same number also equals
\[
\boxed{
\sup_{\lambda\in\Delta_3}
\left[
\sum_{i=1}^3\lambda_i b_i+
\sup_{\pi\in\Pi_m}
\int_{A_0\times A_2}
\sum_{i=1}^3\lambda_i\mathbf1_{E_i}\,d\pi
\right].}
\tag{7}
\]
Finally, put
\[
N=\sum_{i=1}^3\mathbf1_{E_i},
\qquad
\Gamma=\sup_{\pi\in\Pi_m}\int_{A_0\times A_2}N\,d\pi.
\tag{8}
\]
Then \(N\ge1\) pointwise, \(\Gamma\ge m\), and
\[
\boxed{
\max_i\bigl(b_i+\tau(E_i)\bigr)
\ge
\frac{\sum_i b_i+\Gamma}{3}.}
\tag{9}
\]

## Proof

First, \(\Pi_m\) is nonempty.  Indeed,
\[
\pi^\circ=\frac1M\,\mu_0\otimes\mu_2
\]
has total mass \(m\), second marginal \(\mu_2\), and first marginal
\((m/M)\mu_0\le\mu_0\).

We prove the upper bound in (4) for an arbitrary affine \(f\).  Fix
\(\pi\in\Pi_m\) and a measurable vertex cover in (3).  Then
\[
\begin{aligned}
\pi(E_f)
&\le
\pi(U\times A_2)+\pi(A_0\times V)\\
&=\pi_0(U)+\pi_2(V)\\
&\le\mu_0(U)+\mu_2(V)
=|U|+|V|.
\end{aligned}
\tag{10}
\]
Taking the infimum over covers and then the supremum over \(\pi\) gives
\[
\sup_{\pi\in\Pi_m}\pi(E_f)\le\tau(E_f).
\tag{11}
\]

Suppose next that \(f\) is nonconstant.  Define the finite pushforward
measures
\[
\alpha=f_\#\mu_0,\qquad \beta=f_\#\mu_2
\]
on \(\mathbb R\), with distribution functions
\[
F_0(s)=\alpha((-\infty,s]),\qquad
F_2(s)=\beta((-\infty,s]).
\tag{12}
\]
Every level set of \(f\) is a line, so it has planar area zero in either
endpoint body.  Hence \(\alpha,\beta\) are atomless and \(F_0,F_2\) are
continuous.  Accepted fact `a2a1f8532c91018f` gives
\[
\tau(E_f)=
\kappa:=
\inf_{s\in\mathbb R}
\bigl(F_0(s)+F_2(-s)\bigr).
\tag{13}
\]
Sending \(s\) to \(-\infty\) in (13) shows \(\kappa\le m\).
If \(\kappa=0\), (11) already proves (4), so assume \(\kappa>0\).

Fix \(q\) with
\[
0<q<\kappa.
\tag{14}
\]
For \(0<u<M\) and \(0<v<m\), define the lower quantile functions
\[
Q_0(u)=\inf\{s:F_0(s)\ge u\},\qquad
Q_2(v)=\inf\{s:F_2(s)\ge v\}.
\tag{15}
\]
Continuity and the endpoint limits of the two distribution functions give
\[
F_0(Q_0(u))=u,\qquad F_2(Q_2(v))=v.
\tag{16}
\]
For \(0<u<q\), use \(s=Q_0(u)\) in (13).  Equations (13), (14), and (16)
give
\[
F_2(-Q_0(u))>q-u.
\tag{17}
\]
Since \(F_2\) is continuous, (17) implies the strict quantile inequality
\[
Q_2(q-u)<-Q_0(u).
\tag{18}
\]
Thus
\[
Q_0(u)+Q_2(q-u)<0
\qquad(0<u<q).
\tag{19}
\]

We now lift this one-dimensional matching measurably to the endpoint
bodies.  Since the endpoint bodies and \(\mathbb R\) are standard Borel
spaces, there are probability kernels \(K_0(s,\cdot)\) and
\(K_2(t,\cdot)\) which disintegrate \(\mu_0,\mu_2\) over \(f\):
\[
\mu_0(C)=\int K_0(s,C)\,d\alpha(s),\qquad
\mu_2(D)=\int K_2(t,D)\,d\beta(t),
\tag{20}
\]
and, for pushforward-almost every parameter,
\[
K_0(s,\{x_0:f(x_0)=s\})=1,\qquad
K_2(t,\{x_2:f(x_2)=t\})=1.
\tag{21}
\]
Define a finite Borel measure \(\gamma_q\) on \(A_0\times A_2\) by
\[
\gamma_q(C\times D)
=
\int_0^q
K_0(Q_0(u),C)\,
K_2(Q_2(q-u),D)\,du,
\tag{22}
\]
first on measurable rectangles and then by the associated kernel product
measure.  Its total mass is \(q\).

The first marginal in (22) is the lift of the lower \(q\)-quantile
submeasure of \(\alpha\), while its second marginal is the lift of the
lower \(q\)-quantile submeasure of \(\beta\).  More explicitly, the
pushforward of Lebesgue measure on \((0,q)\) by \(Q_0\) is the restriction
of \(\alpha\) to its lowest \(q\) units of mass, and the map
\(u\mapsto q-u\) preserves Lebesgue measure on \((0,q)\); hence
\[
\gamma_{q,0}\le\mu_0,\qquad
\gamma_{q,2}\le\mu_2.
\tag{23}
\]
Because these two quantile pushforwards are dominated by
\(\alpha,\beta\), respectively, the exceptional parameter sets on which
the disintegration identities (21) need not hold have zero
Lebesgue measure in (22).
Equations (19), (21), and (22) give
\[
f(x_0)+f(x_2)<0
\quad\text{for }\gamma_q\text{-almost every }(x_0,x_2).
\tag{24}
\]
Affineness gives
\[
f(x_0)+f(x_2)
=2f\left(\frac{x_0+x_2}{2}\right),
\]
so (24) says that \(\gamma_q\) is supported on \(E_f\).

It remains to complete this \(q\)-subcoupling to an element of \(\Pi_m\).
Because \(q<\kappa\le m\), put
\[
\eta_0=
\frac{m-q}{M-q}\bigl(\mu_0-\gamma_{q,0}\bigr),
\qquad
\eta_2=\mu_2-\gamma_{q,2}.
\tag{25}
\]
Both measures in (25) have mass \(m-q\), and
\[
0<\frac{m-q}{M-q}\le1.
\tag{26}
\]
Their normalized product coupling is
\[
\rho_q=\frac1{m-q}\,\eta_0\otimes\eta_2.
\tag{27}
\]
Set
\[
\pi_q=\gamma_q+\rho_q.
\tag{28}
\]
Its total mass is \(m\), and its second marginal is
\[
\gamma_{q,2}+\eta_2=\mu_2.
\tag{29}
\]
Its first marginal satisfies
\[
\begin{aligned}
\gamma_{q,0}+\eta_0
&=
\gamma_{q,0}
+\frac{m-q}{M-q}(\mu_0-\gamma_{q,0})\\
&\le\gamma_{q,0}+(\mu_0-\gamma_{q,0})
=\mu_0.
\end{aligned}
\tag{30}
\]
Therefore \(\pi_q\in\Pi_m\).  Since \(\gamma_q\) is supported on \(E_f\),
\[
\pi_q(E_f)\ge q.
\tag{31}
\]
Letting \(q\uparrow\kappa\), without asserting attainment at
\(q=\kappa\), gives
\[
\sup_{\pi\in\Pi_m}\pi(E_f)\ge\kappa=\tau(E_f).
\tag{32}
\]
Together with (11), this proves (4) for every nonconstant affine \(f\).

If \(f\equiv c<0\), then \(E_f=A_0\times A_2\).  Every
\(\pi\in\Pi_m\) assigns it mass \(m\), and accepted fact
`a2a1f8532c91018f` gives \(\tau(E_f)=m\).  If \(f\equiv c\ge0\), strictness
in (2) gives \(E_f=\varnothing\), so every coupling assigns it mass zero;
the same accepted fact gives \(\tau(E_f)=0\), including \(c=0\).
This proves (4) in every constant case.

We turn to the three-index formulas.  For \(i=1,2,3\), equation (4) gives
\[
b_i+\tau(E_i)
=\sup_{\pi\in\Pi_m}\bigl(b_i+\pi(E_i)\bigr).
\tag{33}
\]
For any finite family of real-valued functions \(g_i\) on a nonempty set,
\[
\max_i\sup_\pi g_i(\pi)
=\sup_\pi\max_i g_i(\pi).
\tag{34}
\]
Indeed, the right side is at least each individual supremum, while every
\(g_i(\pi)\) is at most the maximum of those individual suprema.  Applying
(34) to \(g_i(\pi)=b_i+\pi(E_i)\) proves (6), with no attainment
assumption.

For every \(z\in\mathbb R^3\),
\[
\max_i z_i
=\sup_{\lambda\in\Delta_3}\sum_i\lambda_i z_i.
\tag{35}
\]
Use (35) inside (6).  Suprema over the Cartesian product
\(\Pi_m\times\Delta_3\) commute, regardless of attainment, so
\[
\begin{aligned}
\sup_{\pi\in\Pi_m}\max_i\bigl(b_i+\pi(E_i)\bigr)
&=
\sup_{\pi\in\Pi_m}\sup_{\lambda\in\Delta_3}
\sum_i\lambda_i\bigl(b_i+\pi(E_i)\bigr)\\
&=
\sup_{\lambda\in\Delta_3}
\left[
\sum_i\lambda_i b_i+
\sup_{\pi\in\Pi_m}
\int\sum_i\lambda_i\mathbf1_{E_i}\,d\pi
\right].
\end{aligned}
\tag{36}
\]
This is (7).

Finally, for every \((x_0,x_2)\in A_0\times A_2\),
\[
\sum_{i=1}^3
f_i\left(\frac{x_0+x_2}{2}\right)=-1.
\]
At least one summand is strictly negative.  Hence the three \(E_i\) cover
the whole product and \(N\ge1\) pointwise.  Every \(\pi\in\Pi_m\) has mass
\(m\), so
\[
\int N\,d\pi\ge m,\qquad\Gamma\ge m.
\tag{37}
\]
Taking \(\lambda_i=1/3\) in (7) gives
\[
\begin{aligned}
\max_i\bigl(b_i+\tau(E_i)\bigr)
&\ge
\frac13\sum_i b_i+
\frac13\sup_{\pi\in\Pi_m}\int N\,d\pi\\
&=
\frac{\sum_i b_i+\Gamma}{3},
\end{aligned}
\]
which is (9).

## External sources

none
