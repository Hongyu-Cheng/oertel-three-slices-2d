---
fact_id: 5b75ecd9ec86dbcf
kind: theorem
author: "mp_r298_nonconcurrent_caps"
assurance: LLM-verified
subgoal_id: nonconcurrent-three-cap-inequality
depends_on: ["851e063a1b9908a3"]
source_packet_sha256: e05e20fd26fecbfca9ea8691eaf0f386f3021b3c243892e31b1d4312a8274738
verifier_run: cd2bb1f74e0a4c40
target_match: null
---

## Statement

Let \(K\subset\mathbb R^2\) be a compact convex body with nonempty interior, and let \(f_1,f_2,f_3\) be nonconstant pairwise nonparallel affine functions satisfying
\[
f_1+f_2+f_3=-1.
\]
Put
\[
H_i=\{x\in\mathbb R^2:f_i(x)\leq0\},\qquad
b_i=|K\cap H_i|,\qquad A=|K|.
\]
Then
\[
5(b_1+b_2+b_3)-6\min_i b_i\geq4A.
\]

For distinct \(i,j,k\in\{1,2,3\}\), let \(s_i\) be the area of
\[
K\cap H_i\cap\{f_j>0\}\cap\{f_k>0\},
\]
let \(d_i\) be the area of the opposite doubleton cell
\[
K\cap\{f_i>0\}\cap H_j\cap H_k,
\]
and let
\[
g=|K\cap H_1\cap H_2\cap H_3|.
\]
Then
\[
s_1+s_2+s_3+5g\geq6\min_i(s_i-d_i).
\]

## Proof

Write \(m=\min_i b_i\). Every level set of every \(f_i\) is a line and hence has planar measure zero.

First suppose \(m=0\). Since \(\sum_i f_i=-1\), at every point of \(\mathbb R^2\) at least one \(f_i\) is negative. Thus \(H_1\cup H_2\cup H_3=\mathbb R^2\), and the union bound gives
\[
A\leq b_1+b_2+b_3.
\]
Consequently
\[
5(b_1+b_2+b_3)-6m=5(b_1+b_2+b_3)\geq5A\geq4A.
\]
Henceforth assume \(m>0\).

For each \(i\), define the support endpoints and cap-area function
\[
\alpha_i=\min_{x\in K}f_i(x),\qquad
\beta_i=\max_{x\in K}f_i(x),\qquad
F_i(t)=|K\cap\{f_i\leq t\}|.
\]
The nonzero linear part of \(f_i\) and the nonempty interior of \(K\) imply \(\alpha_i<\beta_i\). The function \(F_i\) is continuous: if \(t_n\to t\), the indicators of \(\{f_i\leq t_n\}\) converge pointwise on \(K\setminus\{f_i=t\}\), and the exceptional level line is null, so dominated convergence applies.

Moreover, \(F_i\) is strictly increasing on \([\alpha_i,\beta_i]\). Indeed, for \(\alpha_i\leq s<t\leq\beta_i\), the open strip
\[
\operatorname{int}K\cap\{s<f_i<t\}
\]
is nonempty. To see this, choose a value strictly between \(s\) and \(t\); a segment from an interior point of \(K\) to a minimizer or maximizer of \(f_i\) supplies an interior point with that value. The strip is then a nonempty open set and has positive area. Also,
\[
F_i(\alpha_i)=0,\qquad F_i(\beta_i)=A,
\]
because the lower support set is contained in a line. Hence \(F_i|_{[\alpha_i,\beta_i]}\) is a continuous strictly increasing bijection onto \([0,A]\). Denote its continuous inverse by
\[
Q_i:[0,A]\longrightarrow[\alpha_i,\beta_i].
\]

For \(0\leq q\leq m\), set
\[
\tau_i(q)=Q_i(b_i-q).
\]
Then
\[
F_i(\tau_i(q))=b_i-q,
\]
and every \(\tau_i\) is continuous on the closed interval \([0,m]\). Since \(b_i>0\), one has \(\alpha_i<0\). If \(b_i<A\), then \(0<\beta_i\), strict increase gives \(Q_i(b_i)=0\), and therefore \(\tau_i(q)\leq0\). If \(b_i=A\), then \(\beta_i\leq0\), \(Q_i(b_i)=\beta_i\), and again \(\tau_i(q)\leq0\). Thus all thresholds are inward shifts.

This definition deliberately uses support endpoints at saturated caps. More precisely,
\[
\tau_i(0)=
\begin{cases}
0,&b_i<A,\\
\beta_i,&b_i=A.
\end{cases}
\]
When \(b_i=A\), every threshold in the whole interval \([\beta_i,0]\) has cap area \(b_i\); there is no uniqueness assertion at this endpoint. At the other endpoint, if \(b_i=m\), then
\[
\tau_i(m)=Q_i(0)=\alpha_i
\]
and the shifted cap has area zero, although it may contain a support segment.

Put
\[
\sigma(q)=\tau_1(q)+\tau_2(q)+\tau_3(q).
\]
This is continuous on \([0,m]\). We now consider all possible endpoint positions relative to \(-1\).

Suppose first that \(\sigma(0)\leq-1\). For \(b_i<A\), set \(I_i=\{0\}\), and for \(b_i=A\), set \(I_i=[\beta_i,0]\). Every \(\theta_i\in I_i\) satisfies \(F_i(\theta_i)=b_i\), and the possible sums \(\theta_1+\theta_2+\theta_3\) form the interval
\[
[\sigma(0),0].
\]
Thus there are \(\theta_i\in I_i\) with
\[
\theta_1+\theta_2+\theta_3=-1.
\]
In this case set \(q_*=0\).

Suppose next that \(\sigma(0)>-1\) and \(\sigma(m)\leq-1\). By continuity there is \(q_*\in(0,m]\) such that
\[
\sigma(q_*)=-1.
\]
Set \(\theta_i=\tau_i(q_*)\). In both of the preceding cases,
\[
\sum_i\theta_i=-1,\qquad
|K\cap\{f_i\leq\theta_i\}|=b_i-q_*.
\]

Define \(g_i=f_i-\theta_i\). Their linear parts are unchanged, so they are nonconstant and pairwise nonparallel, and
\[
g_1+g_2+g_3=0.
\]
The zero lines of \(g_1\) and \(g_2\) meet at a unique point \(p\). The displayed identity then gives \(g_3(p)=0\), so all three zero lines are concurrent. After translating \(p\) to the origin, the functions
\[
\ell_i(z)=g_i(p+z)
\]
are nonzero pairwise nonparallel linear forms with \(\ell_1+\ell_2+\ell_3=0\). Applying accepted fact `851e063a1b9908a3` to \(K-p\) and these forms gives
\[
5\sum_i(b_i-q_*)-6\min_i(b_i-q_*)\geq4A.
\]
Because the same \(q_*\leq m\) is subtracted from all three cap areas,
\[
\min_i(b_i-q_*)=m-q_*.
\]
Therefore
\[
5\sum_i b_i-6m\geq4A+9q_*\geq4A.
\]
This application includes \(q_*=m\) and any zero-area shifted cap, since the accepted fact has no positive-cap hypothesis.

It remains only the endpoint alternative
\[
\sigma(0)>-1,\qquad \sigma(m)>-1.
\]
For every \(x\in\mathbb R^2\),
\[
\sum_i\bigl(f_i(x)-\tau_i(m)\bigr)=-1-\sigma(m)<0.
\]
Hence at least one \(f_i(x)-\tau_i(m)\) is negative, so the three shifted halfplanes cover \(\mathbb R^2\). Their intersections with \(K\) have respective areas \(b_i-m\). The union bound, valid also for the support-line cap of area zero belonging to every index with \(b_i=m\), yields
\[
A\leq\sum_i(b_i-m)=\sum_i b_i-3m.
\]
It follows that
\[
5\sum_i b_i-6m\geq5(A+3m)-6m=5A+9m>4A.
\]
This exhausts all cases and proves the three-cap inequality.

We finally derive the exact-cell form. The three cutting lines are null, so strict versus weak inequalities on cell boundaries do not alter any area. Also, the cell in which all three \(f_i\) are positive is empty because their sum is \(-1\). Thus the three singleton cells, the three doubleton cells, and the triple cell partition \(K\) up to a null set. Put
\[
S=s_1+s_2+s_3,\qquad D=d_1+d_2+d_3,\qquad
r=\min_i(s_i-d_i).
\]
Then
\[
A=S+D+g.
\]
For \(\{i,j,k\}=\{1,2,3\}\),
\[
b_i=s_i+d_j+d_k+g=D+g+(s_i-d_i).
\]
Consequently
\[
\sum_i b_i=S+2D+3g,\qquad
\min_i b_i=D+g+r.
\]
Substitution gives the exact identity
\[
\begin{aligned}
5\sum_i b_i-6\min_i b_i-4A
&=5(S+2D+3g)-6(D+g+r)-4(S+D+g)\\
&=S+5g-6r.
\end{aligned}
\]
The already proved three-cap inequality makes the left side nonnegative, and therefore
\[
s_1+s_2+s_3+5g\geq6\min_i(s_i-d_i).
\]

## External sources

none
