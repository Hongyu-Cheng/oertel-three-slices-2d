---
fact_id: d3afd91c459bcce8
kind: lemma
author: "mp_r34_bridge_positive"
assurance: LLM-verified
subgoal_id: canonical-single-double-bridge-positive
depends_on: ["0e51a47a9add571f"]
source_packet_sha256: 088cbc3614a0faf6e2e7bab0d085fd833d01961b3223c30179fa6212d3552466
verifier_run: c2e31c75336f4190
target_match: null
---

## Statement

Assume the setting and exact sign-cell convention of accepted fact `0e51a47a9add571f`: \(N=\{1,2,3\}\); the \(f_i\) are nonconstant affine functions on \(\mathbb R^2\) with pairwise nonparallel linear parts and
\[
f_1+f_2+f_3=-1;
\]
\(L_1+L_2+L_3<-1\); and \(A_0,A_2,K\) are nonempty two-dimensional convex polytopes satisfying
\[
(A_0+A_2)/2\subseteq K.
\]
For \(J\subseteq N\), let
\[
P_J=A_0\cap\{f_i\le L_i\ (i\in J),\ f_i>L_i\ (i\notin J)\},
\]
\[
Q_J=A_2\cap\{f_i\le-L_i\ (i\in J),\ f_i>-L_i\ (i\notin J)\},
\]
\[
R_J=K\cap\{f_i\le0\ (i\in J),\ f_i>0\ (i\notin J)\},
\]
and write \(p_J=|P_J|\) and \(q_J=|Q_J|\).

Let \(\{j,k,\ell\}=N\) and suppose
\[
p_\varnothing>0,\qquad q_{\{j\}}>0,\qquad q_{\{k\}}>0.
\]
With closures taken in \(\mathbb R^2\), define
\[
U_j=\frac{P_\varnothing+\overline{Q_{\{j\}}}}2,
\qquad
U_k=\frac{P_\varnothing+\overline{Q_{\{k\}}}}2.
\]
Then
\[
\left|\operatorname{conv}(U_j\cup U_k)\cap R_{\{j,k\}}\right|>0.
\]

## Proof

Because \(A_2\) is closed, \(\overline{Q_{\{j\}}}\subseteq A_2\). If \(y\in\overline{Q_{\{j\}}}\), continuity gives
\[
f_i(y)+L_i\ge0\quad(i\ne j),
\qquad
f_j(y)+L_j\le0.
\]
For \(x\in P_\varnothing\), all quantities \(f_i(x)-L_i\) are strictly positive. Hence, for \(z=(x+y)/2\) and \(i\ne j\),
\[
2f_i(z)
=
\bigl(f_i(x)-L_i\bigr)+\bigl(f_i(y)+L_i\bigr)>0.
\]
Since \(\sum_i f_i(z)=-1\), it follows that
\[
f_j(z)=-1-\sum_{i\ne j}f_i(z)<0.
\]
Moreover, \(z\in K\) by \((A_0+A_2)/2\subseteq K\). Thus
\[
U_j\subseteq K\cap\{f_j<0,\ f_k>0,\ f_\ell>0\}.
\]
The same argument gives
\[
U_k\subseteq K\cap\{f_k<0,\ f_j>0,\ f_\ell>0\}.
\]

Each of \(P_\varnothing,Q_{\{j\}},Q_{\{k\}}\) is convex. A convex subset of \(\mathbb R^2\) with positive area has nonempty interior, since otherwise its affine hull is contained in a line and its area is zero. Therefore there are open balls
\[
B(x_0,\rho_0)\subseteq P_\varnothing,\qquad
B(y_j,\rho_j)\subseteq Q_{\{j\}},\qquad
B(y_k,\rho_k)\subseteq Q_{\{k\}},
\]
with all radii positive. Consequently,
\[
B\left(\frac{x_0+y_j}{2},\frac{\rho_0+\rho_j}{2}\right)
=
\frac{B(x_0,\rho_0)+B(y_j,\rho_j)}2
\subseteq U_j,
\]
and similarly
\[
B\left(\frac{x_0+y_k}{2},\frac{\rho_0+\rho_k}{2}\right)
\subseteq U_k.
\]
Write the two centers as \(z_j\) and \(z_k\).

Consider
\[
z(t)=(1-t)z_j+t z_k,\qquad 0\le t\le1.
\]
At \(z_j\),
\[
f_j<0,\qquad f_k>0,\qquad f_\ell>0,
\]
whereas at \(z_k\),
\[
f_k<0,\qquad f_j>0,\qquad f_\ell>0.
\]
Affineness implies \(f_\ell(z(t))>0\) for every \(t\in[0,1]\). There are unique \(\tau_k,\tau_j\in(0,1)\) such that
\[
f_k(z(\tau_k))=0,\qquad f_j(z(\tau_j))=0.
\]
At \(t=\tau_k\), the plane identity gives
\[
f_j(z(\tau_k))
=
-1-f_\ell(z(\tau_k))<0.
\]
Since \(f_j(z(t))\) crosses from negative to positive at \(\tau_j\), this proves \(\tau_k<\tau_j\). Hence, for every \(t\in(\tau_k,\tau_j)\),
\[
f_j(z(t))<0,\qquad f_k(z(t))<0,\qquad f_\ell(z(t))>0.
\]

Fix \(t_0\in(\tau_k,\tau_j)\). If the two balls about \(z_j,z_k\) above have radii \(r_j,r_k>0\), then
\[
(1-t_0)B(z_j,r_j)+t_0B(z_k,r_k)
=
B\bigl(z(t_0),(1-t_0)r_j+t_0r_k\bigr)
\]
is contained in \(\operatorname{conv}(U_j\cup U_k)\). Since \(K\) is convex and contains \(U_j\cup U_k\),
\[
\operatorname{conv}(U_j\cup U_k)\subseteq K.
\]
The three inequalities at \(z(t_0)\) are strict, so continuity supplies \(\varepsilon>0\), no larger than the displayed ball radius, such that
\[
B(z(t_0),\varepsilon)
\subseteq
\{f_j<0,\ f_k<0,\ f_\ell>0\}.
\]
Therefore
\[
B(z(t_0),\varepsilon)
\subseteq
\operatorname{conv}(U_j\cup U_k)\cap R_{\{j,k\}},
\]
and the intersection has area at least \(\pi\varepsilon^2>0\).

For completeness, the closure introduces no hidden positive-area boundary piece. Indeed,
\[
\overline{Q_{\{j\}}}\setminus Q_{\{j\}}
\subseteq
\{f_k=-L_k\}\cup\{f_\ell=-L_\ell\},
\]
and analogously for \(Q_{\{k\}}\). These are lines because the \(f_i\) are nonconstant, hence have planar area zero. The positive-area ball constructed above satisfies all three middle inequalities strictly, so it avoids every cutting line \(f_i=0\) and belongs to \(R_{\{j,k\}}\) under the exact \(\le\)/\(>\) convention without any boundary reassignment.

## External sources

none
