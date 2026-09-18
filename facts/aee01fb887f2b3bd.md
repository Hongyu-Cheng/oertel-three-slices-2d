---
fact_id: aee01fb887f2b3bd
kind: lemma
author: "/root/mp_r58_scott_ratio_region"
assurance: LLM-verified
subgoal_id: canonical-all-double-positive-middle-scale-closure
depends_on: ["0e51a47a9add571f","2f9be517307232c7","91cb5bfc71da49ac"]
source_packet_sha256: f80bdfc86eed6efc199418287ae7119d9bbba99178343fa500d0543aa073f0f5
verifier_run: ebfaec95b6a646d5
target_match: null
---

## Statement

Let \(N=\{1,2,3\}\). Let \(A_0,A_2,K\subseteq\mathbb R^2\) be nonempty two-dimensional convex polytopes, let \(f_1,f_2,f_3\) be nonconstant affine functions with pairwise nonparallel linear parts, and let \(L_1+L_2+L_3<-1\). Assume
\[
\frac{A_0+A_2}{2}\subseteq K,
\qquad
f_1+f_2+f_3=-1,
\]
and use the exact-cell convention of accepted fact `0e51a47a9add571f`:
\[
P_J=A_0\cap\{f_j\leq L_j\ (j\in J),\ f_j>L_j\ (j\notin J)\},
\]
\[
Q_H=A_2\cap\{f_j\leq-L_j\ (j\in H),\ f_j>-L_j\ (j\notin H)\},
\]
\[
R_G=K\cap\{f_j\leq0\ (j\in G),\ f_j>0\ (j\notin G)\}.
\]
Write
\[
p_J=|P_J|,\qquad q_H=|Q_H|,\qquad r_G=|R_G|,
\]
\[
M=|A_0|,\qquad m=|A_2|,\qquad k=|K|,
\]
and, as in accepted fact `91cb5bfc71da49ac`,
\[
u_i=\sum_{J\ni i}p_J,\qquad
v_i=\sum_{H\ni i}q_H,\qquad
c_i=\sum_{G\ni i}r_G.
\]
Assume the complete canonical finite-interior hypotheses, \(M\geq m\), the canonical tails
\[
c_i+m\geq h,\qquad c_i+M\geq h,
\]
the three crossings
\[
u_i+v_i+c_i=h,\qquad
h=\frac{2(M+m+k)}9,
\]
and
\[
W:=
\sum_J(3|J|-2)p_J+
\sum_H(3|H|-2)q_H+
\sum_G(3|G|-2)r_G=0.
\]
Suppose the positive \(Q\)-support is exactly
\[
\{123,12,13,23\},
\]
and put
\[
q=q_{123}>0,\qquad
x_i=q_{N\setminus\{i\}}>0,\qquad
m=q+x_1+x_2+x_3.
\]
Assume also
\[
r_1r_2r_3r_{123}>0.
\]

For
\[
K_i=K\cap\{f_i\geq0\}\qquad(i=1,2,3),
\]
each \(K_i\) is a two-dimensional planar convex body, the interiors of the three \(K_i\) have no common point, and
\[
|K_i|=k-c_i.
\]
Consequently,
\[
M+m-k\geq\frac92\min_i(m-x_i).
\tag{1}
\]

Accepted fact `2f9be517307232c7` implies that an actual counterexample has the exact strict necessary condition
\[
M<m+k.
\tag{2}
\]
At the canonical-closure level, the necessary condition retained from (2) is
\[
M\leq m+k.
\tag{3}
\]
Every canonical counterexample closure point satisfying the displayed hypotheses therefore obeys
\[
\max_i x_i\geq\frac{5m}{9}.
\tag{4}
\]
Thus no such \(W=0\) realization in the counterexample closure exists in the exact open region \(\max_i x_i<5m/9\); equivalently, this open region is excluded from the all-double positive-middle branch and supplies the required strict excess there. The conclusion makes no claim at \(\max_i x_i=5m/9\).

## Proof

Fix \(i\in N\), and choose \(j\neq i\). Since \(r_j>0\), the exact singleton cell \(R_{\{j\}}\) has positive planar area. Because \(i\notin\{j\}\), the exact-cell convention gives \(f_i>0\) throughout \(R_{\{j\}}\), and hence
\[
R_{\{j\}}\subseteq K_i.
\]
Thus \(|K_i|>0\). The set \(K_i\) is compact and convex because it is the intersection of the compact convex polytope \(K\) with a closed halfplane. Its positive planar area implies that it has nonempty interior, so it is a two-dimensional planar convex body.

There is not even a common point of the three \(K_i\). Indeed, if \(z\in K_1\cap K_2\cap K_3\), then \(f_i(z)\geq0\) for all \(i\), contrary to
\[
f_1(z)+f_2(z)+f_3(z)=-1.
\]
In particular,
\[
\operatorname{int}K_1\cap\operatorname{int}K_2\cap\operatorname{int}K_3
=\varnothing.
\tag{5}
\]

The exact cells with \(i\in G\) partition \(K\cap\{f_i\leq0\}\), so
\[
\left|K\cap\{f_i\leq0\}\right|
=\sum_{G\ni i}r_G=c_i.
\]
The sets \(K_i\) and \(K\cap\{f_i\leq0\}\) cover \(K\), and their intersection lies in the line \(\{f_i=0\}\). Since \(f_i\) is nonconstant, that line has planar area zero. Therefore
\[
|K_i|=k-c_i.
\tag{6}
\]

Under the all-double support, the only positive \(Q\)-cell omitting \(i\) is \(Q_{N\setminus\{i\}}\). Hence
\[
v_i=m-x_i.
\tag{7}
\]
Using the crossing equality, (6), (7), and \(u_i\geq0\), we obtain
\[
|K_i|
=k-h+u_i+v_i
\geq k-h+(m-x_i).
\tag{8}
\]

Scott's theorem applies to the three bodies by (5), and \(K_1\cup K_2\cup K_3\subseteq K\). Thus
\[
k
\geq |K_1\cup K_2\cup K_3|
\geq\frac95\min_i|K_i|
\geq\frac95\left(k-h+\min_i(m-x_i)\right).
\]
After rearrangement,
\[
9h\geq4k+9\min_i(m-x_i).
\]
Substituting \(9h=2(M+m+k)\) gives
\[
2(M+m-k)\geq9\min_i(m-x_i),
\]
which proves (1).

Now apply accepted fact `2f9be517307232c7` to the three slice areas \(M,k,m\), whose sum is \(T=M+m+k\). Its sufficient hypothesis for the outer slice \(A_0\) is
\[
\frac MT\geq\frac12,
\]
equivalently \(M\geq m+k\). Therefore its exact logical complement for an actual counterexample is (2). Passing only the necessary balance to the canonical counterexample closure gives the non-strict condition (3), which is the form used below.

Combining (1) and (3) yields
\[
\frac92\min_i(m-x_i)
\leq M+m-k
\leq2m.
\]
Therefore
\[
\min_i(m-x_i)\leq\frac{4m}{9}.
\]
Since
\[
\min_i(m-x_i)=m-\max_i x_i,
\]
this is exactly (4).

Equivalently, if \(\max_i x_i<5m/9\), then
\[
\min_i(m-x_i)>\frac{4m}{9},
\]
and (1) forces \(M+m-k>2m\), or \(M>m+k\), contradicting (3). This excludes precisely the stated open ratio region.

If instead \(\max_i x_i=5m/9\), the same calculation gives only
\[
M+m-k\geq2m,
\qquad
M+m-k\leq2m,
\]
so equality can occur in both displayed estimates. Scott's inequality together with the closure-safe condition (3) therefore does not exclude this boundary. No strict boundary conclusion is asserted.

## External sources

P. R. Scott, "On the union of convex bodies with no interior point in common", Mathematika 37 (1990), 245-250, DOI https://doi.org/10.1112/S0025579300012961. Scott's theorem states that if \(K_1,\ldots,K_{d+1}\) are \(d\)-dimensional convex bodies in Euclidean \(d\)-space whose interiors have no common point, then
\[
\left|\bigcup_{i=1}^{d+1}K_i\right|
\geq
\frac{(d+1)^d}{(d+1)^d-d^d}\min_j|K_j|.
\]
For \(d=2\), the coefficient is \(9/(9-4)=9/5\). Here every \(K_i\) is compact and convex and contains the positive-area cell \(R_{\{j\}}\) for any \(j\neq i\), so every \(K_i\) is two-dimensional. Equation (5) verifies the no-common-interior-point hypothesis, all three bodies lie in the same plane, and the measure used throughout is planar Lebesgue area. Hence Scott's theorem applies exactly as used.
