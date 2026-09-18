---
fact_id: a8ec4e2404adfc8a
kind: lemma
author: "/root/mp_r57_exact_a2_full_realization_stress"
assurance: LLM-verified
subgoal_id: canonical-all-double-positive-middle-scale-closure
depends_on: ["0e51a47a9add571f","2f9be517307232c7","91cb5bfc71da49ac","c98440f17e611ea2"]
source_packet_sha256: 29a0d8e306abc2e250bd5dfa19138f7e9574bb4e25c4946b5fb8e56aaa7e0ae2
verifier_run: 7ad74a2ecc78448d
target_match: null
---

## Statement

Let \(N=\{1,2,3\}\).  Assume the affine sign-plane and exact-cell hypotheses of accepted fact `0e51a47a9add571f`: \(A_0,A_2,K\subseteq\mathbb R^2\) are nonempty two-dimensional convex polytopes,
\[
\frac{A_0+A_2}{2}\subseteq K,
\]
\(f_1,f_2,f_3\) are nonconstant affine functions with pairwise nonparallel linear parts,
\[
f_1+f_2+f_3=-1,
\]
and
\[
L_1+L_2+L_3<-1.
\]
Use the exact convention
\[
P_J=A_0\cap
\{f_j\leq L_j\ (j\in J),\ f_j>L_j\ (j\notin J)\},
\]
\[
Q_J=A_2\cap
\{f_j\leq-L_j\ (j\in J),\ f_j>-L_j\ (j\notin J)\},
\]
\[
R_J=K\cap
\{f_j\leq0\ (j\in J),\ f_j>0\ (j\notin J)\}.
\]
Write their areas as \(p_J,q_J,r_J\), and put
\[
M=|A_0|,\qquad m=|A_2|,\qquad k=|K|.
\]
Assume \(M\geq m\), and define the canonical excess
\[
W=
\sum_J(3|J|-2)p_J
+\sum_H(3|H|-2)q_H
+\sum_G(3|G|-2)r_G.
\]

Assume the complete canonical finite-interior hypotheses and the all-double positive \(Q\)-support of accepted fact `91cb5bfc71da49ac`:
\[
q_{123}>0,\qquad
x_i:=q_{N\setminus\{i\}}>0\quad(i=1,2,3),
\]
and every other \(Q\)-cell has zero area.  Put
\[
u_i=\sum_{J\ni i}p_J,\qquad
c_i=\sum_{G\ni i}r_G,
\]
\[
s_P=\sum_i p_{\{i\}},\qquad
d_P=\sum_{i<j}p_{\{i,j\}},\qquad
r=r_{123}.
\]
Assume explicitly
\[
0<u_i<M,\qquad 0<x_i<m,\qquad
r_1r_2r_3r>0.
\tag{1}
\]
Assume \(W=0\).
The allowed boundary strata may have zero doubleton \(P\)- or \(R\)-cells, coincident cell vertices, redundant polygon vertices, and points on cutting lines; only the positive-area conditions in (1) are required.

Assume the three canonical crossings and left tails:
\[
u_i+(m-x_i)+c_i=h,
\qquad
h=\frac{2(M+m+k)}9,
\tag{2}
\]
\[
h\leq c_i+m,\qquad
h\leq c_i+M
\qquad(i=1,2,3).
\tag{3}
\]
Assume also that these data arise from an actual counterexample to the locked depth target in the canonical \(W=0\) branch.  Accepted fact `2f9be517307232c7` then gives, strictly,
\[
M<m+k,\qquad
m<M+k,\qquad
k<M+m.
\tag{4}
\]

Define the closed halfplane sections
\[
P_i^-=A_0\cap\{f_i\leq L_i\},\qquad
Q_i^+=A_2\cap\{f_i\geq-L_i\},\qquad
K_i^+=K\cap\{f_i\geq0\}.
\tag{5}
\]
Every body in (5) is two-dimensional, each of the three indexed triples has empty common intersection, and Scott's planar theorem gives the exact simultaneous inequalities
\[
\boxed{\quad
s_P+d_P\geq\frac95\min_i u_i,
\quad}
\tag{6}
\]
\[
\boxed{\quad
x_1+x_2+x_3\geq\frac95\min_i x_i,
\quad}
\tag{7}
\]
\[
\boxed{\quad
k-r\geq\frac95\min_i(k-c_i).
\quad}
\tag{8}
\]
Moreover,
\[
\boxed{\quad
\max_i(x_i-u_i)
\geq
\frac{2k+7m-2M+5r}{9}.
\quad}
\tag{9}
\]
Consequently every actual counterexample under these hypotheses satisfies
\[
\boxed{\quad
\max_i x_i
>
\frac{5(m+r)}9
>
\frac{5m}{9}.
\quad}
\tag{10}
\]
The conclusion is pointwise for each realization with \(r>0\); it supplies no uniform positive lower bound for \(r/m\).

## Proof

We first check all hypotheses of Scott's theorem, including dimensionality.  Each set in (5) is the intersection of a compact convex polygon with a closed halfplane, so it is compact and convex.

For \(P_i^-\), the exact-cell partition gives
\[
|P_i^-|=\sum_{J\ni i}p_J=u_i>0.
\]
Thus \(P_i^-\) has nonempty planar interior.  For \(Q_i^+\), the all-double support gives, up to the null cutting line,
\[
|Q_i^+|=x_i>0.
\]
Indeed, \(Q_{N\setminus\{i\}}\) is the only positive-area exact cell whose index omits \(i\); any other such exact cell and the equality line have planar area zero.  Thus every \(Q_i^+\) is also two-dimensional.

Fix \(i\), and choose \(j\neq i\).  By (1), \(r_j>0\).  Throughout the strict cell \(R_{\{j\}}\), one has \(f_i>0\), so
\[
R_{\{j\}}\subseteq K_i^+.
\]
Hence \(|K_i^+|\geq r_j>0\), and every \(K_i^+\) is two-dimensional.  The exact cells with \(i\in G\) partition \(K\cap\{f_i\leq0\}\), while the line \(f_i=0\) has planar area zero because \(f_i\) is nonconstant.  Therefore
\[
|K_i^+|=k-c_i.
\tag{11}
\]

Each triple in (5) has no common point.  A point in all three \(P_i^-\) would satisfy
\[
-1=\sum_i f_i\leq\sum_iL_i<-1,
\]
a contradiction.  A point in all three \(Q_i^+\) would satisfy
\[
-1=\sum_i f_i\geq-\sum_iL_i>1,
\]
again a contradiction.  A point in all three \(K_i^+\) would satisfy
\[
-1=\sum_i f_i\geq0,
\]
which is impossible.  Thus the interiors in each triple have empty common intersection.

We now retain each union area exactly.  Accepted fact `0e51a47a9add571f` gives \(P_{123}=\varnothing\).  Up to null cutting lines, \(\bigcup_iP_i^-\) is the disjoint union of all singleton and doubleton \(P\)-cells.  Hence
\[
\left|\bigcup_iP_i^-\right|=s_P+d_P.
\tag{12}
\]
For the all-double \(Q\)-support, a point belongs to \(Q_i^+\) exactly when its exact index omits \(i\), apart from the null equality line.  The only positive such cell is \(Q_{N\setminus\{i\}}\).  The three caps are distinct exact cells, so
\[
\left|\bigcup_iQ_i^+\right|
=x_1+x_2+x_3.
\tag{13}
\]
Finally, a middle point belongs to some \(K_i^+\) unless all three \(f_i<0\).  Up to cutting lines, the omitted set is exactly \(R_{123}\).  Therefore
\[
\left|\bigcup_iK_i^+\right|=k-r.
\tag{14}
\]

Scott's theorem as recorded in accepted fact `c98440f17e611ea2`, applied to the three two-dimensional convex bodies in each row of (5), says that their union area is at least \(9/5\) times their minimum area.  Combining it with (11)-(14) proves (6)-(8).  This simultaneous use is valid on every allowed boundary stratum because all weak-versus-strict discrepancies lie in the three cutting lines and have planar area zero.  The positive areas in (1) prevent any of the nine bodies in (5) from collapsing to a segment or point.

It remains to couple the middle Scott inequality to the crossings.  Put
\[
t_i=x_i-u_i.
\]
Combining (2) with the first inequality in (3) gives
\[
t_i\geq0.
\tag{15}
\]
Equation (2) also gives
\[
c_i=h-m+t_i.
\tag{16}
\]
Thus
\[
\min_i(k-c_i)
=
k-h+m-\max_i t_i.
\tag{17}
\]
Substitute (17) into (8):
\[
5(k-r)
\geq
9\left(k-h+m-\max_i t_i\right).
\]
Rearrangement, followed by \(9h=2(M+m+k)\), gives
\[
\begin{aligned}
9\max_i t_i
&\geq
4k+9m-9h+5r\\
&=
2k+7m-2M+5r.
\end{aligned}
\]
This proves (9).

The first strict inequality in (4) gives
\[
2k+7m-2M+5r
>
2k+7m-2(m+k)+5r
=
5m+5r.
\]
Together with (9),
\[
\max_i t_i>\frac{5(m+r)}9.
\tag{18}
\]
By definition \(t_i=x_i-u_i\), and (1) gives \(u_i>0\).  Hence \(t_i<x_i\) for every \(i\).  Equation (18) therefore proves
\[
\max_i x_i
>
\max_i t_i
>
\frac{5(m+r)}9.
\]
Finally \(r>0\), so \(5(m+r)/9>5m/9\).  This proves (10).  No step bounds \(r\) away from zero uniformly, and no such conclusion is part of the statement.

## External sources

P. R. Scott, "On the union of convex bodies with no interior point in common", Mathematika 37 (1990), 245-250, https://doi.org/10.1112/S0025579300012961 .

The theorem used, as recorded in accepted fact `c98440f17e611ea2`, states that if \(K_1,\ldots,K_{d+1}\) are \(d\)-dimensional convex bodies whose interiors have no common point, then
\[
\left|\bigcup_{i=1}^{d+1}K_i\right|
\geq
\frac{(d+1)^d}{(d+1)^d-d^d}
\min_i|K_i|.
\]
For \(d=2\), the coefficient is \(9/(9-4)=9/5\).  The proof above verifies compact convexity, positive planar area, and empty common intersection separately for the three source bodies, the three endpoint bodies, and the three middle bodies, so every applicability condition is satisfied.
