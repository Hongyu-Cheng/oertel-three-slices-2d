---
fact_id: 639fc3cad3ba84fa
kind: lemma
author: "mp_r36_calibration"
assurance: LLM-verified
subgoal_id: canonical-all-double-calibration-realizability
depends_on: ["0e51a47a9add571f","8234d1112ec2f031"]
source_packet_sha256: dc87640cb763c19c0f9b6b759cf20f1df616172e37c6880841d6666d7915dea2
verifier_run: 7c78505af40a4663
target_match: null
---

## Statement

Let \(N=\{1,2,3\}\). Let \(f_1,f_2,f_3\) be nonconstant affine functions on \(\mathbb R^2\), with pairwise nonparallel linear parts and
\[
f_1+f_2+f_3=-1.
\]
Let \(L_1+L_2+L_3<-1\), and put
\[
\ell_i=f_i+L_i,
\qquad
\gamma=1-L_1-L_2-L_3>2.
\]
Let \(A_0,A_2,K\subset\mathbb R^2\) be nonempty two-dimensional convex polytopes satisfying
\[
\frac{A_0+A_2}{2}\subseteq K.
\]
For \(J\subseteq N\), define
\[
Q_J=A_2\cap
\{\ell_j\le0\ (j\in J),\ \ell_j>0\ (j\notin J)\},
\]
\[
R_J=K\cap
\{f_j\le0\ (j\in J),\ f_j>0\ (j\notin J)\},
\]
and write \(q_J=|Q_J|\), \(r_J=|R_J|\).

Assume
\[
q_{12}=q_{13}=q_{23}=q_N=\frac{|A_2|}{4},
\qquad
q_J=0
\quad
\text{for every other }J\subseteq N.
\]
Then
\[
\gamma^2r_N\le q_N,
\]
and hence
\[
r_N<\frac{q_N}{4}.
\]
Consequently, no such common-plane polytopes can realize the rational table having
\[
q_{12}=q_{13}=q_{23}=q_N=\frac14,
\qquad
r_N=\frac1{10}.
\]

## Proof

The hypotheses and exact-cell convention are those of accepted fact `0e51a47a9add571f`. We first verify that the quarter-cell hypothesis gives the equality configuration required by accepted fact `8234d1112ec2f031`.

Put \(Q=A_2\), and for \(i\in N\) define the closed cap
\[
C_i=Q\cap\{\ell_i\ge0\}.
\]
Each line \(\ell_i=0\) has planar area zero because \(\ell_i\) is nonconstant. Hence
\[
|C_i|
=
\sum_{J:\,i\notin J}q_J
=
q_{N\setminus\{i\}}
=
\frac{|Q|}{4}.
\]
For distinct \(i,j\), the region in \(Q\) where both \(\ell_i>0\) and \(\ell_j>0\) is the union, up to cutting lines of area zero, of cells \(Q_J\) with \(i,j\notin J\). Every such cell has zero area by hypothesis. If the interiors of \(C_i\) and \(C_j\) met, their intersection would contain a nonempty open subset on which both inequalities were strict, and therefore would have positive area. Thus the interiors of \(C_1,C_2,C_3\) are pairwise disjoint.

Their common complementary region is
\[
C_0
=
Q\cap\{\ell_1\le0,\ell_2\le0,\ell_3\le0\}
=
Q_N,
\]
so \(|C_0|=|Q|/4\). In particular,
\[
\sum_{i=1}^3\sqrt{\frac{|C_i|}{|Q|}}
=
3\sqrt{\frac14}
=
\frac32.
\]
Accepted fact `8234d1112ec2f031` now implies that \(Q\) is a triangle, each line \(\ell_i=0\) is one of its medial cutting lines, and the \(C_i\) are its three corner triangles. The halfplanes \(\ell_i\le0\) select the central medial triangle. Therefore the global intersection
\[
T_\gamma
:=
\{x\in\mathbb R^2:\ell_1(x)\le0,\ell_2(x)\le0,\ell_3(x)\le0\}
\]
is exactly that medial triangle, not merely its intersection with \(Q\). Hence
\[
T_\gamma=Q_N
\qquad\text{and}\qquad
|T_\gamma|=q_N. \tag{1}
\]

It remains to compare this triangle with the middle sign triangle. Define
\[
F:\mathbb R^2\to\mathbb R^3,
\qquad
F(x)=(f_1(x),f_2(x),f_3(x)).
\]
Its image lies in
\[
\Pi_1=\{z\in\mathbb R^3:z_1+z_2+z_3=-1\}.
\]
Two of the linear parts of the \(f_i\) are linearly independent because they are nonparallel. Thus the linear part of \(F\) has rank two. Since the direction space of \(\Pi_1\) is also two-dimensional, \(F\) is an affine isomorphism from \(\mathbb R^2\) onto \(\Pi_1\).

Let
\[
T_1
=
\{x\in\mathbb R^2:f_1(x)\le0,f_2(x)\le0,f_3(x)\le0\}.
\]
Then
\[
F(T_1)
=
\Delta_1
:=
\{z\in\Pi_1:z_i\le0\text{ for all }i\}
=
\operatorname{conv}\{-e_1,-e_2,-e_3\}. \tag{2}
\]
Also
\[
\ell_1+\ell_2+\ell_3
=
-1+L_1+L_2+L_3
=
-\gamma.
\]
For \(x\in T_\gamma\), put \(w=(\ell_1(x),\ell_2(x),\ell_3(x))\). Then \(w_i\le0\) and \(\sum_iw_i=-\gamma\), so \(w/\gamma\in\Delta_1\). Since \(w=F(x)+(L_1,L_2,L_3)\), this gives
\[
F(T_\gamma)
=
-(L_1,L_2,L_3)+\gamma\Delta_1
=
-(L_1,L_2,L_3)+\gamma F(T_1). \tag{3}
\]

Write \(F(x)=Gx+b\), where \(G\) is injective. Applying \(F^{-1}\) to (3), for \(y\in T_1\) one obtains
\[
F^{-1}\!\left(-(L_1,L_2,L_3)+\gamma F(y)\right)
=
\gamma y+t,
\]
where
\[
t=G^{-1}\!\left(-(L_1,L_2,L_3)+(\gamma-1)b\right)
\]
is independent of \(y\). The vector inside \(G^{-1}\) lies in the image of \(G\) because both affine-plane points being subtracted have coordinate sum \(-1\). Hence
\[
T_\gamma=t+\gamma T_1. \tag{4}
\]
Thus the two bounded sign triangles are homothetic with ratio \(\gamma\), and planar area scales by \(\gamma^2\). From (1) and (4),
\[
|T_1|
=
\frac{|T_\gamma|}{\gamma^2}
=
\frac{q_N}{\gamma^2}. \tag{5}
\]

Finally,
\[
R_N=K\cap T_1,
\]
so
\[
r_N=|R_N|
\le |T_1|
=
\frac{q_N}{\gamma^2}.
\]
This proves the universal common-plane inequality
\[
\gamma^2r_N\le q_N.
\]
Since \(\gamma>2\) and \(q_N=|Q|/4>0\),
\[
r_N\le\frac{q_N}{\gamma^2}<\frac{q_N}{4}. \tag{6}
\]

For the rational all-double table, \(q_N=1/4\), so \(q_N/4=1/16\), whereas the prescribed middle-cell area is \(r_N=1/10\). Exactly,
\[
r_N-\frac{q_N}{4}
=
\frac1{10}-\frac1{16}
=
\frac3{80}
>
0.
\]
This contradicts (6), proving nonrealizability. The midpoint inclusion was not needed for this contradiction; the common affine sign-plane geometry already forces the stronger bound.

## External sources

none
