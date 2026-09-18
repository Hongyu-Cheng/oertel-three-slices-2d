---
fact_id: e40abbed940a40ab
kind: lemma
author: "/root/mp_r52_scale_bridge"
assurance: LLM-verified
subgoal_id: canonical-all-double-variable-cap-normal-form
depends_on: ["0e51a47a9add571f","ce343e749df349fe"]
source_packet_sha256: d06b1bd4931a96ee2ad98febfdccd8ca28ae4bb1e6d19d1eacea40d5f47cc8f4
verifier_run: c80ad4f1c40a469b
target_match: null
---

## Statement

Let \(N=\{1,2,3\}\).  Assume the affine sign-plane hypotheses and exact-cell convention of accepted fact `0e51a47a9add571f`: the functions \(f_1,f_2,f_3\) are nonconstant affine functions on \(\mathbb R^2\), their linear parts are pairwise nonparallel,
\[
f_1+f_2+f_3=-1,
\]
the real thresholds satisfy
\[
s:=L_1+L_2+L_3<-1,
\]
and \(A_0,A_2,K\) are nonempty two-dimensional convex polytopes satisfying
\[
\frac{A_0+A_2}{2}\subseteq K.
\]
Thus
\[
P_\varnothing=A_0\cap\{f_i>L_i\text{ for all }i\},
\]
\[
Q_H=A_2\cap
\{f_i\le -L_i\ (i\in H),\ f_i>-L_i\ (i\notin H)\},
\]
and
\[
R_G=K\cap
\{f_i\le0\ (i\in G),\ f_i>0\ (i\notin G)\}.
\]
Write \(p_\varnothing=|P_\varnothing|\), \(q_H=|Q_H|\), and \(r_G=|R_G|\).

Assume that the positive-area \(Q\)-support is exactly
\[
\{123,12,13,23\},
\]
so in particular
\[
q:=q_{123}>0.
\]
Assume also
\[
p_\varnothing>0,\qquad r_{123}>0,\qquad r_1,r_2,r_3>0.
\]
Define
\[
\delta=-1-s>0,\qquad
\gamma=1-s=\delta+2>2
\]
and the three global ambient triangles
\[
\mathcal T_1=\{x:f_i(x)\le0\text{ for }i=1,2,3\},
\]
\[
\mathcal T_P=\{x:f_i(x)\ge L_i\text{ for }i=1,2,3\},
\]
\[
\mathcal T_Q=\{x:f_i(x)\le-L_i\text{ for }i=1,2,3\}.
\]
Then all three are nondegenerate compact triangles.  Moreover,
\[
\mathcal T_1\subseteq K,\qquad
|\mathcal T_1|=r_{123},
\]
\[
|\mathcal T_P|=\delta^2r_{123},\qquad
|\mathcal T_Q|=\gamma^2r_{123},
\]
and
\[
p_\varnothing\le|\mathcal T_P|.
\]
Consequently,
\[
|\mathcal T_Q|
\ge
\left(\sqrt{p_\varnothing}+2\sqrt{r_{123}}\right)^2.
\tag{1}
\]

More precisely, let
\[
\Sigma=\operatorname{conv}\{(0,0),(1,0),(0,1)\}.
\]
If \(\Psi:\mathbb R^2\to\mathbb R^2\) is an affine isomorphism with
\(\Psi(\mathcal T_Q)=\Sigma\), and if the coordinate area of the central
\(Q\)-cell satisfies
\[
|\Psi(Q_{123})|=\frac D2,
\]
then \(D>0\),
\[
|\mathcal T_Q|=\frac qD,
\tag{2}
\]
and
\[
D\le
\frac{q}{\left(\sqrt{p_\varnothing}+2\sqrt{r_{123}}\right)^2}.
\tag{3}
\]
No inclusion \(\mathcal T_Q\subseteq A_2\) is assumed or asserted; one only has
\(Q_{123}=A_2\cap\mathcal T_Q\).  All strict-versus-weak boundary choices above
are the exact-cell choices of `0e51a47a9add571f`; every cutting line has planar
area zero, so the area identities and inequalities remain valid when a
polytope edge or vertex is collinear or coincident with a cutting line.

## Proof

By accepted fact `0e51a47a9add571f`, the affine sign map
\[
F:\mathbb R^2\longrightarrow
\{z\in\mathbb R^3:z_1+z_2+z_3=-1\},
\qquad
F(x)=(f_1(x),f_2(x),f_3(x)),
\]
is an affine isomorphism.  Put
\[
\Delta=\{u\in\mathbb R^3:u_i\ge0,\ u_1+u_2+u_3=1\}.
\]
The three positive middle singleton areas allow application of accepted fact
`ce343e749df349fe`.  It gives
\[
\mathcal T_1\subseteq K
\]
and identifies \(R_{123}\) with \(\mathcal T_1\) up to the null cutting-line
boundaries.  Hence
\[
F(\mathcal T_1)=-\Delta,\qquad
|\mathcal T_1|=r_{123}>0.
\tag{4}
\]

For \(x\in\mathcal T_P\), the three numbers
\[
f_i(x)-L_i
\]
are nonnegative and have sum
\[
-1-s=\delta.
\]
Conversely, every nonnegative triple with sum \(\delta\) corresponds under
\(F\) to a unique point of \(\mathcal T_P\).  Therefore
\[
F(\mathcal T_P)=(L_1,L_2,L_3)+\delta\Delta.
\tag{5}
\]
The affine map on the sign plane
\[
z\longmapsto (L_1,L_2,L_3)-\delta z
\]
maps \(-\Delta\) onto the right-hand side of (5).  Its linear part on the
two-dimensional direction space is multiplication by \(-\delta\).  Thus
\(\mathcal T_P\) is a translated reflected dilation of \(\mathcal T_1\) by
the exact positive linear factor \(\delta\), and (4) gives
\[
|\mathcal T_P|=\delta^2r_{123}.
\tag{6}
\]

Similarly, for \(x\in\mathcal T_Q\), the three numbers
\[
-L_i-f_i(x)
\]
are nonnegative and have sum
\[
-s+1=\gamma.
\]
Hence
\[
F(\mathcal T_Q)=-(L_1,L_2,L_3)-\gamma\Delta.
\tag{7}
\]
The affine map
\[
z\longmapsto -(L_1,L_2,L_3)+\gamma z
\]
maps \(-\Delta\) onto the right-hand side of (7).  Its linear part on the
direction space is multiplication by \(\gamma\).  Thus \(\mathcal T_Q\) is a
translated dilation of \(\mathcal T_1\) by the exact positive linear factor
\(\gamma=\delta+2\), and
\[
|\mathcal T_Q|=\gamma^2r_{123}.
\tag{8}
\]
Equations (4), (5), and (7), together with \(\delta>0\) and \(\gamma>0\), also
show that the three displayed ambient sets are nondegenerate compact
triangles.

The exact cell \(P_\varnothing\) is contained in the interior of
\(\mathcal T_P\).  Therefore (6) implies
\[
p_\varnothing\le\delta^2r_{123}.
\]
Because \(\delta>0\) and \(r_{123}>0\),
\[
\delta\sqrt{r_{123}}\ge\sqrt{p_\varnothing}.
\tag{9}
\]
Using (8), \(\gamma=\delta+2\), and (9),
\[
\begin{aligned}
|\mathcal T_Q|
&=(\delta+2)^2r_{123}\\
&=\left(\delta\sqrt{r_{123}}+2\sqrt{r_{123}}\right)^2\\
&\ge
\left(\sqrt{p_\varnothing}+2\sqrt{r_{123}}\right)^2,
\end{aligned}
\]
which proves (1).

It remains to verify the optional normalized-coordinate formulation.  Let
\(c>0\) be the constant area multiplier of \(\Psi\).  Since
\(|\Sigma|=1/2\),
\[
c|\mathcal T_Q|=\frac12.
\]
The assumed normalized central-cell area and \(q=|Q_{123}|>0\) give
\[
cq=\frac D2.
\]
Dividing these two equalities yields
\[
\frac q{|\mathcal T_Q|}=D>0,
\]
which is (2).  Combining (2) with (1), and using the positivity of \(q\), \(D\),
\(p_\varnothing\), and \(r_{123}\), proves (3).

Finally, accepted fact `0e51a47a9add571f` states that every cutting set
\(f_i=L_i\), \(f_i=-L_i\), or \(f_i=0\) is a line of planar area zero.
Therefore none of the preceding area comparisons changes on coincident
endpoint, collinear-edge, redundant-vertex, or cutting-line boundary strata.
The all-double support hypothesis is needed here only to ensure \(q>0\) for
the \(D\)-formulation; inequality (1) itself follows from the stated
\(P\)- and \(R\)-cell positivity hypotheses.

## External sources

none
