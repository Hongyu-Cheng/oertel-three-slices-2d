---
fact_id: b12dbfdde261e9de
kind: lemma
author: "mp_r377_fixed_triangle_endpoint"
assurance: LLM-verified
subgoal_id: counterexample-triangle-n3-matrix-search
depends_on: ["09393c6edf1fc4e2","64760c76cadff481","f74f24523b5f53b2"]
source_packet_sha256: 21820578fe7742b8f26315c261ce67cc5ae2fa4c4372e494ae0e698e72f8b574
verifier_run: 3edf8dbdcf7447c9
target_match: null
---

## Statement

Normalize \(|\Delta|=1\), and put
\[
p=\frac{3743567}{7758225},
\qquad
p_3=\frac{838966}{8136675}.
\tag{1}
\]

First, the following fixed-level two-cap statement holds. Let \(f,g\) be nonconstant affine functions on a nondegenerate triangle. If
\[
\bigl|\{f\ge0\}\bigr|=p,
\qquad
\bigl|\{g\ge0\}\bigr|=p,
\tag{2}
\]
where areas are normalized by the area of the triangle, then
\[
\boxed{\quad
\bigl|\{f+g\le0\}\bigr|\ge\frac14.
\quad}
\tag{3}
\]
The statement includes every vertex-on-line, repeated-value, parallel-line, and constant-sum boundary case.

Now fix
\[
L=\begin{pmatrix}
-29/2&53/2&-25/2\\
-29/2&-25/2&53/2\\
30&-13&-13
\end{pmatrix},
\qquad
A=\frac{841}{6708},
\qquad
B=\frac{47089}{41925},
\tag{4}
\]
\[
t=\frac{377081}{754650}
=\frac{2(1+A+B)}9.
\tag{5}
\]
There do not exist real, and hence there do not exist rational, matrices
\(U,V\in\mathbb R^{3\times3}\) and
\(\sigma\in\mathbb R^3\) satisfying the endpoint hypotheses of accepted
facts `64760c76cadff481` and `09393c6edf1fc4e2`,
including
\[
\mathbf1^\top U=\mathbf1^\top,\qquad
\mathbf1^\top V=\mathbf1^\top,\qquad
|\det U|=A,\qquad |\det V|=B,
\tag{6}
\]
the three compatibility inequalities
\[
\min_jU_{ij}+\min_jV_{ij}\ge0
\qquad(i=1,2,3),
\]
\[
q:=\sigma_1+\sigma_2+\sigma_3>1,
\tag{7}
\]
and all three strict rows
\[
\mathcal C(L_{i*};0)
+A\mathcal C((LU)_{i*};-\sigma_i)
+B\mathcal C((LV)_{i*};\sigma_i)
<t
\qquad(i=1,2,3).
\tag{8}
\]

Equivalently, in the lossless parametrization of accepted fact
`f74f24523b5f53b2`, let
\[
-1<s<1,\qquad
U=\ell\mathbf1^\top+(1-s)X,
\qquad
V=-\ell\mathbf1^\top+(1+s)Y,
\tag{9}
\]
where \(\mathbf1^\top\ell=s\) and \(X,Y\) are arbitrary nonnegative
column-stochastic matrices having the determinant magnitudes required by
(6). Put
\[
d=L\ell+\sigma.
\tag{10}
\]
For the three bottom-cap capacity thresholds \(D_i(X,s)\) defined by
\[
\mathcal C\!\left(
D_i(X,s)\mathbf1^\top
+(1-s)(LX)_{i*};0
\right)
=
\begin{cases}
p,&i=1,2,\\
p_3,&i=3,
\end{cases}
\tag{11}
\]
one has the strict universal bound
\[
\boxed{\quad
\sum_{i=1}^3D_i(X,s)<s-1<1+s.
\quad}
\tag{12}
\]
In particular, the proposed inequality
\(\sum_iD_i(X,s)\le1+s\) holds on every cap-order and determinant-sign
chamber, with a uniform gap of more than \(2\).

## Proof

We first prove the two-cap statement (3). Accepted fact
`64760c76cadff481` gives the complete exact cap formula, including repeated
vertex values. Exact arithmetic in (1) gives
\[
\frac12-p=\frac{271091}{15516450}>0.
\tag{13}
\]
Consequently an affine function with cap fraction \(p\) has both a
positive and a negative vertex value. Up to a positive scaling, a cap
with exactly one positive vertex has, after a vertex permutation, the
form
\[
S_1(u)=
\left(1,\ 1-u,\ 1-\frac1{pu}\right),
\qquad
1\le u\le\frac1p.
\tag{14}
\]
Indeed, the one-positive cap formula gives
\[
\frac1{u\,(pu)^{-1}}=p.
\]
Likewise a cap with two nonnegative vertices and one negative vertex has,
after scaling the negative value to \(-1\), the form
\[
D_1(u)=
\left(-1,\ u-1,\ \frac1{(1-p)u}-1\right),
\qquad
1\le u\le\frac1{1-p}.
\tag{15}
\]
The endpoints in (14)-(15) include a cutting line through a vertex.
Replacing \(u\) by the other factor in the displayed product swaps the
two nondistinguished vertices, so no ordering of those two vertices is
lost.

For later reference define the cyclic representatives
\[
S_2(u)=
\left(1-\frac1{pu},\ 1,\ 1-u\right),
\tag{16}
\]
\[
D_2(u)=
\left(\frac1{(1-p)u}-1,\ -1,\ u-1\right),
\tag{17}
\]
\[
D_3(u)=
\left(u-1,\ \frac1{(1-p)u}-1,\ -1\right).
\tag{18}
\]
Under simultaneous vertex permutations and interchange of \(f,g\),
there are exactly six support-incidence orbits:
\[
\begin{array}{c|c|c}
\text{orbit}&f&g\\ \hline
SS_{\rm same}&S_1(u)&S_1(v)\\
SS_{\rm diff}&S_1(u)&S_2(v)\\
SD_{\rm in}&S_1(u)&D_3(v)\\
SD_{\rm out}&S_1(u)&D_1(v)\\
DD_{\rm same}&D_1(u)&D_1(v)\\
DD_{\rm diff}&D_1(u)&D_2(v).
\end{array}
\tag{19}
\]
Here \(S\) means a one-positive cap, \(D\) means a two-positive cap,
``in'' means that the singleton vertex lies in the doubleton support,
and ``out'' means that it does not. The parameter ranges are those in
(14) for every \(S\) and those in (15) for every \(D\). After normalizing
\(f\), the remaining positive relative scale is arbitrary:
\[
h=f+\lambda g,\qquad \lambda>0.
\tag{20}
\]
Thus (19)-(20) parameterize every pair in (2), including all support
boundaries.

It remains to check when
\[
\bigl|\{h\le0\}\bigr|<\frac14
\tag{21}
\]
could occur. Write the three vertex values of \(h\) as
\(h_1,h_2,h_3\). There are exactly seven relevant sign cases. If all
three are nonnegative and not all zero, (21) holds. If \(h_i<0\) and
\(h_j,h_k\ge0\), the exact one-negative formula says that (21) is
equivalent to
\[
4h_i^2<
(h_j-h_i)(h_k-h_i).
\tag{22}
\]
If \(h_i,h_j\le0<h_k\), the exact one-positive complement formula says
that (21) is equivalent to
\[
4h_k^2>
3(h_k-h_i)(h_k-h_j).
\tag{23}
\]
These are one all-nonnegative case, three cases of (22), and three cases
of (23). If all three values are nonpositive, the lower cap is full. If
all three vanish, it is also full by the constant-row convention.
Therefore the seven predicates above exhaust every order, equality, and
sign chamber without sorting the two same-sign values.

Substitution of each row of (19) into the seven predicates produces
\(6\cdot7=42\) rational semialgebraic systems in
\((u,v,\lambda)\). Every denominator is positive on its displayed
parameter interval. Exact real cylindrical algebraic decomposition gives
\[
\begin{array}{c|ccccccc}
SS_{\rm same}&F&F&F&F&F&F&F\\
SS_{\rm diff}&F&F&F&F&F&F&F\\
SD_{\rm in}&F&F&F&F&F&F&F\\
SD_{\rm out}&F&F&F&F&F&F&F\\
DD_{\rm same}&F&F&F&F&F&F&F\\
DD_{\rm diff}&F&F&F&F&F&F&F,
\end{array}
\tag{24}
\]
where \(F\) means that the existential system consisting of the parameter
domain and the corresponding strict violation predicate is false.
For auditability, (24) was computed by exact
\[
\operatorname{Resolve}\!\left[
\exists(u,v,\lambda)\in\mathbb R^3:
\text{domain}\wedge\text{violation},
\mathbb R
\right]
\]
after the literal substitutions (14)-(20); no floating-point number
occurs. WolframScript 1.13.0 with the local Wolfram Language 14.3.0
kernel returned `False` separately for all 42 systems and exited with
status zero. Equations (14)-(23) are the complete symbolic reduction
supplied to that exact CAD, so (24) proves (3).

We apply (3) to the fixed middle matrix. The middle cap fractions, directly
from the exact formula in accepted fact `64760c76cadff481`, are
\[
c_1=c_2=\frac{2809}{6396},
\qquad
c_3=\frac{900}{1849}.
\tag{25}
\]
Equations (4)-(5) then give exactly
\[
\frac{t-c_1}{A}=p,
\qquad
\frac{t-c_3}{A}=p_3.
\tag{26}
\]
Moreover
\[
\frac19-p_3=\frac{21703}{2712225}>0,
\qquad
\frac19<\frac14.
\tag{27}
\]

Use the lossless representation (9) from accepted fact
`f74f24523b5f53b2`, and put
\[
k=1-s>0.
\]
Since \(X\) is nondegenerate and the three rows of \(L\) are nonconstant
on the affine plane of \(\Delta\), the affine functions
\[
z_i(\lambda)=k(LX)_{i*}\lambda
\qquad(i=1,2,3)
\tag{28}
\]
are nonconstant. Also
\[
z_1+z_2+z_3=k,
\tag{29}
\]
because \(\mathbf1^\top L=\mathbf1^\top\) and
\(\mathbf1^\top X=\mathbf1^\top\).

Let \(q_1,q_2,q_3\) be their unique upper-cap thresholds:
\[
\mathcal C(k(LX)_{i*};q_i)
=
\begin{cases}
p,&i=1,2,\\
p_3,&i=3.
\end{cases}
\tag{30}
\]
Apply (3) to
\[
f=z_1-q_1,\qquad g=z_2-q_2.
\]
It gives
\[
\left|
\{z_1+z_2\le q_1+q_2\}
\right|
\ge\frac14.
\tag{31}
\]
By (29), the same set is
\[
\{z_3\ge k-q_1-q_2\}.
\tag{32}
\]
Its area is strictly larger than \(p_3\) by (27). The cap function of
the nonconstant affine function \(z_3\) is continuous and strictly
decreasing between its support values, by the complete formula in
accepted fact `64760c76cadff481`. Therefore its \(p_3\)-threshold obeys
\[
q_3>k-q_1-q_2,
\qquad\text{hence}\qquad
q_1+q_2+q_3>k.
\tag{33}
\]

Adding \(d_i\) to the three vertex values changes the zero-threshold cap
to the \(z_i\)-cap at threshold \(-d_i\). Thus the capacity threshold in
(11) is
\[
D_i(X,s)=-q_i.
\tag{34}
\]
Equation (33) gives the first strict inequality in (12):
\[
\sum_iD_i(X,s)
=-\sum_iq_i
<-k=s-1.
\tag{35}
\]

Finally suppose the full strict rows (8) held. The large-end cap is
nonnegative, so (25)-(26) imply that the three bottom cap fractions are
strictly below \(p,p,p_3\), respectively. Monotonicity of the cap under
addition of \(d_i\) and (34) then give
\[
d_i<D_i(X,s)\qquad(i=1,2,3).
\tag{36}
\]
On the other hand, (10), \(\mathbf1^\top L=\mathbf1^\top\), and
\(\mathbf1^\top\ell=s\) give
\[
\sum_i d_i=s+\sum_i\sigma_i=s+q>1+s
\tag{37}
\]
by the surviving orientation in accepted fact `09393c6edf1fc4e2`.
Equations (12), (36), and (37) are contradictory. Hence no endpoint
completion of the fixed \(L\) exists. The proof did not restrict \(Y\),
the shape of \(X\), the determinant signs, or any cap-order chamber.

## External sources

none
