---
fact_id: ecee03aff61db31e
kind: lemma
author: "mp_r10_shear_invariance"
assurance: LLM-verified
subgoal_id: height-shear-invariance
depends_on: []
source_packet_sha256: 1f6524e29bb233d1ef1f0d0d5ca131b21e27f927a1096e7479a74c6185c37cdc
verifier_run: 4757d92365804ed1
target_match: null
---

## Statement

Let \(C\subset\mathbb R\times\mathbb R^2\) be a compact polytope such that
\[
S=C\cap(\mathbb Z\times\mathbb R^2)
 =\bigcup_{i=0}^2(\{i\}\times A_i),
\]
where each \(A_i\subset\mathbb R^2\) is a nonempty two-dimensional convex body. For \(d\in\mathbb R^2\), define
\[
F_d(x,z)=(x,z+(x-1)d),\qquad C_d=F_d(C),\qquad S_d=F_d(S).
\]
Then \(F_d\) is an invertible affine map with inverse \(F_{-d}\), and
\[
S_d=C_d\cap(\mathbb Z\times\mathbb R^2)
 =\bigcup_{i=0}^2\bigl(\{i\}\times(A_i+(i-1)d)\bigr).
\]
For every \(i\in\{0,1,2\}\), every measurable \(E\subseteq\{i\}\times\mathbb R^2\), and every \(d\in\mathbb R^2\),
\[
\mathcal H_2(F_d(E))=\mathcal H_2(E).
\]
Consequently, the three slice areas and their total satisfy
\[
|A_i+(i-1)d|=|A_i|,\qquad T_d=T.
\]
Moreover, for every \(y=(i,z)\in S\),
\[
h_{S_d}\bigl(F_d(y)\bigr)=h_S(y),
\qquad
F_d(y)=(i,z+(i-1)d).
\]
Thus, for every real \(q\),
\[
\exists y\in S:\ h_S(y)\ge qT
\quad\Longleftrightarrow\quad
\exists y_d\in S_d:\ h_{S_d}(y_d)\ge qT_d,
\]
with the forward witness \(y_d=F_d(y)\) and the reverse witness \(y=F_{-d}(y_d)\). In particular, this holds for \(q=2/9\).

## Proof

Write points of \(\mathbb R^3\) as \((x,z)\), where \(x\in\mathbb R\) and \(z\in\mathbb R^2\). Since
\[
F_{-d}(F_d(x,z))
 =(x,z+(x-1)d-(x-1)d)
 =(x,z),
\]
and similarly \(F_d(F_{-d}(x,z))=(x,z)\), the map \(F_d\) is invertible with inverse \(F_{-d}\). It is affine because
\[
F_d(x,z)=(x,z+xd)-(0,d).
\]

The first coordinate is unchanged by \(F_d\). Hence \(F_d\) and \(F_d^{-1}\) both preserve membership in \(\mathbb Z\times\mathbb R^2\). Therefore
\[
\begin{aligned}
C_d\cap(\mathbb Z\times\mathbb R^2)
&=F_d(C)\cap(\mathbb Z\times\mathbb R^2)\\
&=F_d\bigl(C\cap(\mathbb Z\times\mathbb R^2)\bigr)
 =F_d(S).
\end{aligned}
\]
For \(z\in A_i\),
\[
F_d(i,z)=(i,z+(i-1)d),
\]
so
\[
F_d(\{i\}\times A_i)
 =\{i\}\times(A_i+(i-1)d).
\]
This proves the asserted description of \(S_d\). Also, \(C_d\) is a compact polytope because an affine image of the convex hull of finitely many points is the convex hull of their images, and continuity preserves compactness.

Fix \(i\in\{0,1,2\}\). On the plane \(P_i=\{i\}\times\mathbb R^2\), the map \(F_d\) agrees with the ambient Euclidean translation
\[
T_i(x,z)=(x,z+(i-1)d).
\]
For any \(u,v\in\mathbb R^3\),
\[
\|T_i(u)-T_i(v)\|=\|u-v\|.
\]
Thus \(T_i\) maps every cover of a set \(E\subseteq P_i\) bijectively to a cover of \(T_i(E)=F_d(E)\), without changing any covering-set diameter. Applying the same observation to \(T_i^{-1}\), the infima in the definition of every Hausdorff two-dimensional outer content are equal in both directions. Passing to the defining limit gives
\[
\mathcal H_2(F_d(E))=\mathcal H_2(E).
\]
Taking \(E=\{i\}\times A_i\) yields
\[
|A_i+(i-1)d|=|A_i|.
\]
Hence, writing \(a_i^d=|A_i+(i-1)d|\),
\[
T_d=\sum_{i=0}^2a_i^d=\sum_{i=0}^2a_i=T.
\]

It remains to verify directly that every halfspace used in the depth infimum is transported in both directions. Every closed halfspace can be written as
\[
H=\{(x,z):\alpha x+\langle\beta,z\rangle\ge c\},
\]
where \((\alpha,\beta)\ne(0,0)\). If \((x,w)=F_d(x,z)\), then \(z=w-(x-1)d\), so
\[
F_d(H)
 =
 \left\{(x,w):
 (\alpha-\langle\beta,d\rangle)x+\langle\beta,w\rangle
 \ge c-\langle\beta,d\rangle
 \right\}.
\]
Its displayed normal is nonzero: if \(\beta\ne0\), its \(\mathbb R^2\) component is nonzero, while if \(\beta=0\), its first component is \(\alpha\ne0\). Thus \(F_d(H)\) is a closed halfspace.

Conversely, if
\[
K=\{(x,w):\alpha x+\langle\beta,w\rangle\ge c\}
\]
is any closed halfspace, substitution of \(w=z+(x-1)d\) gives
\[
F_d^{-1}(K)
 =
 \left\{(x,z):
 (\alpha+\langle\beta,d\rangle)x+\langle\beta,z\rangle
 \ge c+\langle\beta,d\rangle
 \right\},
\]
again a closed halfspace with nonzero normal. Hence \(H\mapsto F_d(H)\) is a bijection between all closed halfspaces, with inverse \(K\mapsto F_d^{-1}(K)\).

For any closed halfspace \(H\), bijectivity and preservation of the first coordinate give, for each \(i\),
\[
(S_d\cap F_d(H))\cap P_i
 =F_d\bigl((S\cap H)\cap P_i\bigr).
\]
The slice-measure result proved above therefore yields
\[
\mathcal H_2\bigl((S_d\cap F_d(H))\cap P_i\bigr)
 =
\mathcal H_2\bigl((S\cap H)\cap P_i\bigr).
\]
Summing over the three disjoint slices, in accordance with the mass convention in the definition of depth, gives
\[
\mathcal H_2(S_d\cap F_d(H))
 =\mathcal H_2(S\cap H).
\]

Now fix \(y=(i,z)\in S\) and put
\[
y_d=F_d(y)=(i,z+(i-1)d).
\]
If \(H\) is any closed halfspace containing \(y\), then \(F_d(H)\) is a closed halfspace containing \(y_d\), and the preceding mass identity gives
\[
h_{S_d}(y_d)
 \le \mathcal H_2(S_d\cap F_d(H))
 =\mathcal H_2(S\cap H).
\]
Taking the infimum over all closed halfspaces \(H\ni y\) proves
\[
h_{S_d}(y_d)\le h_S(y).
\]

For the reverse inequality, let \(K\) be any closed halfspace containing \(y_d\). Then \(F_d^{-1}(K)\) is a closed halfspace containing \(y\), and applying the same mass identity to \(F_d^{-1}(K)\) gives
\[
h_S(y)
 \le \mathcal H_2(S\cap F_d^{-1}(K))
 =\mathcal H_2(S_d\cap K).
\]
Taking the infimum over all closed halfspaces \(K\ni y_d\) proves
\[
h_S(y)\le h_{S_d}(y_d).
\]
Thus \(h_{S_d}(F_d(y))=h_S(y)\) for every \(y\in S\).

Finally, if \(h_S(y)\ge qT\), then \(y_d=F_d(y)\) satisfies
\[
h_{S_d}(y_d)=h_S(y)\ge qT=qT_d.
\]
Conversely, if \(h_{S_d}(y_d)\ge qT_d\), then \(y=F_{-d}(y_d)\) satisfies
\[
h_S(y)=h_{S_d}(y_d)\ge qT_d=qT.
\]
This proves the witness transformation and the equivalence in both directions.

## External sources

none
