---
fact_id: 91cb5bfc71da49ac
kind: lemma
author: "mp_r31_no_opposite"
assurance: LLM-verified
subgoal_id: canonical-no-opposite-pair
depends_on: ["0e51a47a9add571f"]
source_packet_sha256: 20986957b28bbde6974c3c87c875f0b5e8f8cd91585af04d6e4e36c656210d22
verifier_run: defdf35197d54bb9
target_match: null
---

## Statement

Let \(N=\{1,2,3\}\). Under the hypotheses and exact-cell convention of accepted fact `0e51a47a9add571f`, put
\[
q_i=f_i+L_i,\qquad
q_H=|Q_H|,\qquad
m=|A_2|,
\]
so that
\[
q_1+q_2+q_3=-\sigma
\]
for some \(\sigma>0\). Put
\[
v_i=\sum_{H\ni i}q_H.
\]
Assume the finite-interior conditions
\[
0<v_i<m\qquad(i=1,2,3)
\]
and the no-opposite-pair conditions
\[
q_{\{i\}}q_{N\setminus\{i\}}=0
\qquad(i=1,2,3).
\]
Then the positive-area support
\[
\mathcal S_Q=\{H\subseteq N:q_H>0\}
\]
is exactly one of
\[
\mathcal S_{jk}
=
\{N,\{j\},\{k\},\{j,k\}\},
\qquad
\{j,k,\ell\}=N,
\tag{1}
\]
or
\[
\mathcal S_{\mathrm{dbl}}
=
\{N,\{1,2\},\{1,3\},\{2,3\}\}.
\tag{2}
\]
Every support in (1)-(2) is realizable by a nonempty two-dimensional convex polytope for the same affine-plane sign arrangement.

Let \(p_J,r_G\) be the other exact-cell areas, let
\[
M=\sum_Jp_J,\qquad k=\sum_Gr_G,
\]
and put
\[
u_i=\sum_{J\ni i}p_J,\qquad
c_i=\sum_{G\ni i}r_G,
\]
\[
E_R=\sum_{|G|=2}r_G+2r_N.
\]
Define
\[
E_Q=
\begin{cases}
q_{\{j,k\}}+2q_N,&\mathcal S_Q=\mathcal S_{jk},\\[2mm]
m+q_N,&\mathcal S_Q=\mathcal S_{\mathrm{dbl}}.
\end{cases}
\tag{3}
\]
Define
\[
W:=
\sum_J(3|J|-2)p_J
+\sum_H(3|H|-2)q_H
+\sum_G(3|G|-2)r_G.
\]
Then
\[
W=
3\left(\sum_{i=1}^3u_i+E_Q+E_R\right)
-(2M-m-k).
\tag{4}
\]
Consequently the one remaining geometric inequality for the entire realizable no-opposite family is
\[
\sum_{i=1}^3u_i+E_Q+E_R
>
\frac{2M-m-k}{3}.
\tag{5}
\]
For support (1), this is
\[
\sum_i u_i+q_{\{j,k\}}+2q_N
+\sum_{|G|=2}r_G+2r_N
>
\frac{2M-m-k}{3};
\tag{6}
\]
for support (2), it is
\[
\sum_i u_i+m+q_N
+\sum_{|G|=2}r_G+2r_N
>
\frac{2M-m-k}{3}.
\tag{7}
\]
Thus (5) is exactly equivalent to \(W>0\). Under the three crossing equalities
\[
u_i+v_i+c_i=\frac{2(M+m+k)}9,
\]
their sum gives equality in (5), so proving the strict geometric inequality contradicts the finite-interior branch.

## Proof

Accepted fact `0e51a47a9add571f` shows that the affine sign map identifies the plane with
\[
q_1+q_2+q_3=-\sigma,
\qquad \sigma>0,
\]
and that \(Q_\varnothing\) is empty. After the affine normalization
\[
x=\frac{q_1}{\sigma},\qquad y=\frac{q_2}{\sigma},
\qquad \frac{q_3}{\sigma}=-1-x-y,
\]
the seven strict chambers have adjacency graph consisting of the outer cycle
\[
\{3\},\{1,3\},\{1\},\{1,2\},\{2\},\{2,3\}
\tag{8}
\]
and the central chamber \(N\), which is adjacent precisely to the three doubleton chambers.

The subgraph induced by \(\mathcal S_Q\) is connected. Indeed, positive cell area is equivalent, up to the null cutting lines, to \(\operatorname{int}A_2\) meeting the corresponding strict chamber. Given points of \(\operatorname{int}A_2\) in two supported chambers, their segment lies in \(\operatorname{int}A_2\). Successive chambers along the segment are adjacent. If the segment passes through the intersection of two cutting lines, openness of \(\operatorname{int}A_2\) supplies a ball about that intersection, so all required intervening adjacent chambers also have positive area. Three cutting lines cannot meet because their coordinate sum is \(-\sigma\ne0\).

Suppose first that \(N\notin\mathcal S_Q\). Connectivity places \(\mathcal S_Q\) in a consecutive path of the outer cycle (8). The no-opposite conditions forbid two vertices at distance three, so this path has at most three vertices. Every such path is contained in one of the alternating triples
\[
\{\{j\},\{j,k\},\{k\}\},
\qquad
\{\{j,k\},\{j\},\{j,\ell\}\}.
\]
In the first triple, the remaining coordinate \(\ell\) is absent from every index, so \(v_\ell=0\). In the second, \(j\) belongs to every index, so \(v_j=m\). Both contradict \(0<v_i<m\). Hence
\[
N\in\mathcal S_Q.
\tag{9}
\]

Let \(\mathcal D\) and \(\mathcal T\) be the supported doubletons and singletons. If \(|\mathcal D|=0\), connectivity with the central vertex forces \(\mathcal T=\varnothing\), contradicting properness. If
\[
\mathcal D=\{\{j,k\}\},
\]
the opposite-pair condition excludes \(\{\ell\}\), while connectivity permits only \(\{j\}\) and \(\{k\}\). Properness in coordinate \(j\) forces \(\{k\}\), and properness in coordinate \(k\) forces \(\{j\}\). Thus the support is exactly (1).

If two doubletons are supported, write them as \(\{j,k\}\) and \(\{j,\ell\}\). Their opposite singleton exclusions leave at most \(\{j\}\). Every remaining supported cell contains \(j\), including \(N\), so \(v_j=m\), a contradiction. If all three doubletons are supported, every singleton is excluded by its opposite doubleton. Each coordinate is omitted by its complementary doubleton, so all three caps remain proper. This gives exactly (2). The classification is exhaustive.

It remains to verify realizability rather than merely Boolean consistency. In normalized coordinates, for (1) with \((j,k,\ell)=(1,2,3)\), take
\[
Q^{(1)}
=
\operatorname{conv}\left\{
\left(-2,\frac1{10}\right),
\left(\frac1{10},-2\right),
\left(-\frac1{10},-\frac1{10}\right)
\right\}.
\tag{10}
\]
Its three side inequalities include
\[
2x+19y\le-\frac{21}{10},
\qquad
19x+2y\le-\frac{21}{10}.
\]
If \(x+y\ge-1\), then \(x\ge0\) would imply
\[
19x+2y=17x+2(x+y)\ge-2,
\]
contradicting the second side inequality. Similarly \(y\ge0\) contradicts the first. Hence the part with \(q_3\le0\) lies entirely in \(Q_N\). On the part with \(q_3>0\), one cannot have both \(x,y>0\), so only \(Q_1,Q_2,Q_{12}\) occur. The first two vertices lie strictly in \(Q_1,Q_2\), the third lies strictly in \(Q_N\), and the centroid lies strictly in \(Q_{12}\). Thus the exact positive support is
\[
\{N,\{1\},\{2\},\{1,2\}\}.
\]
Permuting coordinates realizes the other two supports in (1).

For (2), take
\[
Q^{(2)}
=
\operatorname{conv}\left\{
\left(-\frac35,-\frac35\right),
\left(-\frac35,\frac1{10}\right),
\left(\frac1{10},-\frac35\right)
\right\}.
\tag{11}
\]
This triangle satisfies
\[
x\ge-\frac35,\qquad
y\ge-\frac35,\qquad
x+y\le-\frac12.
\]
If \(x>0\), then \(y<0\) and \(x+y>-1\), giving \(Q_{23}\); if \(y>0\), one obtains \(Q_{13}\). If \(x+y<-1\), both \(x,y<0\), giving \(Q_{12}\). The remaining strict interior points lie in \(Q_N\). The three vertices lie strictly in the three doubletons, and the centroid lies strictly in \(Q_N\). Hence (11) has exactly support (2). Taking inverse images under the affine sign map realizes all these examples in the original plane.

Finally,
\[
\sum_H(3|H|-2)q_H
=
3\sum_i v_i-2m
=
m+3\left(\sum_i v_i-m\right).
\]
For support (1),
\[
\sum_i v_i-m=q_{\{j,k\}}+2q_N,
\]
while for support (2),
\[
\sum_i v_i-m=m+q_N.
\]
Thus this excess is exactly \(E_Q\) in (3). Likewise,
\[
\sum_G(3|G|-2)r_G=k+3E_R,
\qquad
\sum_J(3|J|-2)p_J=3\sum_i u_i-2M.
\]
Adding these identities proves (4), and hence the equivalence of \(W>0\) with (5). Summing the three crossing equalities gives
\[
\sum_i u_i+(m+E_Q)+(k+E_R)
=\frac{2(M+m+k)}3,
\]
which rearranges to equality in (5). This identifies (5), with the two exact specializations (6)-(7), as the sole remaining geometric inequality.

## External sources

none
