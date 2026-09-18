---
fact_id: cfe3be7ab46f8b38
kind: counterexample
author: "/root/mp_r43_triangle_cevian"
assurance: LLM-verified
subgoal_id: canonical-all-double-complete-partial-union
depends_on: ["0365c0b3a49d468d","0819231d0af83197","2bb72698f0248a65","624b129b68e0fdee","8234d1112ec2f031","91cb5bfc71da49ac","93f1cefaa4795a25","b530304a83fe1e51","ce343e749df349fe","d59ea5516caf527d","d7bdfc054d5093e8","e1361027c1dda6fa"]
source_packet_sha256: 05ce83c6766bc1eb12442e6ccaaeb2355dc04919f14579df1240db15aa9dd10a
verifier_run: 7e97ef389113459f
target_match: null
---

## Statement

Let
\[
S_{\rm dbl}=\{12,13,23,123\}
\]
be the positive \(Q\)-cell support. For positive-area source partial unions, the inequality in the round statement is valid despite their open faces. Among all 520 labeled source pairs that can have positive area after the all-double \(Q\)-zeros are substituted, there are 292 distinct literal source-target triples. Under source enlargement and target shrinking, their 19 inclusion-undominated members form the following six \(S_3\)-orbits. Here \(\{i,j,k\}=N\) and \(x_i=q_{N\setminus\{i\}}\):
\[
\frac14(\sqrt M+\sqrt m)^2\le k, \tag{1}
\]
\[
\frac14(\sqrt{u_i}+\sqrt{v_i})^2\le c_i, \tag{2}
\]
\[
\frac14(\sqrt{M-u_i}+\sqrt{x_i})^2\le k-c_i, \tag{3}
\]
\[
\frac14(\sqrt{p_{ij}}+\sqrt{x_k+q_{123}})^2
\le r_{ij}+r_{123}, \tag{4}
\]
\[
\frac14(\sqrt{p_{ij}}+\sqrt{x_k})^2\le r_{ij}, \tag{5}
\]
\[
\frac14(\sqrt{p_j+p_{ij}}+\sqrt{x_k})^2
\le r_j+r_{ij}. \tag{6}
\]
The multiplicities are respectively \(1,3,3,3,3,6\).

The literal target set from accepted fact `b530304a83fe1e51` is the exact point-incidence target. It is not the smallest area target once the known zero \(Q\)-cells are used. The support-aware target is
\[
\mathcal T_{\rm dbl}(A,B,C,D)
=
\left\{
G\ne\varnothing:
\begin{array}{l}
\exists J\in\mathcal P(A,B),\
\exists H\in\mathcal Q(C,D)\cap S_{\rm dbl},\\
J\cap H\subseteq G\subseteq J\cup H
\end{array}
\right\}. \tag{7}
\]
Using (7) gives 253 distinct triples and 22 inclusion-undominated members in seven \(S_3\)-orbits. The only additional orbit is
\[
\frac14(\sqrt{p_{ij}}+\sqrt m)^2\le k-r_k,
\qquad \{i,j,k\}=N. \tag{8}
\]

Assign every unlisted mass zero and set
\[
p_\varnothing=\frac{121}{10},
\qquad p_1=p_2=p_3=\frac15, \tag{9}
\]
\[
q_{123}=\frac25,
\qquad q_{12}=q_{13}=q_{23}=\frac15, \tag{10}
\]
\[
r_1=r_2=r_3=\frac{19}{10},
\qquad r_{12}=r_{13}=r_{23}=1,
\qquad r_{123}=\frac1{10}. \tag{11}
\]
This is an exact scalar counterexample to any claimed contradiction from the complete literal system. More strongly, it satisfies all partial-union inequalities after every zero \(P\)- and \(Q\)-cell in (9)-(10) is used to shrink the area target.

## Proof

Fix source partial unions
\[
X=P[A;B],\qquad Y=Q[C;D]
\]
of positive area, and put
\[
Z=\bigsqcup_{G\in\mathcal T(A,B,C,D)}R_G.
\]
Each source is a bounded convex set obtained from a polytope by finitely many weak or strict affine inequalities. Consequently
\[
|\overline X|=|X|,\qquad |\overline Y|=|Y|, \tag{12}
\]
because the added sets lie in finitely many cutting lines and polytope boundary edges. Boundedness also gives
\[
\frac{\overline X+\overline Y}{2}
=
\overline{\frac{X+Y}{2}}. \tag{13}
\]
Indeed, the right side is contained in the compact set on the left, while approximating each point of \(\overline X\) and \(\overline Y\) by source points proves the reverse inclusion.

The exact incidence statement of `b530304a83fe1e51` and (13) give
\[
\frac{\overline X+\overline Y}{2}\subseteq\overline Z. \tag{14}
\]
Closing a finite union of exact sign cells adds only portions of the cutting lines and the boundary of \(K\). Hence
\[
|\overline Z|
=|Z|
=\sum_{G\in\mathcal T(A,B,C,D)}r_G. \tag{15}
\]
Applying planar Brunn--Minkowski as supplied by accepted fact
`d7bdfc054d5093e8` to the compact convex sets
\(\overline X,\overline Y\), then using (12), (14), and (15), proves
\[
\frac14(\sqrt{|X|}+\sqrt{|Y|})^2
\le
\sum_{G\in\mathcal T(A,B,C,D)}r_G. \tag{16}
\]

The positive-area convention in the round statement is exact for a scalar system. If one source has area zero, its area alone does not distinguish a literally empty partial union from a nonempty segment or point. With an empty source and a positive other source, the scalar version of (16) can fail. If nonemptiness is certified separately, Brunn--Minkowski applies to the closures and (16) remains valid. If both source areas vanish, (16) has zero left side and is harmless.

The set \(\mathcal T(A,B,C,D)\) remains the exact literal target: `b530304a83fe1e51` proves both its formula and sharpness for every listed cell. In the all-double branch, however, the union of the exact \(Q_H\) with
\[
H\in\mathcal Q(C,D)\cap S_{\rm dbl}
\]
has full area in \(Y\). When \(|Y|>0\), this full-measure subset is dense in the convex set \(Y\). Repeating (13)-(15) with that dense subset proves (16) with the smaller target (7). For a fixed scalar table, the same argument also restricts \(J\) to the cells with \(p_J>0\). Thus (7) does not alter exact point incidence; it removes target cells reached only through zero-area source strata.

For completeness, the finite reduction is an exact Boolean enumeration, not a numerical optimization. Encode each partial sign condition by a word in
\(\{\le0,>0,*\}^3\). There are \(3^3-1=26\) non-forced \(P\)-words and 26 non-forced \(Q\)-words. Exactly 20 \(Q\)-words meet \(S_{\rm dbl}\), giving \(26\cdot20=520\) labeled pairs. For each pair, form
\[
\mathcal P(A,B),\qquad
\mathcal Q(C,D)\cap S_{\rm dbl},
\]
and form either the literal target of `b530304a83fe1e51` or (7). Deleting identical triples gives respectively 292 and 253 triples.

One triple dominates another when both of its source cell sets contain the corresponding source cell sets of the other triple and its target cell set is contained in the other's target cell set, with at least one strict containment. Source-area monotonicity and target-area monotonicity then make its inequality stronger. The complete lists of undominated source and target cell sets, up to relabeling, are
\[
\begin{array}{c|c|c}
\text{\(P\)-cells}&\text{positive \(Q\)-cells}&\text{target \(R\)-cells}\\ \hline
\{0,1,2,3,12,13,23\}&\{12,13,23,123\}
 &\{1,2,3,12,13,23,123\}\\
\{1,12,13\}&\{12,13,123\}&\{1,12,13,123\}\\
\{0,1,2,12\}&\{12\}&\{1,2,12\}\\
\{12\}&\{12,123\}&\{12,123\}\\
\{12\}&\{12\}&\{12\}\\
\{1,12\}&\{12\}&\{1,12\}.
\end{array} \tag{17}
\]
Their orbit sizes are \(1,3,3,3,3,6\), and their area forms are exactly (1)-(6). With the support-aware target, the sole new row is
\[
\{12\},\qquad
\{12,13,23,123\},\qquad
\{1,2,12,13,23,123\}, \tag{18}
\]
whose three relabelings give (8). This proves the asserted exhaustion and dominance reduction. In particular, accepted fact `d59ea5516caf527d` is precisely orbit (3).

The symmetric family in accepted fact `0365c0b3a49d468d` also survives the audit. Its positive \(P\)-support is
\[
S_P=\{\varnothing,1,2,3\}.
\]
If both this support and \(S_{\rm dbl}\) are used in the dense-source reduction, the 121 distinct source-target triples have 13 undominated members in four orbits: (1), (2), (3), and (6). For an inequality with source areas \(P,Q\) and target area \(R\), set
\[
D=4R-P-Q.
\]
It is enough and necessary that
\[
D\ge0,\qquad D^2-4PQ\ge0. \tag{19}
\]
For the global orbit of that family,
\[
P=\frac{70+187\delta}{20},\quad Q=1,\quad
R=\frac{91\delta}{10},\quad
D=\frac{541\delta-90}{20},
\]
and
\[
400(D^2-4PQ)
=292681\delta^2-112340\delta+2500>0
\qquad(\delta\ge1). \tag{20}
\]
For orbit (3),
\[
P=\frac{66+187\delta}{20},\quad Q=\frac15,\quad
R=5\delta,\quad
D=\frac{213\delta-70}{20},
\]
and
\[
400(D^2-4PQ)
=45369\delta^2-32812\delta+3844>0
\qquad(\delta\ge1). \tag{21}
\]
Both quadratics are positive at \(\delta=1\) and strictly increasing thereafter. The remaining two orbit inequalities reduce to
\[
\frac9{20}\le\frac{41\delta}{10},
\qquad
\frac15\le3\delta. \tag{22}
\]
Thus the entire accepted family, not merely one sample, satisfies every literal and support-aware partial-union inequality.

It remains to verify the stricter rational table (9)-(11). Its totals and cap sums are
\[
M=\frac{127}{10},\qquad m=1,\qquad k=\frac{44}{5},
\]
\[
u_i=\frac15,\qquad v_i=\frac45,\qquad c_i=4,\qquad
h=\frac{2(M+m+k)}9=5. \tag{23}
\]
Therefore all crossings hold. The tail conditions of accepted fact
`624b129b68e0fdee` hold because the left tails satisfy \(c_i+m=h\)
and the right tails are strict. Also
\[
0<u_i<M,\qquad0<v_i<m,\qquad0<h<M.
\]

Put
\[
U=\sum_i u_i=\frac35,\qquad
E_R=r_{12}+r_{13}+r_{23}+2r_{123}=\frac{16}{5}.
\]
The all-double excess identity of accepted fact `91cb5bfc71da49ac`
is checked exactly by
\[
U+m+q_{123}+E_R
=\frac{26}{5}
=\frac{2M-m-k}{3}. \tag{24}
\]
Hence \(W=0\). The defect identity of accepted fact
`0819231d0af83197` is also exact:
\[
2M+2m-3\sum_i(u_i+v_i)-k
=\frac{48}{5}
=3E_R. \tag{25}
\]

For the three \(Q\)-caps, the two conditions of accepted fact
`8234d1112ec2f031` are
\[
q_{123}^2m-4q_{12}q_{13}q_{23}
=\frac{16}{125}>0,
\qquad
\sum_i\sqrt{\frac{x_i}{m}}=\frac3{\sqrt5}<\frac32. \tag{26}
\]
The analogous source-cap inequalities for \(P\) are also strict:
\[
p_\varnothing^2M-4p_1p_2p_3=\frac{14875}{8}>0,
\qquad
\sum_i\sqrt{\frac{p_i}{M}}
=3\sqrt{\frac2{127}}<\frac32. \tag{27}
\]

For the overlap-corrected inequality of accepted fact
`2bb72698f0248a65`, the right side is
\[
k-r_{123}+\sum_i r_i=\frac{72}{5},
\]
whereas its left side is
\[
\frac34\left(\sqrt{\frac{121}{10}}+\frac1{\sqrt5}\right)^2
=\frac{369}{40}+\frac{33\sqrt2}{20}
<\frac{72}{5}. \tag{28}
\]
The last inequality follows from \(66\sqrt2<207\).

All double \(R\)-cells and \(r_{123}\) are positive, so the support implication of `93f1cefaa4795a25` holds. For the corrected middle caps of `ce343e749df349fe`,
\[
e_i=\left(\frac{19}{10}-\frac{1\cdot1}{1/10}\right)_+=0, \tag{29}
\]
so both middle-cap inequalities hold. Finally,
\[
\left(\sum_i\sqrt{r_i+\frac{2r_{123}}9}\right)^2
=\frac{173}{10}
<\frac{88}{5}=2k, \tag{30}
\]
and
\[
\left(\sum_i\sqrt{r_i}\right)^2
=\frac{171}{10}
<\frac{88}{5}. \tag{31}
\]
Thus both inequalities of `e1361027c1dda6fa` hold strictly.

For a final exact check of every partial-union inequality, use the actual positive supports
\[
S_P=\{\varnothing,1,2,3\},\qquad
S_Q=S_{\rm dbl}.
\]
The dense-source enumeration has 121 distinct structural triples and 13 inclusion-undominated ones in four orbits. Their source and target areas, together with the certificate (19), are
\[
\begin{array}{c|c|c|c|c}
\text{orbit}&P&Q&R&D&D^2-4PQ\\ \hline
\text{global}&127/10&1&44/5&43/2&8229/20\\
\text{cap}&1/5&4/5&4&15&5609/25\\
\text{complement}&25/2&1/5&24/5&13/2&129/4\\
\text{ordered}&1/5&1/5&29/10&56/5&3132/25.
\end{array} \tag{32}
\]
Every entry in the last two columns is positive. Dominance therefore proves every one of the 121 support-aware structural inequalities, hence all 400 positive-source labeled literal inequalities for this table. Equations (23)-(32) verify every other listed scalar constraint. The table is deliberately claimed only as a scalar calibration; the argument gives no common-plane realization.

## External sources

none
