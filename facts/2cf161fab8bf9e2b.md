---
fact_id: 2cf161fab8bf9e2b
kind: lemma
author: "mp_r84_two_cap_globalization"
assurance: LLM-verified
subgoal_id: canonical-root-tail-two-cap-allocation
depends_on: ["70dbfdc8fc4b6f51","f93a19566af88e9a"]
source_packet_sha256: d31bcc6595ec614e03792134afd6d9c2ad1c912a2e8e483ecea51334653bf624
verifier_run: c73468dd75cd46d0
target_match: null
---

## Statement

Use the six rays and sector names of accepted fact `f93a19566af88e9a`. In the cyclic notation of accepted fact `70dbfdc8fc4b6f51`, write
\[
(S_0,S_1,S_2,S_3,S_4,S_5)
=(A,B,C,D,E,F)=(O,N_y,W_y,P,W_x,N_x)
\]
and let \(R_i\) be the fan ray between \(S_{i-1}\) and \(S_i\), with indices modulo six. Let \(K\) be a two-dimensional convex polygon with \(0\in\operatorname{int}K\), and suppose at least one \(R_i\) meets a genuine vertex of \(K\).

Let \(L\) be the first derivative of the six sector areas with respect to arbitrary velocities of the genuine vertices. Define
\[
\begin{aligned}
h_x&=(1,0,0,0,1,1),\\
h_y&=(1,1,1,0,0,0),\\
h_t&=(0,0,1,1,1,0),
\end{aligned}
\qquad
\mathcal W=\operatorname{span}\{\mathbf1,h_x,h_y,h_t\}.
\]
Then
\[
\ker L^T\cap\mathcal W=\{0\}.                                    \tag{1}
\]

Consequently the pullbacks by \(L\) of
\[
\mathbf1,\qquad h_x-h_y,\qquad h_t
\]
are linearly independent. The same conclusion holds after omitting \(h_t\).

## Proof

No edge of \(K\) can lie on a fan ray, because the supporting line of such an edge would contain the interior point \(0\). Thus each fan ray meets the boundary either in the relative interior of one edge or at one genuine vertex.

Orient the genuine vertices \(Q_1,\ldots,Q_n\) counterclockwise and parametrize the edge \(Q_iQ_{i+1}\) by \(Q_i+t(Q_{i+1}-Q_i)\), \(0\le t\le1\). Split \((0,1)\) into its positive-length sector intervals \(I\). For a sector-weight vector
\[
\lambda=(\lambda_0,\ldots,\lambda_5),
\]
the edge coefficient calculation in accepted fact `70dbfdc8fc4b6f51` remains valid when a fan crossing is at an endpoint, because an endpoint has zero one-dimensional measure. Hence
\[
L^T\lambda=0
\]
is equivalent, on every edge, to
\[
\sum_I\lambda_{\sigma(I)}
\left(\int_I(1-t)\,dt,\int_I t\,dt\right)=0,                     \tag{2}
\]
where \(\sigma(I)\) is the sector containing the relative interior of the corresponding edge piece.

For two disjoint positive-length intervals \(I<J\), put
\[
m(I)=\left(\int_I(1-t)\,dt,\int_I t\,dt\right).
\]
Then
\[
\det(m(I),m(J))
=|I|\,|J|\,(\bar t_J-\bar t_I)>0.                               \tag{3}
\]
Thus any one or two of the moment columns are linearly independent. A supporting edge subtends an angle strictly less than \(\pi\) at \(0\), so it meets at most three fan rays and has at most four sector pieces. It follows from (2)-(3) that an edge block is possible only in either of the following situations:

1. every sector weight on the block is zero; or
2. at least three sector weights on the block are nonzero.

In particular, a one- or two-piece edge forces all its weights to vanish, a three-piece edge is either all zero or has three nonzero weights, and a four-piece mixed edge has exactly one zero weight.

Let \(r\ge1\) be the number of fan rays meeting vertices, and let \(k_i\) be the number of fan rays meeting the relative interior of the \(i\)-th edge. Every one of the six fan transitions occurs exactly once, so
\[
\sum_{i=1}^n k_i+r=6.                                            \tag{4}
\]
If all six components of a nonzero \(\lambda\in\ker L^T\) were nonzero, every edge would have \(k_i\ge2\). Since \(n\ge3\), (4) would give
\[
6-r=\sum_i k_i\ge2n\ge6,
\]
contrary to \(r\ge1\). Therefore every nonzero annihilator on an endpoint stratum has at least one zero component.

We now impose \(\lambda\in\mathcal W\) and give a complete incidence enumeration. The two defining relations of \(\mathcal W\) are
\[
\lambda_0-\lambda_1=\lambda_4-\lambda_3,\qquad
\lambda_2-\lambda_3=\lambda_0-\lambda_5.                         \tag{5}
\]
Equivalently, writing the first four components as \(a,b,c,d\),
\[
\lambda=(a,b,c,d,a-b+d,a-c+d).                                  \tag{6}
\]
Directly setting coordinates in (6) equal to zero shows that, up to cyclic relabeling and reversal, the exact zero set \(Z=\{i:\lambda_i=0\}\) is one of the seven rows below. The letters displayed as nonzero are restricted so that no further component vanishes.
\[
\begin{array}{c|c|c}
\text{type}&Z&\lambda\\ \hline
\mathrm{I}&\{0\}&(0,b,c,d,d-b,d-c)\\
\mathrm{II}&\{0,1\}&(0,0,c,d,d,d-c)\\
\mathrm{III}&\{0,2\}&(0,b,0,d,d-b,d)\\
\mathrm{IV}&\{0,3\}&(0,b,c,0,-b,-c)\\
\mathrm{V}&\{0,1,2\}&(0,0,0,d,d,d)\\
\mathrm{VI}&\{0,2,4\}&(0,b,0,b,0,b)\\
\mathrm{VII}&\{0,1,3,4\}&(0,0,c,0,0,-c).
\end{array}                                                       \tag{7}
\]
There are no other exact zero patterns: two zeros have cyclic separation one, two, or three; three zeros forced by (6) are either consecutive or alternating; four zeros leave one opposite pair; and five zeros force the sixth.

Write a four-piece edge block as the cyclic string of its sector indices. By (3), a mixed edge must contain exactly one member of \(Z\). Checking the six cyclic four-blocks against (7) gives the complete list
\[
\begin{array}{c|c}
\text{type}&\text{admissible mixed four-blocks}\\ \hline
\mathrm{I}&0123,\ 3450,\ 4501,\ 5012\\
\mathrm{II}&1234,\ 3450\\
\mathrm{III}&1234,\ 2345,\ 3450,\ 4501\\
\mathrm{IV}&1234,\ 2345,\ 4501,\ 5012\\
\mathrm{V}&2345,\ 3450\\
\mathrm{VI}&\text{none}\\
\mathrm{VII}&\text{none}.
\end{array}                                                       \tag{8}
\]
This table tracks an edge even when it contains both boundary transitions of one zero sector: those are precisely the coincident-stop blocks \(4501\) and \(5012\) in type I, and the corresponding blocks in types III-IV. A transition at a fan-ray vertex is not inside any block and is counted separately in (4).

We next exhaust the seven rows of (8). Throughout, an additional vertex in an open sector of nonzero weight would split that sector's boundary arc and create an edge with at most one crossing and a nonzero weight. Thus multiple vertices in one sector can occur only in a zero-weight sector. Likewise, an additional fan-ray vertex on a nonzero boundary path replaces an interior crossing by a vertex transition and strictly decreases the total number of interior crossings available to its incident edges.

**Type I: \(Z=\{0\}\).** There are two zero/nonzero transitions, \(50\) and \(01\).

First consider a coincident-stop edge. A block \(4501\) consumes the three transitions
\[
45,\quad50,\quad01,
\]
and a block \(5012\) consumes
\[
50,\quad01,\quad12.
\]
The complementary boundary path has the other three transitions. Since the coincident-stop edge contains the entire \(S_0\)-arc, the complementary path must contain at least two edges in order that the polygon have at least three genuine vertices. Every one of their sector weights is nonzero, so each edge needs at least two interior crossings. Three remaining transitions cannot supply two such edges. A further ray vertex only decreases the number of interior crossings. Hence coincident stop edges are impossible.

Suppose the two stops are distinct. If both are interior to edges, the two possible stop edges are \(0123\) and \(3450\). Their transition sets
\[
\{01,12,23\},\qquad\{34,45,50\}
\]
use all six transitions, leaving no ray vertex, contrary to the endpoint hypothesis.

If \(01\) lies in the edge \(0123\) and \(50\) is a ray-vertex transition, the only unused nonzero transitions are \(34,45\). They must lie on one edge with block \(345\); splitting that path or placing another ray vertex on it would leave an edge with at most one interior crossing. Thus the \(0123\) and \(345\) edges meet at one vertex in \(S_3\), while every other vertex lies in \(\overline{S_0}\). The case with \(3450\) and the ray transition \(01\) is symmetric.

If both stops are ray vertices \(R_0,R_1\), the four remaining transitions are
\[
12,\quad23,\quad34,\quad45.
\]
The nonzero boundary path needs at least two edges, because no edge can have four crossings. By (3), each needs at least two crossings. Hence the split is forced to be \(2+2\), with blocks \(123\) and \(345\), meeting at a unique vertex in \(S_3\). Any additional fan-ray vertex would change the available count from four to at most three and is impossible. Extra genuine vertices may occur only in \(S_0\).

Thus every endpoint incidence surviving type I has all but one vertices in \(\overline{S_0}\) and a unique vertex in the opposite open sector \(S_3\). This includes one ray stop, two ray stops, arbitrary internal vertices on the zero-weight \(S_0\)-chain, and all endpoint degenerations of the \(3+3\) incidence.

**Type II: \(Z=\{0,1\}\).** The only mixed stop edges are \(1234\) at the transition \(12\) and \(3450\) at \(50\). They both contain the transition \(34\), so they cannot both occur: a fan ray meets the boundary only once.

If one stop is mixed and the other is a ray vertex, then, besides the internal zero transition \(01\), exactly one nonzero transition remains. For example, \(1234\) together with the ray transition \(50\) leaves \(45\). The residual nonzero path has at most one crossing, contradicting (3). Additional ray vertices only split this path further.

If both stops are ray vertices \(R_0,R_2\), the zero chain accounts for the internal transition \(01\), and the complementary nonzero path has exactly the three transitions \(23,34,45\). It would have to be one four-piece edge \(2345\); two edges would require at least four crossings. But the angular arc from \(R_2\) to \(R_0\) through \(S_2,S_3,S_4,S_5\) is the complement of two adjacent fan sectors. Two adjacent sectors have total angle at most \(3\pi/4\), so this complementary arc has angle greater than \(\pi\). A supporting edge seen from \(0\in\operatorname{int}K\) has angular span strictly less than \(\pi\). This is impossible. Every internal transition of the zero chain and every possible additional ray vertex has now been counted.

**Type III: \(Z=\{0,2\}\).** The nonzero sector \(S_1\) is isolated between two zero sectors. It cannot contain two genuine vertices, because the edge between two consecutive such vertices lies wholly in \(S_1\) and has nonzero weight.

If there is one vertex in \(S_1\), neither incident edge can stop at \(R_1\) or \(R_2\), because that short edge would lie wholly in \(S_1\). Table (8) therefore forces the incoming block \(4501\) and the outgoing block \(1234\). Their transition sets are
\[
\{45,50,01\},\qquad\{12,23,34\},
\]
so they use all six transitions. Both remote endpoints lie in \(\overline{S_4}\). If they are distinct, the boundary chain joining them lies wholly in the nonzero sector \(S_4\), contradicting (3); if they coincide, the polygon has only two genuine vertices. There is no transition left for an additional fan-ray vertex. Thus type III is impossible.

It remains to check that the \(S_1\)-arc might have no open-sector vertex. If both \(R_1,R_2\) were vertices, the edge between them would have the single nonzero piece \(1\), which is impossible. If neither were a vertex, one edge would contain pieces from \(S_0,S_1,S_2\), hence at least two zero pieces and at most two nonzero pieces, again impossible by (3). Thus exactly one of \(R_1,R_2\) would have to be a vertex. If it is \(R_1\), the edge covering the \(S_1\)-arc is forced to be \(1234\), using \(12,23,34\). The complementary path from its endpoint in \(S_4\) back to \(R_1\) has only \(45,50,01\); before reaching \(R_1\) it ends in \(S_0\), so every unsplit closing edge has the three-piece block \(450\), with only two nonzero weights. Splitting it or placing an additional ray vertex creates still shorter forbidden blocks. The case with \(R_2\) and block \(4501\) is symmetric. Hence the no-open-vertex case is also impossible.

**Type IV: \(Z=\{0,3\}\).** For the isolated zero sector \(S_0\), either both boundary transitions \(50,01\) are ray vertices, or one coincident-stop edge handles both; by (8) that edge is \(4501\) or \(5012\). There is no mixed block handling only one of the two transitions. The same dichotomy holds for \(S_3\), with coincident blocks \(1234\) or \(2345\).

If both zero sectors use coincident-stop edges, the only disjoint transition-set pairs are
\[
\begin{aligned}
4501&:\{45,50,01\},&
1234&:\{12,23,34\},\\
5012&:\{50,01,12\},&
2345&:\{23,34,45\}.
\end{aligned}
\]
Each pair uses all six transitions and consists of two edges. Any third edge lies in a nonzero sector and violates (3). The two cross-pairs overlap respectively at \(45\) or \(12\), so they are impossible because a fan ray cannot cross two edges.

If one zero sector uses a coincident edge and the other uses two ray vertices, five transitions are already assigned. The remaining nonzero run has only one transition. For example, \(4501\) together with ray transitions \(23,34\) leaves \(12\). No nonzero boundary path can be formed with at most one crossing. If both zero sectors use ray vertices, four transitions are at vertices and the two nonzero runs retain only \(12\) and \(45\), again impossible. This covers coincident stops, all ray stops, and every possible additional ray vertex.

**Type V: \(Z=\{0,1,2\}\).** The two possible mixed stop edges \(2345\) and \(3450\) both contain transitions \(34,45\), so they cannot both occur.

If both outer transitions \(23,50\) are ray vertices, the complementary nonzero path has only transitions \(34,45\) and must be one edge \(345\). All genuine vertices then lie in the closed angular arc from \(R_0\) through \(S_0,S_1,S_2\) to \(R_3\). This arc has angle exactly \(\pi\).

If one outer transition is mixed and the other is a ray vertex, transition uniqueness forces the nonzero endpoint of the mixed edge to be that other ray vertex; otherwise a residual edge wholly in \(S_3,S_4\), or \(S_5\) has at most one crossing. All remaining edges are zero-weight edges inside \(S_0,S_1,S_2\), so again every genuine vertex lies in the same closed \(\pi\)-arc. Additional fan-ray vertices can occur only inside that zero chain and do not change this containment. A polygon whose vertex directions lie in a closed semicircle cannot contain \(0\) in its interior. Thus type V is impossible.

**Types VI and VII.** Table (8) has no mixed edge. Hence every zero/nonzero transition must occur at a fan-ray vertex. In type VI the three nonzero sectors are isolated. The boundary between the two ray vertices surrounding any one of them is either one edge with one nonzero sector piece or is split by a vertex into edges lying wholly in that nonzero sector. Both alternatives violate (3). In type VII the two nonzero sectors are isolated and the same argument applies. Extra ray vertices are already the prescribed zero/nonzero transitions, while extra vertices inside a nonzero sector only create further forbidden zero-crossing edges. Thus both types are impossible.

The enumeration (7)-(8) and the seven cases above prove that the only possible endpoint incidence for a nonzero vector in \(\mathcal W\cap\ker L^T\) is the type-I opposite-sector configuration: all but one vertices lie in one closed sector, the remaining vertex lies in the opposite open sector, and at least one endpoint of the multi-vertex chain lies on a fan ray.

It remains to exclude that configuration using the \(3+3\) calculation from accepted fact `70dbfdc8fc4b6f51`. Relabel the opposite sectors so that the unique vertex is in \(A\) and all remaining vertices are in \(\overline D\). Edges within \(D\) force \(\lambda_D=0\), while exact type I gives \(\lambda_A\ne0\); normalize \(\lambda_A=1\). Because \(0\) is interior, the unique vertex is in the open sector \(A\), and the two crossing sides meet \(\overline D\) on opposite sides of the ray through \(-A\).

Use the notation of equations (14)-(15) of `70dbfdc8fc4b6f51`. The unique vertex gives \(0<\theta<1\). On one crossing side one has \(X>Y\ge0\), and on the other \(Y'>X'\ge0\). Equality at \(Y=0\) or \(X'=0\) is exactly a chain endpoint on a fan ray. The quantities
\[
R=\frac{1+Y}{X-Y},\qquad Q=\frac{1+X'}{Y'-X'}
\]
remain finite and strictly positive, and the same two edge-moment computations give
\[
\begin{aligned}
\lambda_B&=-\frac{R^2+2R+\theta}{1-\theta},
&\lambda_C&=\frac{R^2}{\theta},\\
\lambda_F&=-\frac{Q^2+2Q+1-\theta}{\theta},
&\lambda_E&=\frac{Q^2}{1-\theta},
\end{aligned}                                                     \tag{9}
\]
with \(\lambda_D=0\). The endpoint substitutions are legitimate directly in (9); no limiting division vanishes.

Every vector in \(\mathcal W\) satisfies
\[
\lambda_A-\lambda_B=\lambda_E-\lambda_D,\qquad
\lambda_C-\lambda_D=\lambda_A-\lambda_F.
\]
Substitution of (9) gives
\[
Q^2=(R+1)^2,\qquad R^2=(Q+1)^2.
\]
Since \(R,Q>0\), these say \(Q=R+1\) and \(R=Q+1\), a contradiction. Hence the type-I survivor is also impossible, proving (1).

Finally, suppose
\[
L^T\bigl(\alpha\mathbf1+\beta(h_x-h_y)+\gamma h_t\bigr)=0.
\]
The vector in parentheses lies in \(\mathcal W\), so (1) makes it zero. The three displayed sector vectors are linearly independent, hence \(\alpha=\beta=\gamma=0\). This proves the asserted constraint qualification, and omitting \(h_t\) gives the two-constraint version.

## External sources

none
