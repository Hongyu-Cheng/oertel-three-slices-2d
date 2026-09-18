---
fact_id: f8cf62cef1390fac
kind: counterexample
author: "mp_r147_opposite_a2_realization"
assurance: LLM-verified
subgoal_id: opposite-survivor-full-a2-realization
depends_on: ["18e8f69f5a782c16","fa0e57b225178b3b"]
source_packet_sha256: 90b73d567e75a7d6b583310b7c2e2b5122de223a44549b02b416126d10c2b06c
verifier_run: 57666d3bc8e049c6
target_match: null
---

## Statement

Keep every rational datum of accepted fact `18e8f69f5a782c16` fixed.
In particular,
\[
\Delta=1,\qquad \delta=76,\qquad S=\delta+2=78,
\]
and the \(A_2\) cell areas are
\[
\begin{array}{c|cccc}
 &Q_j&Q_{jk}&Q_N&Q_{k\ell}\\ \hline
|\cdot|&\dfrac1{200}&\dfrac{12101}{8000}&8&\dfrac1{10000}.
\end{array}
\]
In the notation of accepted fact `fa0e57b225178b3b`, put
\[
W:=-q_j=78-U+V.
\]
The four cells, including their boundary closures, are assigned as
\[
\begin{array}{c|ccc}
Q_j&U\leq0&V\geq0&W\geq0\\
Q_{jk}&U\geq0&V\geq0&W\geq0\\
Q_N&U\geq0&V\leq0&W\geq0\\
Q_{k\ell}&U\geq0&V\leq0&W\leq0.
\end{array}
\]
The three prescribed sections are
\[
\begin{aligned}
U=0:&\quad V\in\left[8,\frac{161}{20}\right],
&&J_2=\lambda_{2k}=\frac1{20},\\
V=0:&\quad U\in\left[\frac{14}{3},5\right],
&&H_2=\lambda_{2\ell}=\frac13,\\
W=0:&\quad (U,V)=(78-t,-t),\quad
t\in\left[46,\frac{23001}{500}\right],
&&K_2=\lambda_{2j}=\frac1{500}.
\end{aligned}
\]
Thus the fixed offsets are
\[
u=\frac{14}{3},\qquad v=8,\qquad w_0=46,\qquad
\theta=73,\qquad \psi=\frac{15999}{500}.
\]

Define \(A_2\) to be the convex polygon with the following vertices in
clockwise order:
\[
\begin{array}{c|cc}
i&(z_i)_U&(z_i)_V\\ \hline
1&0&8\\
2&-1/5&167/20\\
3&0&161/20\\
4&1&387703/60000\\
5&5&0\\
6&10&-5737/675\\
7&32&-46\\
8&8009/250&-5758/125\\
9&15999/500&-23001/500\\
10&14/3&0.
\end{array}
\]
This is a compact two-dimensional rational strictly convex polygon.
Its three full sections and four cell areas are exactly the data above.

## Proof

For cyclic indices, set
\[
D_i=\det(z_i-z_{i-1},z_{i+1}-z_i).
\]
Direct substitution gives
\[
\begin{array}{c|rrrrrrrrrr}
i&1&2&3&4&5&6&7&8&9&10\\ \hline
D_i&
-1/30&
-1/100&
-5297/300000&
-1303/12000&
-182353/108000&
-13/25&
-1087/18750&
-1/5000&
-803/15000&
-2981/750.
\end{array}
\]
Every turn is strict and clockwise.  For a direct supporting-edge
check, let
\[
m_i=\max_{k\notin\{i,i+1\}}
\det(z_{i+1}-z_i,z_k-z_i).
\]
The ten exact maxima are
\[
\begin{array}{c|rrrrrrrrrr}
i&1&2&3&4&5&6&7&8&9&10\\ \hline
m_i&
-1/100&
-1/100&
-5297/300000&
-1303/12000&
-13/25&
-1087/18750&
-1/5000&
-1/5000&
-803/15000&
-1/30.
\end{array}
\]
They are all negative.  Hence every other vertex lies strictly to the
right of each directed edge \(z_i z_{i+1}\), so the listed decagon is
strictly convex and has the stated cyclic order.

The values of the three cutting affine functions at all vertices are
\[
\begin{array}{c|ccc}
i&U(z_i)&V(z_i)&W(z_i)\\ \hline
1&0&8&86\\
2&-1/5&167/20&1731/20\\
3&0&161/20&1721/20\\
4&1&387703/60000&5007703/60000\\
5&5&0&73\\
6&10&-5737/675&40163/675\\
7&32&-46&0\\
8&8009/250&-5758/125&-1/10\\
9&15999/500&-23001/500&0\\
10&14/3&0&220/3.
\end{array}
\]
Consequently, \(U=0\) meets the boundary only at \(z_1,z_3\),
\(V=0\) meets it only at \(z_5,z_{10}\), and \(W=0\) meets it only at
\(z_7,z_9\).  Convexity now gives the full sections
\[
A_2\cap\{U=0\}=[z_1,z_3]
=\left\{(0,V):8\leq V\leq\frac{161}{20}\right\},
\]
\[
A_2\cap\{V=0\}=[z_{10},z_5]
=\left\{(U,0):\frac{14}{3}\leq U\leq5\right\},
\]
and
\[
A_2\cap\{W=0\}=[z_7,z_9]
=\left\{(78-t,-t):
46\leq t\leq\frac{23001}{500}\right\}.
\]
These endpoints give the prescribed lengths \(J_2=1/20\),
\(H_2=1/3\), and \(K_2=1/500\) exactly.

The sign table also gives the four closed cell polygons, in clockwise
order:
\[
\begin{array}{c|l}
Q_j&(z_1,z_2,z_3)\\
Q_{jk}&(z_3,z_4,z_5,z_{10},z_1)\\
Q_N&(z_5,z_6,z_7,z_9,z_{10})\\
Q_{k\ell}&(z_7,z_8,z_9).
\end{array}
\]
For a cyclic polygon \(P=(p_1,\ldots,p_r)\), write
\[
\Sigma(P)=\sum_{i=1}^r
\bigl((p_i)_U(p_{i+1})_V-(p_i)_V(p_{i+1})_U\bigr).
\]
Exact shoelace substitution gives
\[
\begin{array}{c|cc}
P&\Sigma(P)&|P|=-\Sigma(P)/2\\ \hline
Q_j&-1/100&1/200\\
Q_{jk}&-12101/4000&12101/8000\\
Q_N&-16&8\\
Q_{k\ell}&-1/5000&1/10000\\
A_2&-380709/20000&380709/40000.
\end{array}
\]
Since \(\Delta=1\), these coordinate areas are the prescribed physical
areas.  Their sum is
\[
\frac1{200}+\frac{12101}{8000}+8+\frac1{10000}
=\frac{380709}{40000}=|A_2|.
\]
The first two cells meet along \([z_1,z_3]\), the middle two meet along
\([z_{10},z_5]\), and the last two meet along \([z_7,z_9]\).  Their
interiors are disjoint by the strict signs in the table.  The three
cutting lines have no intersection in \(A_2\), because their pairwise
intersections are \((0,0)\), \((0,-78)\), and \((78,0)\), none of
which belongs to the corresponding full section.  Hence the four
polygons partition the decagon, and no unsupported sign cell occurs.

## External sources

none
