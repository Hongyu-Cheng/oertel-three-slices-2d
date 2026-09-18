---
fact_id: 46afc7eb815ffc5b
kind: lemma
author: "mp_r34_sign_pruning"
assurance: LLM-verified
subgoal_id: canonical-support-affine-sign-pruning
depends_on: ["b046e3066136e781"]
source_packet_sha256: b4fa8546353e195651b1d740b65c5b36079b29f6958a8d49740e1a4fd79ccdbd
verifier_run: f32b3ac38bbb45f7
target_match: null
---

## Statement

Use the notation and system family \(\mathcal S_{\eta,\tau_Q,\tau_R,\sigma}\) of accepted fact `b046e3066136e781`.

For one body \(E\), at an endpoint with support coordinate \(x\), put
\[
a=-L_E(x),\qquad b=-U_E(x).
\]
Then \(b\le a\), and the four endpoint values in positions \(1,2,3,4\) are
\[
(a,b,x-b,x-a).
\]
A sign state is the four-character string
\[
\operatorname{sgn}(a)\operatorname{sgn}(b)
\operatorname{sgn}(x-b)\operatorname{sgn}(x-a),
\]
where each character is \(+\), \(0\), or \(-\).

The complete state sets according to the sign of \(x\) are
\[
\begin{aligned}
\mathcal V_-=\{&
++--,+-+-,+---,+-0-,+0--,\\
&--++,--+-,--+0,----,--0-,--00,\\
&0-+-,0---,0-0-,00--\},\\
\mathcal V_0=\{&
++--,+-+-,+00-,--++,0-+0,0000\},\\
\mathcal V_+=\{&
++++,+++-,+++0,++--,++0-,++00,\\
&+-++,+-+-,+-+0,+0++,+0+-,+0+0,\\
&--++,0-++,00++\}.
\end{aligned}
\]
The states that force zero endpoint height \(a-b=0\) are exactly
\[
\mathcal Z_-=\{--00,00--\},\qquad
\mathcal Z_0=\{0000\},\qquad
\mathcal Z_+=\{++00,00++\}.
\]
Every state outside the corresponding \(\mathcal Z_\epsilon\) has a realization with \(a>b\).

For endpoint signs \(s,t\in\{-,0,+\}\), define
\[
\lambda(s,t)=
\begin{cases}
\mathrm C_+,&s=-,\ t=+,\\
\mathrm C_-,&s=+,\ t=-,\\
\mathrm N,&s,t\in\{-,0\}\text{ and }(s,t)\ne(0,0),\\
\mathrm P,&s,t\in\{0,+\}.
\end{cases}
\]
Thus \(\lambda(0,0)=\mathrm P\), the pairs \((-,0),(0,-)\) have label \(\mathrm N\), and the pairs \((+,0),(0,+)\) have label \(\mathrm P\).

For
\[
(\epsilon,\eta)\in
\{(-,-),(-,0),(-,+),(0,+),(+,+)\},
\]
let \(\mathcal T_{\epsilon\eta}\) be the set of four-letter label words obtained by applying \(\lambda\) coordinatewise to a state in \(\mathcal V_\epsilon\) and a state in \(\mathcal V_\eta\), retaining a state pair only when at least one member is outside its corresponding \(\mathcal Z\)-set.

This is a complete finite automaton: a positive-area affine strip on \(x_0<x_1\), with \(\operatorname{sgn}x_0=\epsilon\) and \(\operatorname{sgn}x_1=\eta\), realizes exactly the words in \(\mathcal T_{\epsilon\eta}\).

Define
\[
\mathcal A=
\mathcal T_{--}\cup\mathcal T_{-0}\cup\mathcal T_{-+},
\qquad
\mathcal B=\mathcal T_{++},
\]
\[
\mathcal C=
\mathcal T_{-+}\cup\mathcal T_{0+}\cup\mathcal T_{++},
\qquad
\mathcal D=\mathcal T_{-+}.
\]
Here \(\mathcal A\) is the word set for an interval whose left endpoint is negative, \(\mathcal B\) for an interval with both endpoints positive, and \(\mathcal C\) for an interval whose right endpoint is positive. For arbitrary \(x_0<x_1\), the complete realizable word set is
\[
\mathcal A\cup\mathcal C,
\]
which has \(72\) elements.

For an explicit word list, abbreviate
\[
X=\mathrm C_+,\qquad Y=\mathrm C_-.
\]
In each of the following tables, the row gives the first two letters and the second column gives every allowed last-two-letter suffix. Undisplayed prefixes are impossible.

For \(\mathcal A\):
\[
\begin{array}{c|l|c}
NN&NN,PN,PP,PX,PY,XN,XX,YN,YY&9\\
PN&NN,PN,PX,XN,XX,YN&6\\
PP&NN,XN,XX&3\\
PX&NN,PN,PX,XN,XX,YN&6\\
PY&NN,XN,XX&3\\
XN&NN,PN,PP,PX,PY,XN,XX,YN,YY&9\\
XX&NN,PN,PP,PX,PY,XN,XX,YN,YY&9\\
YN&NN,PN,PX,XN,XX,YN&6\\
YY&NN,XN,XX&3
\end{array}
\]
For \(\mathcal B\):
\[
\begin{array}{c|l|c}
NN&PP&1\\
PN&PN,PP,PX,PY&4\\
PP&NN,PN,PP,PX,PY,XN,XX,YN,YY&9\\
PX&PN,PP,PX,PY,YN,YY&6\\
PY&PN,PP,PX,PY,XN,XX&6\\
XN&PP,PY&2\\
XX&PP,PY,YY&3\\
YN&PP,PX&2\\
YY&PP,PX,XX&3
\end{array}
\]
For \(\mathcal C\):
\[
\begin{array}{c|l|c}
NN&PP,PX,XX&3\\
PN&PN,PP,PX,PY,XN,XX&6\\
PP&NN,PN,PP,PX,PY,XN,XX,YN,YY&9\\
PX&NN,PN,PP,PX,PY,XN,XX,YN,YY&9\\
PY&PN,PP,PX,PY,XN,XX&6\\
XN&PN,PP,PX,PY,XN,XX&6\\
XX&NN,PN,PP,PX,PY,XN,XX,YN,YY&9\\
YN&PP,PX,XX&3\\
YY&PP,PX,XX&3
\end{array}
\]
For \(\mathcal D\):
\[
\begin{array}{c|l|c}
NN&PP,PX,XX&3\\
PN&PN,PX,XN,XX&4\\
PP&NN,XN,XX&3\\
PX&NN,PN,PX,XN,XX,YN&6\\
PY&XN,XX&2\\
XN&PN,PP,PX,PY,XN,XX&6\\
XX&NN,PN,PP,PX,PY,XN,XX,YN,YY&9\\
YN&PX,XX&2\\
YY&XX&1
\end{array}
\]

The resulting exact cardinalities are
\[
\begin{array}{c|c|c|c|c}
\text{set}&\text{all}&\{\mathrm N,\mathrm P\}\text{-only}
&\pi\text{-fixed}&\pi\text{-fixed and }\{\mathrm N,\mathrm P\}\text{-only}\\ \hline
\mathcal A&54&6&6&2\\
\mathcal B&36&6&4&2\\
\mathcal C&54&6&6&2\\
\mathcal D&36&3&4&1
\end{array}
\]
where
\[
\pi(\sigma_1,\sigma_2,\sigma_3,\sigma_4)
=(\sigma_3,\sigma_4,\sigma_1,\sigma_2).
\]

The reduced exhaustive list consists exactly of the systems
\[
\mathcal S_{\eta,\tau_Q,\tau_R,\sigma}
\]
such that:

1. \(\eta\in\{0,1,2\}\);

2. the tail pair is one of
\[
(\tau_Q,\tau_R)\in
\{(\mathrm F,\mathrm F),(\mathrm F,\mathrm I),
(\mathrm I,\mathrm I)\};
\]

3. the per-body words satisfy
\[
\begin{array}{c|c|c|c}
(\tau_Q,\tau_R)&\sigma_P&\sigma_Q&\sigma_R\\ \hline
(\mathrm F,\mathrm F)&\mathcal A&\mathcal B&\mathcal B\\
(\mathrm F,\mathrm I)&\mathcal A&\mathcal B&\mathcal C\\
(\mathrm I,\mathrm I)&\mathcal A&\mathcal C&\mathcal C
\end{array}
\]
and, in the \((\mathrm I,\mathrm I)\) row, additionally
\[
\sigma_Q\in\mathcal B
\quad\text{or}\quad
\sigma_R\in\mathcal D;
\]

4. at least one of the twelve letters is \(X\) or \(Y\);

5. for the twelve-letter vector, using the label order of accepted fact `b046e3066136e781`,
\[
\sigma\le_{\mathrm{lex}}\pi\sigma.
\]

This list contains exactly
\[
472032
\]
systems, and its feasibility union is identical to that of the original \(150994368\)-system list.

## Proof

At one endpoint,
\[
a=-L_E(x),\qquad b=-U_E(x),
\]
and \(L_E(x)\le U_E(x)\) is equivalent to \(b\le a\). The four values are
\[
a,\quad b,\quad x-b,\quad x-a.
\]
For \(x<0\), multiplication by the positive number \((-x)^{-1}\) reduces the sign calculation to \(x=-1\). The possible signs are determined solely by the order of
\[
b\le a
\]
relative to the two thresholds \(-1\) and \(0\). Exhausting the open intervals and the threshold equalities gives exactly \(\mathcal V_-\). The same argument at \(x>0\), with normalization \(x=1\) and thresholds \(0,1\), gives \(\mathcal V_+\). At \(x=0\), the state is
\[
(\operatorname{sgn}a,\operatorname{sgn}b,
 \operatorname{sgn}(-b),\operatorname{sgn}(-a)),
\]
which gives exactly \(\mathcal V_0\).

In these threshold decompositions, \(a=b\) is forced only for
\[
--00,\ 00--\quad(x<0),\qquad
0000\quad(x=0),
\]
and
\[
++00,\ 00++\quad(x>0).
\]
These are precisely the displayed \(\mathcal Z\)-sets. Every other state contains a nonempty cell with \(a>b\).

Now let the left and right endpoint states be \(v,w\). The definition of the four cases \(\mathrm N,\mathrm P,\mathrm C_+,\mathrm C_-\) in accepted fact `b046e3066136e781` is exactly the coordinatewise map \(\lambda(v_j,w_j)\). In particular, the convention \((0,0)\mapsto\mathrm P\) and all one-zero cases agree exactly with that fact.

Conversely, choose any state pair used in \(\mathcal T_{\epsilon\eta}\). Choose \(x_0<x_1\) having the prescribed signs and choose \(a_i,b_i\) in the corresponding state cells, with \(a_i>b_i\) at an endpoint whose state is outside \(\mathcal Z\). Put
\[
L_E(x_i)=-a_i,\qquad U_E(x_i)=-b_i
\]
and interpolate \(L_E,U_E\) affinely. Since \(a_i-b_i\ge0\) at both endpoints, \(U_E-L_E\ge0\) throughout the interval. At least one endpoint inequality is strict, so the strip has positive area. Its four labels are exactly the coordinatewise \(\lambda\)-word. This proves both necessity and sufficiency of the automaton, including all zero endpoints.

Applying \(\lambda\) to every pair in the three finite state tables gives the four explicit prefix-suffix tables in the statement. Their row sums give
\[
|\mathcal A|=54,\qquad
|\mathcal B|=36,\qquad
|\mathcal C|=54,\qquad
|\mathcal D|=36.
\]
Restricting the displayed tables to the letters \(N,P\) gives respectively
\[
6,\ 6,\ 6,\ 3.
\]
A word is fixed by \(\pi\) exactly when its prefix equals its suffix. Reading those entries from the same tables gives the fixed counts
\[
6,\ 4,\ 6,\ 4
\]
and fixed \(N,P\)-only counts
\[
2,\ 2,\ 2,\ 1.
\]
Thus these are exact symbolic table counts, not a numerical feasibility enumeration.

We next impose the support and tail information from accepted fact `b046e3066136e781`. Since
\[
\ell_P=-\delta<0,
\]
the \(P\)-word belongs to \(\mathcal A\). In a full \(Q\)-tail,
\[
D\le\ell_Q<u_Q,\qquad D=\delta+2>0,
\]
so the \(Q\)-word belongs to \(\mathcal B\). In an interior \(Q\)-tail,
\[
\ell_Q<D<u_Q,
\]
so \(u_Q>0\) and the \(Q\)-word belongs to \(\mathcal C\). Likewise, a full \(R\)-tail gives
\[
1\le\ell_R<u_R
\]
and hence \(\sigma_R\in\mathcal B\), while an interior \(R\)-tail gives \(u_R>1\) and hence \(\sigma_R\in\mathcal C\).

Horizontal projection of
\[
(P+Q)/2\subseteq R
\]
gives
\[
\ell_R\le\frac{\ell_P+\ell_Q}{2},
\qquad
u_R\ge\frac{u_P+u_Q}{2}.
\]
In either \(Q\)-tail case,
\[
u_Q>D=\delta+2,
\qquad
u_P>\ell_P=-\delta,
\]
so
\[
\frac{u_P+u_Q}{2}>1.
\]
Therefore \(u_R>1\), and the \(R\)-tail case \(\mathrm Z\), which requires \(u_R\le1\), is impossible.

If \(\tau_Q=\mathrm I\), then
\[
\frac{\ell_P+\ell_Q}{2}
=\frac{-\delta+\ell_Q}{2}<1.
\]
Hence \(\ell_R<1\), so \(\tau_R=\mathrm F\) is impossible. The only tail pairs are consequently
\[
(\mathrm F,\mathrm F),\quad
(\mathrm F,\mathrm I),\quad
(\mathrm I,\mathrm I).
\]

For the interior/interior pair, the left-support inequality gives one further exact word restriction. A \(Q\)-word has a realization with \(\ell_Q>0\) exactly when it lies in
\[
\mathcal B=\mathcal T_{++},
\]
and an \(R\)-word has a realization with \(\ell_R<0\) exactly when it lies in
\[
\mathcal D=\mathcal T_{-+}.
\]
If \(\sigma_Q\notin\mathcal B\) and
\(\sigma_R\notin\mathcal D\), then every compatible realization has
\[
\ell_Q\le0,\qquad \ell_R\ge0,
\]
and therefore
\[
\frac{\ell_P+\ell_Q}{2}
=\frac{-\delta+\ell_Q}{2}<0\le\ell_R,
\]
contradicting horizontal midpoint inclusion.

Conversely, if \(\sigma_Q\in\mathcal B\), choose
\[
\delta<\ell_Q<D=\delta+2.
\]
Then \((-\delta+\ell_Q)/2>0\), and any permitted \(R\) left-endpoint sign can be placed below this value while maintaining \(\ell_R<1\). If instead \(\sigma_R\in\mathcal D\), choose its negative left endpoint sufficiently far left. In either case choose \(u_R>1\) sufficiently large to contain \((u_P+u_Q)/2\). Homogeneity of the nonzero endpoint state cells preserves every label. Thus the exact interior/interior compatibility condition is
\[
\sigma_Q\in\mathcal B
\quad\text{or}\quad
\sigma_R\in\mathcal D.
\]

The state involution
\[
(s_1,s_2,s_3,s_4)\longmapsto
(s_3,s_4,s_1,s_2)
\]
preserves each \(\mathcal V_\epsilon\), each forced-zero set, and hence every transition set used above. Therefore \(\mathcal A,\mathcal B,\mathcal C,\mathcal D\), the interior/interior compatibility condition, and all three tail rows are \(\pi\)-invariant. Lexicographic selection consequently chooses exactly one representative from every orbit.

It remains to count the mixed-label orbits.

For \((\mathrm F,\mathrm F)\), the total number of label vectors is
\[
54\cdot36^2=69984.
\]
Exactly
\[
6^3=216
\]
have only \(N,P\) letters, so there are \(69768\) mixed vectors. The number of fixed mixed vectors is
\[
6\cdot4^2-2^3=96-8=88.
\]
Burnside's formula gives
\[
\frac{69768+88}{2}=34928
\]
orbits.

For \((\mathrm F,\mathrm I)\), the corresponding numbers are
\[
54\cdot36\cdot54=104976,
\]
\[
104976-216=104760
\]
mixed vectors, and
\[
6\cdot4\cdot6-2^3=144-8=136
\]
fixed mixed vectors. Hence there are
\[
\frac{104760+136}{2}=52448
\]
orbits.

For \((\mathrm I,\mathrm I)\), partition according to whether
\(\sigma_Q\in\mathcal B\). The exact number of allowed
\((\sigma_Q,\sigma_R)\) pairs is
\[
36\cdot54+(54-36)\cdot36=2592.
\]
All six \(N,P\)-only words of \(\mathcal C\) already lie in \(\mathcal B\), so all
\[
6^2=36
\]
\(N,P\)-only pairs are allowed. Thus the number of mixed three-body vectors is
\[
54\cdot2592-6\cdot36
=139968-216
=139752.
\]

Among fixed words, the number of allowed fixed
\((\sigma_Q,\sigma_R)\) pairs is
\[
4\cdot6+(6-4)\cdot4=32.
\]
There are \(2\cdot2=4\) fixed \(N,P\)-only pairs. Hence the fixed mixed three-body count is
\[
6\cdot32-2\cdot4=192-8=184,
\]
and Burnside gives
\[
\frac{139752+184}{2}=69968
\]
orbits.

The three tail rows therefore contribute
\[
34928+52448+69968=157344
\]
mixed-label orbits. The residual-strip index has three independent values
\(\eta=0,1,2\), so the final list size is
\[
3\cdot157344=472032.
\]

Every feasible system in the original list must satisfy the endpoint automaton, the three tail alternatives, and the interior/interior compatibility condition, so it occurs in the reduced list after possibly applying the involution. Conversely, every system in the reduced list is literally one of the systems of accepted fact `b046e3066136e781`. Hence the two feasibility unions are identical.

## External sources

none
