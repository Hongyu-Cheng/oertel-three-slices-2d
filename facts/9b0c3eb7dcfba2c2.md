---
fact_id: 9b0c3eb7dcfba2c2
kind: lemma
author: "mp_r256_global_literature"
assurance: LLM-verified
subgoal_id: three-slice-six-cap-equivalence
depends_on: []
source_packet_sha256: 66a0356b78766ec1861ccab102ed66790b36954a65fa901df96bd34fae8de2a6
verifier_run: 45e93b4dbdc44923
target_match: null
---

## Statement

Let
\[
\Lambda=\mathbb Z\times\mathbb R^2,\qquad
S=C\cap\Lambda
\]
be as in the locked problem, and define the finite Borel measure
\[
\mu(B)=\mathcal H_2(S\cap B),\qquad \mu(\mathbb R^3)=T.
\]
Set \(q=2T/9\). The following statements are equivalent.

1. There is \(y^*\in S\) such that \(h_S(y^*)\ge q\).

2. For every \(1\le r\le6\) and every collection of closed halfspaces
   \(H_1,\ldots,H_r\subseteq\mathbb R^3\) covering \(S\),
   \[
   \max_{1\le j\le r}\mu(H_j)\ge q.
   \tag{C6}
   \]

Moreover, (C6) holds automatically for \(1\le r\le4\). Consequently, the
locked conclusion is equivalent to checking (C6) only for \(r=5\) and
\(r=6\).

## Proof

First assume statement 1. If \(H_1,\ldots,H_r\) cover \(S\), then
\(y^*\in H_j\) for some \(j\). The definition of depth gives
\[
\mu(H_j)\ge h_S(y^*)\ge q.
\]
Thus (C6) holds for every \(r\), proving statement 2.

Conversely, assume statement 2 and suppose for contradiction that statement
1 fails. Then \(h_S(y)<q\) for every \(y\in S\). By the definition of the
infimum, for each \(y\in S\) there is a closed halfspace
\[
K_y=\{z\in\mathbb R^3:\langle u_y,z\rangle\le b_y\},
\qquad \|u_y\|=1,
\]
such that \(y\in K_y\) and \(\mu(K_y)<q\).

We first replace \(K_y\) by a low-mass halfspace whose interior contains
\(y\). For \(n\ge1\), set
\[
K_{y,n}=\{z\in\mathbb R^3:\langle u_y,z\rangle\le b_y+1/n\}.
\]
The sets \(K_{y,n}\) decrease to \(K_y\) as \(n\to\infty\). Since \(\mu\) is
finite, continuity from above gives
\[
\mu(K_{y,n})\longrightarrow\mu(K_y)<q.
\]
Choose \(n(y)\) large enough that
\(\mu(K_{y,n(y)})<q\), and write
\[
H_y=K_{y,n(y)}.
\]
Because
\[
\langle u_y,y\rangle\le b_y<b_y+1/n(y),
\]
we have \(y\in\operatorname{int}H_y\).

This perturbation is valid for both possible boundary types. Write
\(u_y=(u_{y,1},u_y')\) according to
\(\mathbb R\times\mathbb R^2\). If \(u_y'\ne0\), then on each support plane
\(\{i\}\times\mathbb R^2\) the displacement sweeps a decreasing planar strip;
the preceding continuity-from-above argument says that the total area of
the three added strips tends to zero. If \(u_y'=0\), the boundary is parallel
to the three support planes. In that case choose \(n(y)\) still larger so
that
\[
\frac1{n(y)}
<
\min\{u_{y,1}i-b_y:i\in\{0,1,2\},\ u_{y,1}i>b_y\}
\]
when the set on the right is nonempty. No new support plane is then crossed.
A support plane lying on the original boundary was already included in the
closed halfspace \(K_y\), so this horizontal perturbation adds no slice mass.
Thus in every orientation \(H_y\) has mass strictly below \(q\) and contains
\(y\) in its interior.

The sets \(\operatorname{int}H_y\), \(y\in S\), form an open cover of \(S\).
The set \(S\) is compact because it is the intersection of the compact
polytope \(C\) with the closed set \(\Lambda\). Hence there are
\(y_1,\ldots,y_m\in S\) such that
\[
S\subseteq\bigcup_{j=1}^m\operatorname{int}H_j,
\qquad
H_j:=H_{y_j},
\qquad
\mu(H_j)<q.
\tag{1}
\]

For \(1\le j\le m\), define
\[
F_j=\mathbb R^3\setminus\operatorname{int}H_j.
\]
Each \(F_j\) is a closed halfspace, hence convex. The finite family of convex
sets
\[
\mathcal G=\{C,F_1,\ldots,F_m\}
\]
has empty intersection on \(\Lambda\):
\[
\Lambda\cap C\cap\bigcap_{j=1}^mF_j=\varnothing.
\tag{2}
\]
Indeed, a point in \(\Lambda\cap C\) belongs to \(S\), while (1) puts it in
the interior of at least one \(H_j\), so it cannot belong to every \(F_j\).

Averkov and Weismantel, Theorem 1.1, prove
\[
h(\mathbb R^d\times\mathbb Z^k)=(d+1)2^k.
\]
Permuting coordinates identifies
\(\Lambda=\mathbb Z\times\mathbb R^2\) with
\(\mathbb R^2\times\mathbb Z\), so
\[
h(\Lambda)=(2+1)2^1=6.
\tag{3}
\]
By the definition of this Helly number, (2) and (3) imply that some subfamily
\(\mathcal G'\subseteq\mathcal G\) of at most six members already has empty
intersection on \(\Lambda\).

There are two cases.

If \(C\in\mathcal G'\), let
\[
J=\{j:F_j\in\mathcal G'\}.
\]
Then \(|J|\le5\). Moreover, \(|J|\ge1\), since
\(C\cap\Lambda=S\ne\varnothing\). The empty-intersection property says
\[
\Lambda\cap C\cap\bigcap_{j\in J}F_j=\varnothing.
\]
Equivalently, the open halfspaces
\(\operatorname{int}H_j\), \(j\in J\), cover \(S\). Therefore the closed
halfspaces \(H_j\), \(j\in J\), also cover \(S\). Every one of them has mass
strictly below \(q\) by (1), contradicting (C6) with
\(1\le |J|\le5\).

If \(C\notin\mathcal G'\), define \(J\) in the same way. Then
\(1\le|J|\le6\), because \(\Lambda\ne\varnothing\), and
\[
\Lambda\cap\bigcap_{j\in J}F_j=\varnothing.
\]
Thus the interiors of \(H_j\), \(j\in J\), cover all of \(\Lambda\), and in
particular the corresponding closed halfspaces cover \(S\). Again every
selected halfspace has mass strictly below \(q\), contradicting (C6), now
with \(1\le|J|\le6\).

Both cases are impossible. Hence statement 1 follows from statement 2, and
the two statements are equivalent.

It remains to reduce the cover assertion to five and six caps. If
\(H_1,\ldots,H_r\) cover \(S\), finite subadditivity gives
\[
T=\mu(S)
\le\sum_{j=1}^r\mu(H_j)
\le r\max_{1\le j\le r}\mu(H_j).
\]
For \(1\le r\le4\),
\[
\max_j\mu(H_j)\ge\frac{T}{r}\ge\frac{T}{4}>\frac{2T}{9}=q.
\]
Here \(T>0\) because each \(A_i\) is two-dimensional and nonempty.
Thus (C6) is automatic for \(r\le4\). Its only nontrivial cases are
\(r=5\) and \(r=6\), completing the proof.

## External sources

1. G. Averkov and R. Weismantel, "Transversal numbers over subsets of linear
   spaces," Theorem 1.1: for nonnegative integers \(d,k\), not both zero,
   \[
   h(\mathbb R^d\times\mathbb Z^k)=(d+1)2^k.
   \]
   Primary preprint: https://arxiv.org/abs/1002.0948
