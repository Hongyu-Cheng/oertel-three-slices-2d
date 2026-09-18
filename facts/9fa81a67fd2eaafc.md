---
fact_id: 9fa81a67fd2eaafc
kind: lemma
author: "mp_r2_balanced_bridge"
assurance: LLM-verified
subgoal_id: balanced-middle-bridge
depends_on: ["400272f6de6c67bb","8ad0785e5b4ae9ef"]
source_packet_sha256: e74b1a5d9baa6567b2d40c3cbe14bdf53a805c07c52d6c2d8c175c0117d38c98
verifier_run: 3d44865db60246db
target_match: null
---

## Statement

Let \(C\subseteq\mathbb R\times\mathbb R^2\) be a compact polytope whose integer-height sections are exactly
\[
S=(\{0\}\times A_0)\cup(\{1\}\times A_1)\cup(\{2\}\times A_2),
\]
where each \(A_i\subseteq\mathbb R^2\) is a nonempty two-dimensional convex polytope. Write
\[
a_i=|A_i|,\qquad T=a_0+a_1+a_2,
\]
and assume \(a_i<T/2\) for \(i=0,1,2\). Let
\[
g_i=\frac1{a_i}\int_{A_i}w\,dw\quad(i=0,2),
\qquad
z=\frac{g_0+g_2}{2}.
\]
Then \(z\in A_1\), and for every \(q\in\mathbb S^1\) and \(\lambda\in\mathbb R\),
\[
\sum_{i=0}^2
\left|A_i\cap
\left\{w:\langle q,w-z\rangle\le\lambda(1-i)\right\}\right|
\ge
\frac{(\sqrt{a_0}+\sqrt{a_2})^2+4\min\{a_0,a_2\}}{9}.
\tag{1}
\]
In particular, if
\[
(\sqrt{a_0}+\sqrt{a_2})^2+4\min\{a_0,a_2\}\ge2T,
\tag{2}
\]
then
\[
h_S(1,z)\ge\frac{2T}{9}.
\]

## Proof

The centroid \(g_i\) belongs to \(A_i\) for \(i=0,2\). Indeed, if \(g_i\notin A_i\), strict separation from the compact convex set \(A_i\) would give an affine functional whose value at \(g_i\) is strictly larger than its supremum on \(A_i\), contradicting the definition of \(g_i\) as the average of points of \(A_i\).

Accepted fact `8ad0785e5b4ae9ef` gives
\[
\frac{A_0+A_2}{2}\subseteq A_1.
\]
Therefore
\[
z=\frac{g_0+g_2}{2}\in A_1.
\]

Fix \(q\in\mathbb S^1\), and define the centroid halfplane caps
\[
B_i=
A_i\cap
\left\{w:\langle q,w-g_i\rangle\le0\right\},
\qquad i=0,2.
\]
The planar Grünbaum inequality gives
\[
|B_i|\ge\frac49a_i,\qquad i=0,2.
\tag{3}
\]
If \(w_i\in B_i\), then
\[
\frac{w_0+w_2}{2}\in\frac{A_0+A_2}{2}\subseteq A_1
\]
and
\[
\left\langle q,\frac{w_0+w_2}{2}-z\right\rangle
=
\frac12\langle q,w_0-g_0\rangle
+\frac12\langle q,w_2-g_2\rangle
\le0.
\]
Hence
\[
\frac{B_0+B_2}{2}
\subseteq
A_1\cap\{w:\langle q,w-z\rangle\le0\}.
\tag{4}
\]
By the planar Brunn-Minkowski inequality, (3), and (4),
\[
\begin{aligned}
\left|A_1\cap\{w:\langle q,w-z\rangle\le0\}\right|^{1/2}
&\ge
\left|\frac{B_0+B_2}{2}\right|^{1/2}\\
&\ge
\frac{\sqrt{|B_0|}+\sqrt{|B_2|}}{2}\\
&\ge
\frac{\sqrt{a_0}+\sqrt{a_2}}{3}.
\end{aligned}
\]
Thus the middle-slice contribution satisfies
\[
\left|A_1\cap\{w:\langle q,w-z\rangle\le0\}\right|
\ge
\frac{(\sqrt{a_0}+\sqrt{a_2})^2}{9}.
\tag{5}
\]

Now fix \(\lambda\in\mathbb R\), and set
\[
d=\langle q,g_0-z\rangle
=\frac12\langle q,g_0-g_2\rangle.
\]
Since \(z=(g_0+g_2)/2\),
\[
\langle q,g_2-z\rangle=-d.
\]
If \(\lambda\ge d\), then \(g_0\) belongs to
\[
\{w:\langle q,w-z\rangle\le\lambda\},
\]
so the slice-\(0\) cap is a halfplane cap containing the centroid of \(A_0\). Grünbaum's inequality therefore yields
\[
\left|A_0\cap\{w:\langle q,w-z\rangle\le\lambda\}\right|
\ge\frac49a_0.
\tag{6}
\]
If \(\lambda\le d\), then
\[
\langle q,g_2-z\rangle=-d\le-\lambda,
\]
so the slice-\(2\) cap contains \(g_2\), and similarly
\[
\left|A_2\cap\{w:\langle q,w-z\rangle\le-\lambda\}\right|
\ge\frac49a_2.
\tag{7}
\]
Every real \(\lambda\) satisfies at least one of \(\lambda\ge d\) and \(\lambda\le d\). Consequently, the two outer slices together always contribute at least
\[
\frac49\min\{a_0,a_2\}.
\tag{8}
\]
Adding (5) and (8) proves (1).

Accepted fact `400272f6de6c67bb` states that the non-slice-parallel halfspaces through \((1,z)\) are exactly the caps parameterized by \(q\in\mathbb S^1\) and \(\lambda\in\mathbb R\). Under (2), inequality (1) bounds each such halfspace by \(2T/9\). The two slice-parallel halfspaces have measures
\[
a_0+a_1=T-a_2>\frac T2>\frac{2T}{9}
\]
and
\[
a_1+a_2=T-a_0>\frac T2>\frac{2T}{9},
\]
because \(a_0,a_2<T/2\). Applying the exact minimum formula in accepted fact `400272f6de6c67bb` gives
\[
h_S(1,z)\ge\frac{2T}{9}.
\]

## External sources

Planar Grünbaum inequality: Branko Grünbaum, “Partitions of mass-distributions and of convex bodies by hyperplanes,” Pacific Journal of Mathematics 10 (1960), no. 4, 1257–1261, Theorem 2, https://msp.org/pjm/1960/10-4/pjm-v10-n4-p18-p.pdf. The theorem states that every halfspace containing the centroid of an \(n\)-dimensional convex body has volume at least \((n/(n+1))^n\) times the body's volume. For \(n=2\), this is \(4/9\). It applies to each two-dimensional convex polytope \(A_i\), both when the cap boundary passes through its centroid and when the halfplane merely contains it.

Planar Brunn-Minkowski inequality: Hermann Brunn, *Ueber Ovale und Eiflächen: Inaugural-Dissertation*, Akademische Buchdruckerei von F. Straub, Munich, 1887, Bayerische Staatsbibliothek shelfmark Math.p. 57 mz, https://www.deutsche-digitale-bibliothek.de/item/6J63DGQIMCO3LHKRNUPGC47B3OQEZI7N. In the form used here, for nonempty planar convex bodies \(B,D\) and \(t\in[0,1]\),
\[
|(1-t)B+tD|^{1/2}
\ge
(1-t)|B|^{1/2}+t|D|^{1/2}.
\]
Taking \(B=B_0\), \(D=B_2\), and \(t=1/2\) gives the inequality used above.
