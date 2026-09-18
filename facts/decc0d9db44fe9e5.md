---
fact_id: decc0d9db44fe9e5
kind: lemma
author: "mp_r74_opposite_retained_separator_row"
assurance: LLM-verified
subgoal_id: canonical-opposite-hull-charge
depends_on: ["0e51a47a9add571f","b431dbefa8a4aec7"]
source_packet_sha256: c52d419dec8b79b1677e3e650d49d49c9a065017294de51fcc6e277f89405932
verifier_run: 10b15c3201954194
target_match: null
---

## Statement

Use the common-plane and exact-cell convention of accepted fact `0e51a47a9add571f`.  Let \(N=\{j,k,\ell\}\), let the affine functions have pairwise nonparallel linear parts and satisfy
\[
f_j+f_k+f_\ell=-1,\qquad L_j+L_k+L_\ell<-1,
\]
and put \(p_i=f_i-L_i\) and \(q_i=f_i+L_i\).  Let \(A_0,A_2,K\) be two-dimensional convex polygons satisfying
\[
\frac{A_0+A_2}{2}\subseteq K.
\]
Assume that the positive-area exact cells are precisely
\[
P_j,P_0,P_\ell,P_{k\ell},\qquad
Q_j,Q_{jk},Q_N,Q_{k\ell},\qquad
R_j,R_{jk},R_N,R_{k\ell},
\]
and that all twelve displayed cells have positive area.  Define
\[
\Delta=|\det(\nabla f_j,\nabla f_\ell)|>0,
\qquad
\rho_{2i}^-=
\lim_{\eta\downarrow0}
\frac{\mathcal H^1(A_2\cap\{q_i=-\eta\})}
     {\|\nabla f_i\|},
\qquad
\lambda_{2i}=\Delta\rho_{2i}^-.
\]
For the \(j\ell\)-row of accepted fact `b431dbefa8a4aec7`, put
\[
B=\{(p_j(w),p_\ell(w)):w\in\overline{P_0}\},
\qquad
D=\{(-q_j(w),-q_\ell(w)):w\in\overline{Q_N}\}.
\]
Then
\[
\mathcal H^1(D\cap(\{0\}\times\mathbb R))=\lambda_{2j},
\qquad
\mathcal H^1(D\cap(\mathbb R\times\{0\}))=\lambda_{2\ell}.
\]
Moreover, there exist \(a,d>0\) such that
\[
aX+dY\le aU+dV
\quad
\text{for all }(X,Y)\in B,\ (U,V)\in D.
\]
Consequently the \(j\ell\)-row satisfies both hypotheses whose existence was left open after accepted fact `b431dbefa8a4aec7`.  The conclusion remains valid after imposing all of that fact's additional scalar and genuine-lower-crossing hypotheses.

## Proof

Let
\[
\tau=-(q_j+q_k+q_\ell)=1-(L_j+L_k+L_\ell)>0.
\]
Because the linear parts are pairwise nonparallel, \(w\mapsto(q_j(w),q_k(w))\) is an affine coordinate system.  Write its coordinates as \(x=q_j\), \(y=q_k\); then
\[
q_\ell=-\tau-x-y.
\]
The four supported \(Q\)-chambers have strict interiors
\[
\begin{array}{c|c}
Q_j&x<0,\ y>0,\ x+y<-\tau,\\
Q_{jk}&x<0,\ y<0,\ x+y<-\tau,\\
Q_N&x<0,\ y<0,\ x+y>-\tau,\\
Q_{k\ell}&x>0,\ y<0,\ x+y>-\tau.
\end{array}
\tag{1}
\]
Every positive-area cell contains a point of \(\operatorname{int}A_2\) in its strict chamber.

We first determine the whole \(q_j=0\) section.  Suppose that
\(w\in A_2\cap\{x=0\}\) has \(y<-\tau\).  Choose
\(z\in\operatorname{int}A_2\cap Q_{k\ell}\).  For every sufficiently
small \(t>0\), the point \((1-t)w+tz\) lies in
\(\operatorname{int}A_2\) and has
\[
x>0,\qquad y<0,\qquad x+y<-\tau.
\]
It therefore lies in the unsupported open chamber \(Q_k\), contradicting
that \(Q_k\) has zero area.  If instead \(w\) has \(y>0\), choose
\(z\in\operatorname{int}A_2\cap Q_N\).  For small \(t>0\),
\((1-t)w+tz\) has
\[
x<0,\qquad y>0,\qquad x+y>-\tau,
\]
so it lies in the unsupported open chamber \(Q_{j\ell}\), again a
contradiction.  Hence
\[
A_2\cap\{q_j=0\}
\subseteq\{q_j=0,\ q_k\le0,\ q_\ell\le0\}
\subseteq\overline{Q_N}.
\tag{2}
\]

The same argument determines the whole \(q_\ell=0\) section.  On that
line \(x+y=-\tau\).  If a point \(w\) of the section has \(x>0\), move
slightly from \(w\) toward a point of
\(\operatorname{int}A_2\cap Q_{jk}\).  The resulting interior points
have \(x>0,y<0,x+y<-\tau\), hence lie in the unsupported chamber
\(Q_k\).  If \(w\) has \(y>0\), move slightly toward a point of
\(\operatorname{int}A_2\cap Q_N\).  The resulting interior points have
\(x<0,y>0,x+y>-\tau\), hence lie in the unsupported chamber
\(Q_{j\ell}\).  Therefore
\[
A_2\cap\{q_\ell=0\}
\subseteq\{q_\ell=0,\ q_j\le0,\ q_k\le0\}
\subseteq\overline{Q_N}.
\tag{3}
\]
The elementary convexity fact used twice above is that if \(z\) is an
interior point of a convex body and \(w\) belongs to that body, then
\((1-t)w+tz\) is interior for every \(0<t\le1\).

Positive area in \(Q_N\) and \(Q_{k\ell}\) puts interior points of
\(A_2\) on opposite sides of \(q_j=0\).  Thus that line meets
\(\operatorname{int}A_2\).  Likewise, positive area in \(Q_{jk}\) and
\(Q_N\) puts interior points on opposite sides of \(q_\ell=0\), so that
line also meets \(\operatorname{int}A_2\).  For a polygon, the chord
length is continuous at every level whose line meets the interior.
Consequently the two one-sided traces in the statement equal the actual
chord lengths at levels \(q_j=0\) and \(q_\ell=0\).

Consider the affine coordinate map
\[
\Psi(w)=(-q_j(w),-q_\ell(w)).
\]
Along \(q_j=0\), the absolute derivative of \(-q_\ell\) with respect to
Euclidean arclength is
\[
\frac{|\det(\nabla f_j,\nabla f_\ell)|}{\|\nabla f_j\|}
=\frac{\Delta}{\|\nabla f_j\|}.
\]
By (2), the image under \(\Psi\) of the full \(q_j=0\) chord is exactly
\(D\cap(\{0\}\times\mathbb R)\).  Hence its length is
\(\Delta\rho_{2j}^-=\lambda_{2j}\).  Interchanging \(j\) and \(\ell\)
and using (3) gives
\[
\mathcal H^1(D\cap(\mathbb R\times\{0\}))
=\Delta\rho_{2\ell}^-=\lambda_{2\ell}.
\tag{4}
\]
This proves both retained-trace conditions, in fact with equality.

It remains to prove nondegeneracy.  First, no point of \(B\) can strictly
dominate a point of \(D\) in both coordinates.  Such a pair, represented
by endpoint points \(u\in\overline{P_0}\) and
\(v\in\overline{Q_N}\), would give at their midpoint \(m=(u+v)/2\)
\[
2f_j(m)=p_j(u)+q_j(v)>0,\qquad
2f_\ell(m)=p_\ell(u)+q_\ell(v)>0.
\]
Since \(f_j+f_k+f_\ell=-1\), this forces \(f_k(m)<0\), so \(m\) lies in
the unsupported open middle chamber \(R_k\).  Strict inequalities persist
after approximating \(u,v\) by strict interior points of their
positive-area cells.  Their midpoint is interior to
\((A_0+A_2)/2\), hence interior to \(K\); an open neighborhood in
\(R_k\) would then give \(R_k\) positive area, a contradiction.
Therefore
\[
(B-D)\cap(0,\infty)^2=\varnothing.
\tag{5}
\]

Separating the compact convex set \(B-D\) from the open positive quadrant
as in accepted fact `b431dbefa8a4aec7` yields \(a,d\ge0\), not both
zero, with
\[
aX+dY\le aU+dV
\quad
\text{for all }(X,Y)\in B,\ (U,V)\in D.
\tag{6}
\]
Both axis sections in (4) are nonempty, because the two cutting lines
meet \(\operatorname{int}A_2\).  Also, positive area of \(P_0\) supplies
a point \((X,Y)\in B\) with \(X,Y>0\).  If \(a=0\), then \(d>0\);
choosing the point of \(B\) with \(Y>0\) and a point of
\(D\cap(\mathbb R\times\{0\})\) contradicts (6).  If \(d=0\), then
\(a>0\); choosing the point of \(B\) with \(X>0\) and a point of
\(D\cap(\{0\}\times\mathbb R)\) contradicts (6).  Thus \(a,d>0\).
This is the required nondegenerate compatibility separator.

## External sources

none
