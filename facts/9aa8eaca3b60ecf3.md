---
fact_id: 9aa8eaca3b60ecf3
kind: lemma
author: "mp_r350_depth_erosion_duality"
assurance: LLM-verified
subgoal_id: projection-quantile-depth-erosion-duality
depends_on: ["19703e1e768865b1","4565d02e3cfa153e"]
source_packet_sha256: d92b51fb811370f29922c329abf4fda96e7b7f7d3d865ef5868e52008968465f
verifier_run: 26cce0eba50a484a
target_match: null
---

## Statement

Let \(A_0,A_2\subset\mathbb R^2\) be compact two-dimensional convex
bodies with
\[
M=|A_0|>m=|A_2|>0.
\]
For every nonzero linear form \(\lambda\), define
\[
q(\lambda)=
\inf\{s:|A_0\cap\{\lambda\le s\}|\ge m\},
\qquad
\beta(\lambda)=\max_{a\in A_2}\lambda(a),
\]
and put
\[
D_m(A_0)=\{p\in\mathbb R^2:d_{A_0}(p)\ge m\}.
\]
Then
\[
\exists z\in\mathbb R^2\quad z-A_2\subseteq D_m(A_0)
\tag{1}
\]
if and only if every triple of nonzero linear forms satisfying
\[
\lambda_1+\lambda_2+\lambda_3=0
\tag{2}
\]
obeys
\[
\sum_{i=1}^3
\bigl(q(\lambda_i)+\beta(\lambda_i)\bigr)\le0.
\tag{3}
\]
If (1) fails, there is such a triple for which the sum in (3) is
strictly positive.  A common positive scaling then makes that sum
strictly larger than \(2\), the necessary projection-quantile budget in
accepted fact `19703e1e768865b1`.

## Proof

We use the defining halfspace-depth formula
\[
d_{A_0}(p)=
\inf\{|A_0\cap H|:H\text{ is a closed halfplane containing }p\}
\tag{4}
\]
for every \(p\in\mathbb R^2\).  If depth was initially defined only on
\(A_0\), (4) is its natural zero extension: for \(p\notin A_0\), strict
separation from the compact convex set \(A_0\) gives a closed halfplane
containing \(p\) and disjoint from \(A_0\).

Fix a nonzero linear form \(\lambda\) and write
\[
F_\lambda(s)=|A_0\cap\{\lambda\le s\}|.
\tag{5}
\]
For every sequence \(s_n\to s\), the corresponding indicator functions
converge pointwise away from the affine line \(\{\lambda=s\}\).  That
line has planar measure zero, and the indicators are bounded by
\(\mathbf 1_{A_0}\).  Dominated convergence therefore shows that
\(F_\lambda\) is continuous.  Let
\[
\alpha_\lambda=\min_{A_0}\lambda,
\qquad
\delta_\lambda=\max_{A_0}\lambda.
\]
These extrema are attained.  Since \(A_0\) has nonempty interior and
\(\lambda\ne0\), one has
\(\alpha_\lambda<\delta_\lambda\).  The lower support cap is contained
in a line and hence has area zero, while the upper cap is all of
\(A_0\).  Thus
\[
F_\lambda(\alpha_\lambda)=0<m<M
=F_\lambda(\delta_\lambda).
\tag{6}
\]
It follows that
\[
E_\lambda=\{s:F_\lambda(s)\ge m\}
\]
is a nonempty closed upper set, bounded below.  Hence
\(q(\lambda)=\inf E_\lambda\) belongs to \(E_\lambda\).  Continuity and
(6) also give
\[
\alpha_\lambda<q(\lambda)<\delta_\lambda,
\qquad
F_\lambda(q(\lambda))=m.
\tag{7}
\]
Indeed, if the last equality were strict, a slightly smaller threshold
would still have cap area greater than \(m\), contradicting the
definition of \(q(\lambda)\).  In particular,
\[
F_\lambda(s)\ge m
\quad\Longleftrightarrow\quad
s\ge q(\lambda).
\tag{8}
\]
This includes support-line thresholds and positive-length support
faces.

We next identify the whole closed depth region.  For any \(p\), the
tight lower halfplane
\[
\{x:\lambda(x)\le\lambda(p)\}
\]
contains \(p\).  Conversely, every closed halfplane containing \(p\)
can be written as \(\{\lambda\le s\}\) with
\(\lambda(p)\le s\), and it contains the corresponding tight
halfplane through \(p\).  Therefore (4), (5), and (8) give
\[
\begin{aligned}
d_{A_0}(p)\ge m
&\quad\Longleftrightarrow\quad
F_\lambda(\lambda(p))\ge m
\ \text{for every }\lambda\ne0\\
&\quad\Longleftrightarrow\quad
\lambda(p)\ge q(\lambda)
\ \text{for every }\lambda\ne0.
\end{aligned}
\]
Consequently,
\[
\boxed{
D_m(A_0)=
\bigcap_{\lambda\ne0}
\{p:\lambda(p)\ge q(\lambda)\}.
}
\tag{9}
\]
In particular, all boundary equalities are retained and
\(D_m(A_0)\) is a closed convex set.

Compactness of \(A_2\) makes \(\beta(\lambda)\) finite and attained,
even when the maximizing set is a support segment.  Define
\[
c(\lambda)=q(\lambda)+\beta(\lambda),
\qquad
K_\lambda=\{z:\lambda(z)\ge c(\lambda)\}.
\tag{10}
\]
Using (9), we obtain the exact chain
\[
\begin{aligned}
z-A_2\subseteq D_m(A_0)
&\quad\Longleftrightarrow\quad
\lambda(z-a)\ge q(\lambda)
\quad(\lambda\ne0,\ a\in A_2)\\
&\quad\Longleftrightarrow\quad
\lambda(z)\ge q(\lambda)+\max_{a\in A_2}\lambda(a)
\quad(\lambda\ne0)\\
&\quad\Longleftrightarrow\quad
z\in\bigcap_{\lambda\ne0}K_\lambda.
\end{aligned}
\tag{11}
\]

We also record the exact homogeneity used below.  For \(t>0\),
\[
F_{t\lambda}(s)=F_\lambda(s/t),
\]
so the threshold set for \(t\lambda\) is \(tE_\lambda\).  Hence
\[
q(t\lambda)=tq(\lambda),
\qquad
\beta(t\lambda)=t\beta(\lambda),
\qquad
c(t\lambda)=tc(\lambda).
\tag{12}
\]
Only positive scaling is asserted or needed.

Suppose first that (1) holds, and choose the corresponding \(z\).
By (11), \(\lambda(z)\ge c(\lambda)\) for every nonzero \(\lambda\).
For a triple satisfying (2), summing these inequalities gives
\[
\sum_{i=1}^3c(\lambda_i)
\le\sum_{i=1}^3\lambda_i(z)=0.
\tag{13}
\]
This proves (3), including its equality case.

For the converse, suppose (1) fails.  By (11),
\[
\bigcap_{\lambda\ne0}K_\lambda=\varnothing.
\tag{14}
\]
We first reduce (14) to finitely many halfplanes.  Choose linearly
independent forms \(u,v\), and consider
\[
B=K_u\cap K_{-u}\cap K_v\cap K_{-v}.
\tag{15}
\]
If \(B\) is empty, (14) already has a finite witness.  Otherwise, the
linear isomorphism \(z\mapsto(u(z),v(z))\) maps \(B\) into the closed
rectangle
\[
[c(u),-c(-u)]\times[c(v),-c(-v)].
\]
Thus \(B\) is compact.  The sets \(B\cap K_\lambda\) are closed in
\(B\), and their total intersection is empty by (14).  The finite
intersection property for compact spaces gives finitely many
directions \(\rho_1,\ldots,\rho_N\) such that
\[
B\cap\bigcap_{j=1}^N K_{\rho_j}=\varnothing.
\tag{16}
\]
Including the four halfplanes in (15), (16) is a finite family of
closed convex sets with empty intersection.  Planar Helly gives a
subfamily
\[
K_{\sigma_1},\ldots,K_{\sigma_r},
\qquad r\le3,
\tag{17}
\]
whose intersection is empty.  Since each individual halfplane is
nonempty, \(r\) is \(2\) or \(3\).

We now state and verify the strict sign in the finite Farkas
alternative.  For a finite system
\[
\sigma_j(z)\ge b_j\qquad(j=1,\ldots,r),
\tag{18}
\]
write \(A\) for the matrix whose rows represent the forms
\(\sigma_j\), and \(b=(b_j)\).  Feasibility of (18) is equivalent to
\[
b\in C:=\{Az-s:z\in\mathbb R^2,\ s\in\mathbb R_{\ge0}^r\}.
\]
The set \(C\) is a closed polyhedral cone.  If (18) is infeasible,
separation of \(b\) from \(C\) gives a vector
\(\gamma\) such that
\[
\gamma\mathbin{\cdot}b>0,
\qquad
\gamma\mathbin{\cdot}y\le0\quad(y\in C).
\tag{19}
\]
Taking \(y=Az\) for both \(z\) and \(-z\) gives
\(A^{\mathsf T}\gamma=0\).  Taking \(y=-s\) for arbitrary
\(s\ge0\) gives \(\gamma\ge0\).  Thus
\[
\gamma_j\ge0,\qquad
\sum_{j=1}^r\gamma_j\sigma_j=0,\qquad
\sum_{j=1}^r\gamma_jb_j>0.
\tag{20}
\]
Conversely, (20) immediately contradicts any feasible point in (18).
This proves the alternative and fixes the strict sign.

Apply (20) to (17) with \(b_j=c(\sigma_j)\).  Let
\[
J=\{j:\gamma_j>0\}.
\]
Because every \(\sigma_j\) is nonzero and their positive weighted sum
is zero, \(J\) cannot have one element.  Since \(r\le3\),
\(|J|\) is \(2\) or \(3\).  For \(j\in J\), put
\[
\mu_j=\gamma_j\sigma_j.
\]
Equations (12) and (20) yield
\[
\sum_{j\in J}\mu_j=0,
\qquad
\sum_{j\in J}c(\mu_j)
=\sum_{j\in J}\gamma_jc(\sigma_j)>0.
\tag{21}
\]

If \(|J|=3\), enumerate \(J=\{j_1,j_2,j_3\}\) and set
\(\nu_i=\mu_{j_i}\).  These are already the required nonzero triple.
If \(|J|=2\), enumerate them so that
\(\mu_1+\mu_2=0\), and define
\[
\nu_1=\mu_1,\qquad
\nu_2=\frac12\mu_2,\qquad
\nu_3=\frac12\mu_2.
\tag{22}
\]
The statement imposes no distinctness or nonparallelism condition.
Thus all three forms in (22) are nonzero, their sum is zero, and (12)
and (21) give
\[
\sum_{i=1}^3c(\nu_i)
=c(\mu_1)+c(\mu_2)>0.
\tag{23}
\]
This handles every two-direction Helly or Farkas certificate without
introducing a zero form.

In either case, failure of (1) has produced a triple of nonzero forms
\(\nu_1,\nu_2,\nu_3\) with zero sum and
\[
S:=\sum_{i=1}^3
\bigl(q(\nu_i)+\beta(\nu_i)\bigr)>0.
\tag{24}
\]
This contradicts (3), proving the converse.  Finally, choose any
\(t>2/S\).  By (12), the triple \(t\nu_1,t\nu_2,t\nu_3\) is still
nonzero and zero-sum, while
\[
\sum_{i=1}^3
\bigl(q(t\nu_i)+\beta(t\nu_i)\bigr)
=tS>2.
\tag{25}
\]
Equation (25) is precisely the claimed rescaling to the necessary
budget in accepted fact `19703e1e768865b1`.

The role of the closed boundary is now explicit.  Closed depth
\(d_{A_0}\ge m\) gives the weak inequalities in (9), (11), and (13).
The strict inequality in (24) does not come from replacing closed caps
by open caps.  It comes from infeasibility of the closed finite system
and the strict separation in (19).  Accepted fact
`4565d02e3cfa153e` is the corresponding strict-interior implication
when \(d_{A_0}>m\); the argument above supplies the missing exact
closed-containment converse.

## External sources

none
