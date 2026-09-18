---
fact_id: bf69b10cd2eb4fca
kind: lemma
author: "mp_r91_regime_b_concurrent_stability"
assurance: LLM-verified
subgoal_id: canonical-root-tail-regime-b-concurrent-stability
depends_on: ["5384a5033810a417","ab2620c83e116de2","fd7b02438ef66d42","fdfc3e7459f0e194"]
source_packet_sha256: cde9e6c8b6fe427fb7e5000bfe4e5614835ff4c9f6ee0b3e27daf80e1512c9b3
verifier_run: 27a81640d2a6458a
target_match: null
---

## Statement

Assume the canonical Regime B hypotheses in accepted facts
`ab2620c83e116de2`, `fd7b02438ef66d42`, and
`fdfc3e7459f0e194`, normalized by \(M=1\).  Write
\[
r=m,\qquad s=k,\qquad
\tau=\frac{2(1+r+s)}9,\qquad x=c_j,\qquad
q=r-\Delta_j,
\]
and let \(i,\ell\) be the two indices with nonempty low-lift intervals.
Then
\[
x>
\frac{(s-\tau)^2}{s}.
\tag{1}
\]
In particular, for every sequence of such configurations, whether or
not its Farkas-triangle areas tend to zero,
\[
\liminf_n\left(
c_{j,n}-\frac{(s_n-\tau_n)^2}{s_n}
\right)\geq0.
\tag{2}
\]
This conclusion remains valid if a Euclidean normalization of the
three line directions has a rank-one limit in which one positive
dependence coefficient vanishes and the other two limiting boundary
lines are opposite.

No canonical Regime B configuration, and hence no canonical Regime B
sequence with \(g_n\to0\), satisfies all the stated inequalities.

## Proof

Fix one configuration.  The two strict low-mass inequalities supplied
by the choices \(a_i\in I_i\) and \(a_\ell\in I_\ell\) are
\[
u_i+v_i+c_i<\tau,\qquad
u_\ell+v_\ell+c_\ell<\tau.
\tag{3}
\]
In particular,
\[
c_i,c_\ell<\tau.
\tag{4}
\]
Regime B has \(1/8<r<1/4\) and
\(\alpha=(5r+5s-4)/9>1/4\).  Hence
\[
r+s>\frac54.
\tag{5}
\]
Combining (5) with \(r<1/4\) gives
\[
5s>5\left(\frac54-r\right)>4(1+r).
\]
This is exactly
\[
\tau=\frac{2(1+r+s)}9<\frac s2.
\tag{6}
\]

Because the linear parts of \(f_i\) and \(f_\ell\) are nonparallel,
their zero lines meet in a unique point \(O\).  In the translated
variable \(z=w-O\), define
\[
\ell_i(z)=f_i(O+z),\qquad
\ell_\ell(z)=f_\ell(O+z),\qquad
\ell_j(z)=1+f_j(O+z).
\tag{7}
\]
The first two functions vanish at \(z=0\).  Since
\(f_i+f_\ell+f_j=-1\), the third also vanishes there, all three are
linear forms, and
\[
\ell_i+\ell_\ell+\ell_j=0.
\tag{8}
\]
Their linear parts are the pairwise nonparallel linear parts of
\(f_i,f_\ell,f_j\).  Thus accepted fact `5384a5033810a417` applies to
the translated convex body \(K-O\).  Put
\[
d_j=\left|K\cap\{f_j\leq-1\}\right|.
\]
The three cap areas in that theorem are \(c_i,c_\ell,d_j\).
Equations (4) and (6) verify its two half-area hypotheses, and the
theorem gives
\[
s\,d_j\geq(s-c_i)(s-c_\ell).
\tag{9}
\]
The deep cap is contained in the ordinary \(j\)-cap, so \(d_j\leq x\).
Using (4) in (9) therefore yields
\[
x\geq d_j
\geq\frac{(s-c_i)(s-c_\ell)}s
>
\frac{(s-\tau)^2}s.
\tag{10}
\]
This proves (1).

The argument is pointwise.  It does not take a limit of the bodies,
the intersection points \(O\), the line slopes, or an affine
normalizing map.  Therefore (10) immediately implies (2).  In
particular, it also covers the rank-one degeneration mentioned in the
subgoal.  More explicitly, if unit line normals are used and their
positive dependence coefficients are normalized to sum to one, a
coefficient tending to zero forces the other two unit normals to tend
to opposite vectors.  The limiting fan then fails the pairwise
nonparallel hypothesis, but this causes no loss: (9) was applied before
the limit for every \(n\), and its scalar inequality survives under
\(\liminf\).  No lower bound on a dependence coefficient, no bounded
condition number, and no bound on the lift slopes occurs in (9).
The assumption \(g_n\to0\) is therefore harmless and is not needed.

We next give the exact Regime B contradiction.  Put
\[
\alpha=\frac{5r+5s-4}{9},\qquad v=\sqrt q.
\]
Accepted fact `ab2620c83e116de2` gives
\[
x=\alpha-q<\alpha,
\tag{11}
\]
and its exact Regime B inequalities give
\[
s<1+r,\qquad
s<2-4r+3v^2,\qquad
r<\frac{5-6v+5v^2}{20}.
\tag{12}
\]
There is the identity
\[
\frac{(s-\tau)^2}{s}-\alpha
=\frac{\tau^2}{s}-r.
\tag{13}
\]
Indeed, after expanding the square, the part
\(s-2\tau-\alpha\) is \(-r\).

Define
\[
\Phi(r,s)=\frac{4(1+r+s)^2}{81s}-r
=\frac{\tau^2}{s}-r.
\]
On \(s<1+r\),
\[
\frac{\partial\Phi}{\partial s}
=\frac4{81}\,
\frac{(1+r+s)(s-1-r)}{s^2}<0.
\tag{14}
\]
We prove \(\Phi(r,s)>0\) throughout strict Regime B.

If \(r\leq16/65\), (12) and (14) give
\[
\Phi(r,s)>
\Phi(r,1+r)
=\frac{16-65r}{81}\geq0.
\tag{15}
\]

Suppose \(r>16/65\).  Since \(q<r<1/4\), one has \(0<v<1/2\).  The
last upper bound in (12), whose right side is decreasing for
\(0<v<1/2\), implies \(v<1/13\): otherwise
\[
r<
\frac{5-6v+5v^2}{20}
\leq
\frac{5-6/13+5/13^2}{20}
=\frac{193}{845}
<
\frac{16}{65},
\]
a contradiction.  Hence, for
\[
S=2-4r+3v^2,
\]
one has
\[
S-(1+r)=1-5r+3v^2
<
1-\frac{80}{65}+\frac3{169}<0.
\tag{16}
\]
By (12), \(s<S<1+r\), so (14) reduces positivity to
\(\Phi(r,S)>0\).  Its numerator has the sign of
\[
E(r,v)=
4-26r+40r^2+(8-35r)v^2+4v^4.
\tag{17}
\]
For \(r\leq1/4\),
\[
\frac{\partial E}{\partial r}
=-26+80r-35v^2<0.
\]
Writing
\[
B(v)=\frac{5-6v+5v^2}{20},
\]
the last inequality in (12) and direct substitution give
\[
E(r,v)>E(B(v),v)
=\frac9{20}v\left(4+3v+10v^2-5v^3\right)>0.
\tag{18}
\]
Equations (15)-(18) prove
\[
\Phi(r,s)>0.
\tag{19}
\]

Combining (10), (11), (13), and (19) gives the exact interior
contradiction
\[
x>
\frac{(s-\tau)^2}{s}
=\alpha+\Phi(r,s)
>\alpha>x.
\tag{20}
\]
Thus no strict Regime B point is geometrically realizable under the
canonical low-mass hypotheses.

For completeness, we now audit the closed limit and its unique
endpoint.  This part is redundant after the pointwise contradiction
(20), but it verifies that even retaining only the lower-semicontinuous
conclusion (2) leaves no boundary escape.

The Regime B bounds place
\[
\frac18<r_n<\frac14,\qquad
\frac54-r_n<s_n<1+r_n,\qquad
0<q_n<r_n
\]
in a bounded set.  Pass to a parameter subsequence with limits
\(r,s,q,x,\tau\).  By (11), (13), and continuity,
\[
x_n-\frac{(s_n-\tau_n)^2}{s_n}
=-\bigl(q_n+\Phi(r_n,s_n)\bigr).
\tag{21}
\]
The lower-semicontinuous inequality (2), together with (19), forces
\[
q_n\longrightarrow0,\qquad
\Phi(r_n,s_n)\longrightarrow0.
\tag{22}
\]
The strict inequalities \(\alpha_n>1/4\), \(q_n>\gamma_n\), and
\(s_n<1+r_n\) pass to
\[
r+s\geq\frac54,\qquad
s+4r\leq2,\qquad
s\leq1+r.
\tag{23}
\]

If \(r\leq1/5\), then (14) and (23) give
\[
\Phi(r,s)\geq
\Phi(r,1+r)
=\frac{16-65r}{81}
\geq\frac1{27}>0,
\]
contrary to (22).  If \(1/5\leq r\leq1/4\), then
\(s\leq2-4r\leq1+r\), and hence
\[
\Phi(r,s)\geq\Phi(r,2-4r)
=
\frac{(4r-1)(10r-4)}{9(2-4r)}
\geq0.
\tag{24}
\]
On this interval equality in (24) is possible only at \(r=1/4\).
Thus (22) forces \(r=1/4\).  Equations (23) then force \(s=1\).
Finally,
\[
\tau=\frac12,\qquad q=0,\qquad
\alpha=\frac14,\qquad x=\alpha-q=\frac14.
\tag{25}
\]
This is the unique feasible equality endpoint.

It remains to exclude (25) while retaining the endpoint geometry.
For each \(n\), keep
\[
d_{j,n}=\left|K_n\cap\{f_{j,n}\leq-1\}\right|.
\]
The chain used in (10) is
\[
(s_n-\tau_n)^2
<
(s_n-c_{i,n})(s_n-c_{\ell,n})
\leq s_nd_{j,n}
\leq s_nx_n.
\tag{26}
\]
At (25), the first and last expressions in (26) tend to \(1/4\).
Also
\[
s_n-c_{i,n}>s_n-\tau_n\longrightarrow\frac12,
\qquad
s_n-c_{\ell,n}>s_n-\tau_n\longrightarrow\frac12.
\]
The product squeeze in (26) therefore forces
\[
c_{i,n}\longrightarrow\frac12,\qquad
c_{\ell,n}\longrightarrow\frac12.
\tag{27}
\]
The two low-mass inequalities (3) now imply
\[
u_{i,n}+v_{i,n}\longrightarrow0,\qquad
u_{\ell,n}+v_{\ell,n}\longrightarrow0.
\tag{28}
\]

Use the simultaneous endpoint complements from accepted fact
`fd7b02438ef66d42`:
\[
E_{0,n}
=A_{0,n}\cap
\{f_{i,n}\geq a_{i,n},\,f_{\ell,n}\geq a_{\ell,n}\},
\]
\[
E_{2,n}
=A_{2,n}\cap
\{f_{i,n}\geq-a_{i,n},\,f_{\ell,n}\geq-a_{\ell,n}\}.
\]
Their union-bound estimates and (28) give
\[
|E_{0,n}|\geq1-u_{i,n}-u_{\ell,n}\longrightarrow1,
\qquad
|E_{2,n}|\geq r_n-v_{i,n}-v_{\ell,n}
\longrightarrow\frac14.
\tag{29}
\]
The reverse bounds \(|E_{0,n}|\leq1\) and
\(|E_{2,n}|\leq r_n\) show that both limits in (29) are exact.
Planar Brunn--Minkowski gives
\[
\liminf_n
\left|\frac{E_{0,n}+E_{2,n}}2\right|
\geq
\frac14\left(1+\frac12\right)^2
=\frac9{16}.
\tag{30}
\]
But the containment in accepted fact `fd7b02438ef66d42` puts this
midpoint body inside
\[
K_n\cap\{f_{j,n}\leq-1\}.
\]
Consequently its area is at most
\[
d_{j,n}\leq x_n\longrightarrow\frac14,
\]
contradicting (30).  The unique endpoint is impossible, including
when it is approached through a rank-one fan degeneration.

Therefore every canonical Regime B sequence is excluded.  In
particular, no such sequence with \(g_n\to0\) exists.

## External sources

none
