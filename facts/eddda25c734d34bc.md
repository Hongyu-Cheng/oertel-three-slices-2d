---
fact_id: eddda25c734d34bc
kind: lemma
author: "mp_r70_opposite_lower_crossing_density"
assurance: LLM-verified
subgoal_id: canonical-opposite-hull-charge
depends_on: ["0e51a47a9add571f","624b129b68e0fdee","a2a9387275a2c97c","ddfaf5f0795fa456","fbf19a78233b5ef1"]
source_packet_sha256: 43947dd5709775d6bf6c8605d46532ad235e48e97d653301bb26938395ffe7ed
verifier_run: 0ccb97dd01c04d68
target_match: null
---

## Statement

Let \(P,Q\subset\mathbb R^2\) be nonempty two-dimensional convex polygons, let
\[
|P|=M\ge m=|Q|>0,
\]
let \(\varphi:\mathbb R^2\to\mathbb R\) be a nonconstant affine function, and let \(c\ge0\) and \(0<t<M\).  Define
\[
F_P(a)=|P\cap\{\varphi\le a\}|,\qquad
F_Q(a)=|Q\cap\{\varphi\le a\}|,
\]
\[
\mu(a)=c+F_P(a)+F_Q(-a),\qquad
I=\{a:\mu(a)<t\}.
\]
Assume \(c+m\ge t\), \(I\ne\varnothing\), and
\[
L=\inf I.
\]
These are the lower-crossing hypotheses of accepted fact `624b129b68e0fdee`, so \(\mu(L)=t\).

For \(R=P,Q\), define the chord density
\[
\rho_R(s)=
\frac{\mathcal H^1(R\cap\{\varphi=s\})}
     {\|\nabla\varphi\|},
\]
with value \(0\) when the section is empty.  At a projected polygonal breakpoint use the following one-sided traces and slopes:
\[
\rho_P^+(L)=\lim_{\eta\downarrow0}\rho_P(L+\eta),\qquad
\dot\rho_P^+(L)=
\lim_{\eta\downarrow0}
\frac{\rho_P(L+\eta)-\rho_P^+(L)}{\eta},
\]
\[
\rho_Q^-(-L)=\lim_{\eta\downarrow0}\rho_Q(-L-\eta),\qquad
\dot\rho_Q^-(-L)=
\lim_{\eta\downarrow0}
\frac{\rho_Q(-L-\eta)-\rho_Q^-(-L)}{-\eta}.
\]
All four limits exist.  Exactly one of the following alternatives holds:
\[
\rho_P^+(L)<\rho_Q^-(-L),
\tag{1}
\]
or
\[
\rho_P^+(L)=\rho_Q^-(-L)
\quad\hbox{and}\quad
\dot\rho_P^+(L)+\dot\rho_Q^-(-L)<0.
\tag{2}
\]
Equivalently, the pair
\[
\left(
\rho_P^+(L)-\rho_Q^-(-L),\,
\dot\rho_P^+(L)+\dot\rho_Q^-(-L)
\right)
\tag{3}
\]
is lexicographically negative.  Conversely, if \(\mu(L)=t\), then (1) or (2) is equivalent to
\[
\mu(L+\eta)<t
\quad\hbox{for every sufficiently small }\eta>0.
\tag{4}
\]
In particular, equality in both entries of (3) is impossible at a genuine lower crossing; a polygon has no higher-order local escape.

The one-sided convention gives the exact breakpoint and zero-area-cap cases.  If \(L<\min_P\varphi\), then
\[
\rho_P^+(L)=\dot\rho_P^+(L)=0.
\]
If \(L=\min_P\varphi\), then \(\rho_P^+(L)\) is the normalized length of the minimizing edge, and is \(0\) when the minimizing face is a vertex; \(\dot\rho_P^+(L)\) is the slope of the first interior chord piece.  The analogous statements at \(-L=\max_Q\varphi\) use the left trace and left slope.  Hence, in the empty-full equality case from `624b129b68e0fdee`,
\[
L=-\max_Q\varphi\le\min_P\varphi,
\tag{5}
\]
if the inequality in (5) is strict, then (1) holds when the maximizing face of \(Q\) is an edge, while (2) holds when it is a vertex.  If equality holds in (5), the normalized lengths of the minimizing face of \(P\) and maximizing face of \(Q\) are compared first, and, only when those lengths agree, the two indicated interior slopes are compared by (2).  At an interior projected vertex the same rule applies with the right chord piece of \(P\) and the left chord piece of \(Q\).

Apply this to the exact-cell convention of accepted fact `0e51a47a9add571f` and the scalar setting of accepted fact `a2a9387275a2c97c`.  Let \(N=\{j,k,\ell\}\), let
\[
f_j+f_k+f_\ell=-1,\qquad L_j+L_k+L_\ell<-1,
\]
and let \(A_0,A_2,K\) be two-dimensional convex polygons satisfying
\[
\frac{A_0+A_2}{2}\subseteq K.
\tag{6}
\]
Write
\[
p_i=f_i-L_i,\qquad q_i=f_i+L_i.
\]
Assume that, in Euclidean coordinates \((r,\omega)\), there are constants
\(\alpha_i,\beta_i\) such that
\[
\begin{array}{lll}
p_k=\alpha_k-r,&p_\ell=\alpha_\ell+\omega-r,
&p_j=2r-\omega-2\alpha_j,\\
q_k=\beta_k-r,&q_\ell=\beta_\ell+\omega-r,
&q_j=2r-\omega-2\beta_j.
\end{array}
\tag{7}
\]
Put
\[
\gamma_i=\frac{\alpha_i+\beta_i}{2}.
\]
Assume
\[
A_0=[r_0^-,r_0^+]\times[-h_0/2,h_0/2],\quad
A_2=[r_2^-,r_2^+]\times[-h_2/2,h_2/2],
\]
\[
K=[r_1^-,r_1^+]\times[-h_1/2,h_1/2],
\qquad h_0,h_2,h_1>0,
\tag{8}
\]
and that all nine cutting graphs in (7) and their \(f_i=0\) averages cross the full horizontal sides strictly.  Assume their sectionwise orders are
\[
\alpha_j+\frac{\omega}{2}
 <\alpha_\ell+\omega<\alpha_k
\quad (|\omega|\le h_0/2),
\tag{9}
\]
\[
\beta_k<\beta_\ell+\omega
 <\beta_j+\frac{\omega}{2}
\quad (|\omega|\le h_2/2),
\tag{10}
\]
\[
\gamma_k<\gamma_\ell+\omega
 <\gamma_j+\frac{\omega}{2}
\quad (|\omega|\le h_1/2).
\tag{11}
\]
Thus the only positive cells, in section order, are
\[
P_{\{j\}},P_\varnothing,P_{\{\ell\}},P_{\{k,\ell\}}
\quad\hbox{with areas }a,b,c_0,d,
\]
\[
Q_{\{j\}},Q_{\{j,k\}},Q_N,Q_{\{k,\ell\}}
\quad\hbox{with areas }e,g_0,g,s,
\]
\[
R_{\{j\}},R_{\{j,k\}},R_N,R_{\{k,\ell\}}
\quad\hbox{with areas }x,y,z,w,
\tag{12}
\]
and all twelve displayed areas are positive.  This is the full-transverse coaxial-rectangle central common-order family containing the realization of accepted fact `fbf19a78233b5ef1`.

Let
\[
M=|A_0|,\qquad m=|A_2|,\qquad \kappa=|K|,\qquad
t=\frac{2(M+m+\kappa)}9,
\]
\[
u_i=|A_0\cap\{f_i\le L_i\}|,\quad
v_i=|A_2\cap\{f_i\le-L_i\}|,\quad
C_i=|K\cap\{f_i\le0\}|.
\]
Assume \(M\ge m\), \(0<t<M\), the three crossings
\[
u_i+v_i+C_i=t\qquad(i=j,k,\ell),
\tag{13}
\]
the canonical tails and finite-interior conditions
\[
C_i+m\ge t,\qquad C_i+M>t,
\tag{14}
\]
\[
0<u_i<M,\qquad0<v_i<m,\qquad0<C_i<\kappa,
\tag{15}
\]
and \(W=0\), where
\[
W=
\sum_J(3|J|-2)|P_J|
+\sum_H(3|H|-2)|Q_H|
+\sum_G(3|G|-2)|R_G|.
\tag{16}
\]
Finally, for every \(i=j,k,\ell\), define
\[
\mu_i(a)=C_i+|A_0\cap\{f_i\le a\}|
               +|A_2\cap\{f_i\le-a\}|,
\qquad
I_i=\{a:\mu_i(a)<t\},
\tag{17}
\]
and require
\[
I_i\ne\varnothing,\qquad L_i=\inf I_i.
\tag{18}
\]
Then no such configuration exists.  Consequently, the positive-\(p_\varnothing\) central common-order branch is empty throughout the full-transverse coaxial-rectangle class once its three nominal crossings are required to be genuine lower crossings.  Accepted fact `ddfaf5f0795fa456` found the opposite derivative in the particular rectangle of `fbf19a78233b5ef1`; the present conclusion excludes every choice of the three rectangle widths and all cell margins, not only that example.

## Proof

For a polygon \(R\), the coarea formula gives, for \(a<b\),
\[
|R\cap\{a<\varphi\le b\}|=\int_a^b\rho_R(s)\,ds.
\tag{19}
\]
Between consecutive values of \(\varphi\) at polygon vertices, the two endpoints of the chord lie on fixed edges, so \(\rho_R\) is affine.  It follows that all traces and slopes in the statement exist, including at a support edge where the interior trace may differ from the exterior value \(0\).  This is the one-sided refinement of the piecewise-quadratic regularity in accepted fact `624b129b68e0fdee`.

Choose \(\varepsilon>0\) so that neither \(P\) on the right of \(L\) nor \(Q\) on the left of \(-L\) has another projected breakpoint within distance \(\varepsilon\).  For \(0<\eta<\varepsilon\), affine chord variation and (19) give the exact identity
\[
\begin{aligned}
\mu(L+\eta)-\mu(L)
={}&
\bigl(\rho_P^+(L)-\rho_Q^-(-L)\bigr)\eta\\
&+\frac12
\bigl(\dot\rho_P^+(L)+\dot\rho_Q^-(-L)\bigr)\eta^2.
\end{aligned}
\tag{20}
\]
The plus sign before \(\dot\rho_Q^-(-L)\) is forced by the two reversals: the \(Q\)-threshold moves from \(-L\) to \(-L-\eta\), and the removed area is subtracted.

Accepted fact `624b129b68e0fdee` gives \(\mu(L)=t\).  Since \(L=\inf I\), there are points of \(I\) arbitrarily close to \(L\) from the right.  The quadratic in (20) is therefore negative for arbitrarily small positive \(\eta\).  Its first nonzero coefficient must be negative.  It cannot have both coefficients zero, since then \(\mu=t\) on a whole interval to the right of \(L\), contradicting the definition of the infimum.  This proves (1)-(3), and (20) also proves the converse (4).

For the breakpoint assertions, a threshold strictly outside a support interval has zero chord density and zero slope on the relevant side.  At a support edge, the interior trace is its positive normalized length.  At a support vertex, the trace is zero and the first interior chord piece has nonzero affine slope: positive at a minimizing vertex and negative at a maximizing vertex.  Substitution in (1)-(2) proves every case following (5).  This also shows explicitly why actual section values at a support edge must not replace the one-sided trace.  There is no cubic or higher case because (20) is exactly quadratic until the next projected breakpoint.

We now prove the rectangular exclusion.  The canonical tails (14), together with (18), put all three \(L_i\) under the lower-crossing conclusion of `624b129b68e0fdee`; (13) identifies their common crossing value.  Because every cutting graph crosses the full horizontal sides strictly, its chord density is constant under a sufficiently small threshold displacement.  From (7), the coefficients of \(r\) are
\[
|\lambda_j|=2,\qquad |\lambda_k|=|\lambda_\ell|=1.
\]
Thus the three instances of (1)-(2) are respectively
\[
\frac{h_0}{2}<\frac{h_2}{2},\qquad
h_0<h_2,\qquad h_0<h_2.
\tag{21}
\]
Equality cannot occur because all six relevant one-sided slopes vanish, which would give the forbidden local plateau in (20).  Hence every genuine lower crossing forces
\[
h_0<h_2.
\tag{22}
\]
This is the exact three-direction version of the rectangle calculation recorded for the stress test in accepted fact `ddfaf5f0795fa456`.

Set
\[
\Delta_\alpha=\alpha_k-\alpha_\ell,\qquad
\Delta_\beta=\beta_\ell-\beta_k.
\]
Equations (9)-(10) at \(\omega=0\) give
\[
\Delta_\alpha>0,\qquad\Delta_\beta>0.
\]
Equation (11) at \(\omega=0\), together with the definition of \(\gamma_i\), gives
\[
0<2(\gamma_\ell-\gamma_k)
=\Delta_\beta-\Delta_\alpha,
\]
and hence
\[
\Delta_\beta>\Delta_\alpha.
\tag{23}
\]
Direct integration across the symmetric transverse intervals in (8) gives
\[
c_0=|P_{\{\ell\}}|=h_0\Delta_\alpha,\qquad
g_0=|Q_{\{j,k\}}|=h_2\Delta_\beta.
\tag{24}
\]
Combining (22)-(24) yields
\[
g_0>c_0.
\tag{25}
\]

On the other hand, the \(k\)- and \(\ell\)-crossings in (13), using the exact support (12) from the convention of accepted fact `0e51a47a9add571f`, are
\[
d+(g_0+g+s)+(y+z+w)=t,
\]
\[
(c_0+d)+(g+s)+(z+w)=t.
\]
Subtracting gives
\[
c_0=g_0+y.
\tag{26}
\]
Since \(y=|R_{\{j,k\}}|>0\), (26) gives \(c_0>g_0\), contradicting (25).  This proves the asserted nonexistence.  Notice that the contradiction already follows from two crossings once the three lower-crossing directions and central order have been imposed.  The remaining assumptions from `a2a9387275a2c97c`, including compatibility (6), \(W=0\), and the unused third crossing, only narrow the excluded class further.

The realization in `fbf19a78233b5ef1` avoids this contradiction precisely by taking \(h_0>h_2\); accepted fact `ddfaf5f0795fa456` then verifies that all three nominal crossings have strict-low-mass points on their left.  Conversely, changing to \(h_0<h_2\) repairs the local direction but forces (25), which is incompatible with the crossing identity (26).  Therefore the next unresolved central common-order case must leave the constant-density regime: at least one active cut must meet a polygonal breakpoint or have a nonconstant affine chord profile, and any equal-density breakpoint must satisfy the strict slope inequality (2).

## External sources

none
