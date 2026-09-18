---
fact_id: b431dbefa8a4aec7
kind: lemma
author: "mp_r71_opposite_breakpoint_density"
assurance: LLM-verified
subgoal_id: canonical-opposite-hull-charge
depends_on: ["0e51a47a9add571f","a2a9387275a2c97c","eddda25c734d34bc"]
source_packet_sha256: 52cceff73ea2ca3b0e1b74c8380477113ae2a4da9a4c38403d6717452ccb63a6
verifier_run: a16d96d4091a401f
target_match: null
---

## Statement

Use the common-plane hypotheses and exact-cell convention of accepted fact `0e51a47a9add571f`.  Let \(N=\{j,k,\ell\}\), write \(0\) for \(\varnothing\), and put
\[
p_i=f_i-L_i,\qquad q_i=f_i+L_i.
\]
Let \(A_0,A_2,K\) be two-dimensional convex polygons with
\[
\frac{A_0+A_2}{2}\subseteq K.
\tag{1}
\]
Assume the positive-area exact cells have the central common-order support
\[
P_j,P_0,P_\ell,P_{k\ell},
\qquad
Q_j,Q_{jk},Q_N,Q_{k\ell},
\qquad
R_j,R_{jk},R_N,R_{k\ell},
\tag{2}
\]
and no others, and that all twelve cells in (2) have positive area.  Write
\[
b=|P_0|,\quad c=|P_\ell|,\quad
g_0=|Q_{jk}|,\quad g=|Q_N|,\quad y=|R_{jk}|.
\tag{3}
\]

Assume the scalar hypotheses of accepted fact `a2a9387275a2c97c`: with
\[
M=|A_0|,\quad m=|A_2|,\quad \kappa=|K|,
\quad t=\frac{2(M+m+\kappa)}9,
\]
the three crossing equalities, canonical tails, finite-interior conditions, and \(W=0\) hold.  Assume also \(M\ge m\), \(0<t<M\), and, for every \(i\in N\),
\[
\mu_i(a)=C_i+|A_0\cap\{f_i\le a\}|
                 +|A_2\cap\{f_i\le-a\}|,
\quad
C_i=|K\cap\{f_i\le0\}|,
\]
\[
I_i=\{a:\mu_i(a)<t\}\ne\varnothing,
\qquad L_i=\inf I_i.
\tag{4}
\]
Thus the three crossings are genuine lower crossings in the sense of accepted fact `eddda25c734d34bc`.

Define their one-sided chord traces by
\[
\rho_{0i}^+
=\lim_{\eta\downarrow0}
\frac{\mathcal H^1(A_0\cap\{f_i=L_i+\eta\})}
     {\|\nabla f_i\|},
\qquad
\rho_{2i}^-
=\lim_{\eta\downarrow0}
\frac{\mathcal H^1(A_2\cap\{f_i=-L_i-\eta\})}
     {\|\nabla f_i\|}.
\tag{5}
\]
Since \(\nabla f_j+\nabla f_k+\nabla f_\ell=0\), the three pairwise determinant magnitudes agree.  Put
\[
\Delta
=|\det(\nabla f_j,\nabla f_k)|
=|\det(\nabla f_j,\nabla f_\ell)|
=|\det(\nabla f_k,\nabla f_\ell)|>0
\tag{6}
\]
and
\[
\lambda_{0i}=\Delta\rho_{0i}^+,
\qquad
\lambda_{2i}=\Delta\rho_{2i}^-.
\tag{7}
\]

Consider the following three pairs of compact convex sets in
\(\mathbb R_{\ge0}^2\):
\[
\begin{array}{c|c|c}
rs&B_{rs}&D_{rs}\\ \hline
jk&
\{(p_j(w),p_k(w)):w\in\overline{P_0}\}&
\{(-q_j(w),-q_k(w)):w\in\overline{Q_N}\}\\[2mm]
j\ell&
\{(p_j(w),p_\ell(w)):w\in\overline{P_0}\}&
\{(-q_j(w),-q_\ell(w)):w\in\overline{Q_N}\}\\[2mm]
k\ell&
\{(p_k(w),-p_\ell(w)):w\in\overline{P_\ell}\}&
\{(-q_k(w),q_\ell(w)):w\in\overline{Q_{jk}}\}.
\end{array}
\tag{8}
\]
In each row, the first coordinate corresponds to \(r\) and the second to
\(s\).  Their coordinate areas are
\[
|B_{jk}|=|B_{j\ell}|=\Delta b,\qquad
|D_{jk}|=|D_{j\ell}|=\Delta g,
\tag{9}
\]
\[
|B_{k\ell}|=\Delta c,\qquad |D_{k\ell}|=\Delta g_0.
\tag{10}
\]

For a row \(rs\), call the two \(Q\)-traces retained in the paired cell if
\[
\mathcal H^1\!\left(D_{rs}\cap(\{0\}\times\mathbb R)\right)
\ge\lambda_{2r},
\qquad
\mathcal H^1\!\left(D_{rs}\cap(\mathbb R\times\{0\})\right)
\ge\lambda_{2s}.
\tag{11}
\]
Compatibility and the missing middle cells imply that there are
\(a_{rs},d_{rs}\ge0\), not both zero, such that
\[
a_{rs}X+d_{rs}Y
\le a_{rs}U+d_{rs}V
\quad
\text{for all }(X,Y)\in B_{rs},\ (U,V)\in D_{rs}.
\tag{12}
\]
Call a separator satisfying (12) nondegenerate if
\(a_{rs},d_{rs}>0\).  For any such chosen separator set
\[
\chi_{rs}
=\max_{(X,Y)\in B_{rs}}
  (a_{rs}X+d_{rs}Y)>0
\tag{13}
\]
and
\[
\Phi_{rs}
=\frac12\left(
\frac{\chi_{rs}}{a_{rs}}\lambda_{0r}
+\frac{\chi_{rs}}{d_{rs}}\lambda_{0s}
+\lambda_{0r}\lambda_{0s}
\right).
\tag{14}
\]

Fix a row \(rs\) in (8).  If its two \(Q\)-traces are retained as in
(11) and a chosen separator satisfying (12) is nondegenerate, then
\[
|B_{rs}|\le\Phi_{rs}
\tag{15}
\]
is impossible.

Under those same retained-trace and nondegenerate-separator hypotheses,
(15) follows in particular from
\[
\frac{a_{rs}\lambda_{0s}}{\chi_{rs}}
+\frac{d_{rs}\lambda_{0r}}{\chi_{rs}}
+\frac{a_{rs}d_{rs}\lambda_{0r}\lambda_{0s}}
       {\chi_{rs}^2}
\ge1.
\tag{16}
\]
Indeed, the chosen separator gives
\[
B_{rs}\subseteq
\{(X,Y)\in\mathbb R_{\ge0}^2:
  a_{rs}X+d_{rs}Y\le\chi_{rs}\}.
\tag{17}
\]
Consequently, only subject to retained traces (11) and a nondegenerate
separator, (16) excludes this breakpoint-density class.  As a special
conditional case, suppose additionally that \(B_{rs}\) is the full
separator triangle in (17) and its two active one-sided \(A_0\)-traces
span the two coordinate sides.  Then the first two fractions in (16) both
equal \(1\), so that row is impossible.  This conditional triangular
geometry allows affine nonconstant chord profiles and active polygonal
breakpoints.

Equivalently, fix any row satisfying retained traces (11).  For every
nondegenerate separator satisfying (12), every surviving configuration
must obey the strict bulging inequality
\[
|B_{rs}|>
\frac12\left(
\frac{\chi_{rs}}{a_{rs}}\lambda_{0r}
+\frac{\chi_{rs}}{d_{rs}}\lambda_{0s}
+\lambda_{0r}\lambda_{0s}
\right).
\tag{18}
\]
No conclusion (15), (16), or (18) is asserted for a row without retained
traces or without a nondegenerate separator.

## Proof

Accepted fact `eddda25c734d34bc` applies to (4) in each of the three
directions.  Its lexicographic alternative gives
\[
\rho_{0i}^+\le\rho_{2i}^-
\quad(i=j,k,\ell),
\qquad\text{hence}\qquad
\lambda_{0i}\le\lambda_{2i}.
\tag{19}
\]
If equality holds in (19), that fact additionally gives the strict
negative sum of the two relevant one-sided slopes.  The proof below needs
only the non-strict trace consequence, so it applies unchanged to that
breakpoint case.  It also applies when the first trace inequality is
strict.

We first derive (12) from compatibility.  Fix one row of (8).  If
\((X,Y)\in B_{jk}\) strictly dominates \((U,V)\in D_{jk}\), then the
corresponding endpoint pair has
\[
2f_j=X-U>0,\qquad 2f_k=Y-V>0.
\]
Since \(f_j+f_k+f_\ell=-1\), its midpoint lies in the strict middle cell
\(R_\ell\), which is absent from (2).  The same argument for the
\(j\ell\)-row gives the absent cell \(R_k\).  For the \(k\ell\)-row,
strict domination gives
\[
2f_k=X-U>0,\qquad 2f_\ell=V-Y<0.
\]
According to the sign of \(f_j\), the midpoint lies in \(R_\ell\) or
\(R_{j\ell}\); both are absent from (2).

These conclusions also hold for points in the closures in (8).  A strict
coordinate gap persists under approximation by interior points of the
positive-area endpoint cells.  The midpoint of two such interior points
is interior to \((A_0+A_2)/2\), hence interior to \(K\) by (1).  An
interior point of \(K\) in a forbidden open sign region would give that
forbidden exact cell positive area, contrary to (2).  In the
\(k\ell\)-row, if \(f_j=0\), every small ball with
\(f_k>0,f_\ell<0\) meets \(R_\ell\) or \(R_{j\ell}\) in positive area,
giving the same contradiction.  Therefore
\[
(B_{rs}-D_{rs})\cap(0,\infty)^2=\varnothing.
\tag{20}
\]

Separate the compact convex set \(B_{rs}-D_{rs}\) from the open positive
quadrant.  The separating functional has nonnegative coefficients: a
negative coefficient would be contradicted by sending the corresponding
coordinate of a point in the open quadrant to \(+\infty\).  Scaling
points of the open quadrant to the origin shows that the separating level
is at most zero.  Thus there are nonnegative \(a_{rs},d_{rs}\), not both
zero, such that
\[
a_{rs}(X-U)+d_{rs}(Y-V)\le0
\]
for every endpoint pair.  This proves (12).  If both coefficients are
positive, then \(\chi_{rs}>0\), because \(B_{rs}\) has positive area in
the positive quadrant, and (12)-(13) give
\[
a_{rs}X+d_{rs}Y\le\chi_{rs}
\le a_{rs}U+d_{rs}V.
\tag{21}
\]

Now fix a row having retained traces and a chosen nondegenerate
separator.  Its two coordinate-axis sections of \(D_{rs}\) are intervals.
Define their four endpoints \(x_0,x_1,y_0,y_1\) by
\[
D_{rs}\cap\{U=0\}
=\{(0,y):y_0\le y\le y_1\},
\qquad
D_{rs}\cap\{V=0\}
=\{(x,0):x_0\le x\le x_1\}.
\tag{22}
\]
The right inequality in (21) gives
\[
y_0\ge\frac{\chi_{rs}}{d_{rs}},
\qquad
x_0\ge\frac{\chi_{rs}}{a_{rs}}.
\tag{23}
\]
The retained-trace hypothesis (11) and (19) give
\[
y_1-y_0\ge\lambda_{2r}\ge\lambda_{0r},
\qquad
x_1-x_0\ge\lambda_{2s}\ge\lambda_{0s}.
\tag{24}
\]

Convexity puts the convex hull of the two intervals in (22) inside
\(D_{rs}\).  Its area is
\[
\begin{aligned}
\frac12(x_1y_1-x_0y_0)
={}&\frac12\bigl(
x_0(y_1-y_0)+y_0(x_1-x_0)\\
&\hspace{27mm}+(x_1-x_0)(y_1-y_0)
\bigr).
\end{aligned}
\tag{25}
\]
Using (23)-(24) in (25) proves
\[
|D_{rs}|\ge\Phi_{rs}.
\tag{26}
\]
Consequently, (15) would give
\[
|D_{rs}|\ge|B_{rs}|.
\tag{27}
\]

For the \(jk\)- and \(j\ell\)-rows, (9) turns (27) into \(g\ge b\).
By the exact coefficient convention in accepted fact
`0e51a47a9add571f`, the only negative term of \(W\) is
\(-2p_0=-2b\), while the coefficient of \(q_N=g\) is \(7\).
Thus \(W=0\) gives
\[
2b\ge7g.
\tag{28}
\]
Since \(b,g>0\), (27)-(28) are incompatible.

For the \(k\ell\)-row, (10) turns (27) into \(g_0\ge c\).  On the other
hand, subtract the \(\ell\)-crossing from the \(k\)-crossing.  From the
support (2), these two equalities are
\[
|P_{k\ell}|+(g_0+g+|Q_{k\ell}|)
 +(y+|R_N|+|R_{k\ell}|)=t,
\]
\[
(c+|P_{k\ell}|)+(g+|Q_{k\ell}|)
 +(|R_N|+|R_{k\ell}|)=t.
\]
Hence
\[
c=g_0+y>g_0,
\tag{29}
\]
contradicting (27).  This proves the impossibility of (15) under the
retained-trace and nondegenerate-separator hypotheses.

It remains to verify the sufficient density condition (16), still under
those same two hypotheses.  Inclusion (17) gives
\[
|B_{rs}|\le\frac{\chi_{rs}^2}
                    {2a_{rs}d_{rs}}.
\tag{30}
\]
The right side of (14), divided by the right side of (30), is exactly
\[
\frac{d_{rs}\lambda_{0r}}{\chi_{rs}}
+\frac{a_{rs}\lambda_{0s}}{\chi_{rs}}
+\frac{a_{rs}d_{rs}\lambda_{0r}\lambda_{0s}}
       {\chi_{rs}^2}.
\]
Thus (16) implies \(|B_{rs}|\le\Phi_{rs}\), and the already proved
conditional contradiction applies.  Under retained traces and a
nondegenerate separator, negating (15) gives (18).  No step assumed that a
chord profile was constant or that an active level avoided a polygonal
breakpoint.

## External sources

none
