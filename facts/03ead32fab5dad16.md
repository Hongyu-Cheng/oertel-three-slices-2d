---
fact_id: 03ead32fab5dad16
kind: lemma
author: "mp_r64_opposite_crossing_coupled_budget"
assurance: LLM-verified
subgoal_id: canonical-opposite-hull-charge
depends_on: ["0e51a47a9add571f","a2a9387275a2c97c"]
source_packet_sha256: 89711bce9b9213291cb6020ea1c0056c18459830ccf8df3843e02b730dbd2bf6
verifier_run: 4b0274067ec24532
target_match: null
---

## Statement

Assume the canonical common-plane hypotheses, exact-cell convention, crossings, tails, finite interior, \(W=0\), and positive opposite pair from accepted fact `a2a9387275a2c97c`, with the sign cells interpreted as in accepted fact `0e51a47a9add571f`.  Fix \(j\), write \(N\setminus\{j\}=\{k,\ell\}\), assume \(p_\varnothing>0\), and put
\[
\delta=-1-(L_1+L_2+L_3)>0.
\]
After relabeling \(k,\ell\) if necessary, make an invertible affine change of planar coordinates to \((r,w)\) in which
\[
\begin{array}{lll}
p_k=\alpha_k-r,&p_\ell=\alpha_\ell+w-r,
&p_j=2r-w-2\alpha_j,\\
q_k=\beta_k-r,&q_\ell=\beta_\ell+w-r,
&q_j=2r-w-2\beta_j,
\end{array}
\tag{1}
\]
where \(p_i=f_i-L_i\) and \(q_i=f_i+L_i\).  Thus
\[
\alpha_k+\alpha_\ell-2\alpha_j=\delta,\qquad
\beta_k+\beta_\ell-2\beta_j=-(\delta+2).
\tag{2}
\]
Normalize planar area by the common positive Jacobian of this affine change.

Assume the following common-strip rectangular structure:
\[
A_0=I_0\times J_0,\qquad
A_2=I_2\times J_2,\qquad
K=I\times J,
\tag{3}
\]
where all six intervals have positive length.  Write
\[
|I_0|=A,\quad |I_2|=B,\quad |I|=C,\qquad
|J_0|=h_0,\quad |J_2|=h_2,\quad |J|=h.
\tag{4}
\]
Assume that, on the full corresponding \(w\)-interval, every zero graph of the three \(p_i\) lies strictly between the two endpoints of \(I_0\), every zero graph of the three \(q_i\) lies strictly between the endpoints of \(I_2\), and every zero graph of the three \(f_i\) lies strictly between the endpoints of \(I\).

Assume in addition that the exact positive \(Q\)-support is one of the following two minimal paths, with the indicated uniform left-to-right order of its zero graphs on \(J_2\):
\[
\{j\},\{j,k\},\{k\},\{k,\ell\},
\qquad
\beta_k<\beta_j+\frac w2<\beta_\ell+w
\tag{5o}
\]
or
\[
\{j\},\{j,k\},N,\{k,\ell\},
\qquad
\beta_k<\beta_\ell+w<\beta_j+\frac w2.
\tag{5c}
\]
Then the outer case (5o) necessarily satisfies
\[
(\delta-38)h_0>(91\delta+190)h_2,
\tag{6o}
\]
and the central case (5c) necessarily satisfies
\[
(3\delta-14)h_0>(33\delta+70)h_2.
\tag{6c}
\]
In particular, the outer case is impossible unless
\[
\delta>38,\qquad
\frac{h_0}{h_2}>
\frac{91\delta+190}{\delta-38},
\tag{7o}
\]
and the central case is impossible unless
\[
\delta>\frac{14}{3},\qquad
\frac{h_0}{h_2}>
\frac{33\delta+70}{3\delta-14}.
\tag{7c}
\]

## Proof

The affine normalization in (1) is available because the three nonparallel linear parts sum to zero.  Choose the \(r,w\) coordinates so that the linear parts indexed by \(k,\ell\) are \((-1,0)\) and \((-1,1)\); the remaining one is then \((2,-1)\).  Since
\[
\sum_ip_i=\delta,\qquad
\sum_iq_i=-(\delta+2),
\]
their constants give (2).  Also \(2f_i=p_i+q_i\).  Therefore, with
\[
\gamma_s=\frac{\alpha_s+\beta_s}{2}\qquad(s=j,k,\ell),
\]
the three middle functions have the same form as (1), with \(\alpha\) replaced by \(\gamma\), and
\[
\gamma_k+\gamma_\ell-2\gamma_j=-1.
\tag{8}
\]
An affine coordinate change multiplies every planar area by the same positive constant, so dividing by that constant does not change any crossing equation or any conclusion below.

Let the right endpoint of \(I_0\) be \(b_0\), the left endpoint be \(a_0\), and let \(J_0=[s_0,s_0+h_0]\).  The full-transverse assumption permits direct integration of the three halfspace cuts:
\[
\begin{aligned}
u_k&=\int_{J_0}(b_0-\alpha_k)\,dw,\\
u_\ell&=\int_{J_0}(b_0-\alpha_\ell-w)\,dw,\\
u_j&=\int_{J_0}\left(\alpha_j+\frac w2-a_0\right)\,dw.
\end{aligned}
\tag{9}
\]
The \(w\)-terms cancel in the nonuniform combination \(1,1,2\).  Using (2) gives
\[
u_k+u_\ell+2u_j
=2Ah_0-\delta h_0
=2M-\delta h_0.
\tag{10}
\]
The identical calculation for \(A_2\), using the second relation in (2), gives
\[
v_k+v_\ell+2v_j
=2Bh_2+(\delta+2)h_2
=2m+(\delta+2)h_2.
\tag{11}
\]
The calculation for \(K\), using (8), gives
\[
c_k+c_\ell+2c_j
=2Ch+h
=2\kappa+h.
\tag{12}
\]

All three separate crossing equations from accepted fact
`a2a9387275a2c97c` have the same right side
\[
t=\frac{2(M+m+\kappa)}9.
\]
Taking their \(1,1,2\) combination and applying (10)-(12) yields
\[
4t
=2(M+m+\kappa)-\delta h_0+(\delta+2)h_2+h.
\tag{13}
\]
Substitution of the displayed value of \(t\) gives the exact
crossing-coupled identity
\[
\boxed{\;
\delta h_0-(\delta+2)h_2-h
=\frac{10}{9}(M+m+\kappa).
\;}
\tag{14}
\]
Unlike the equal-weight sum of the crossings, (14) retains the
three offset sums \(\delta,-(\delta+2),-1\) separately.

We next use the endpoint hull and midpoint geometry.  Under either
order in (5), the left vertical edge of \(A_2\) lies in \(Q_{\{j\}}\)
and its right vertical edge lies in \(Q_{\{k,\ell\}}\).  Their closures
therefore contain the two opposite vertical edges of the rectangle.
Consequently
\[
\operatorname{conv}\!\left(
\overline{Q_{\{j\}}}\cup
\overline{Q_{\{k,\ell\}}}
\right)=A_2.
\tag{15}
\]
Thus the endpoint hull \(H\) from accepted fact
`a2a9387275a2c97c` is the whole of \(A_2\).  Moreover,
\[
\frac{A_0+A_2}{2}\subseteq K
\]
forces the two projection inequalities
\[
C\ge\frac{A+B}{2},
\qquad
h\ge\frac{h_0+h_2}{2}.
\tag{16}
\]

At any fixed \(w\in J_0\), the three \(P\)-zero positions satisfy
\[
\alpha_k+(\alpha_\ell+w)
-2\left(\alpha_j+\frac w2\right)=\delta.
\tag{17}
\]
At least one of the first two positions is at least
\(\delta/2\) to the right of the third.  Since all three positions
are strictly inside \(I_0\),
\[
A>\frac{\delta}{2}.
\tag{18}
\]

Put \(D=\delta+2\).  In the outer order (5o), if the distances from
the middle \(q_j\)-zero to the left \(q_k\)-zero and to the right
\(q_\ell\)-zero are \(d_-\) and \(d_+\), respectively, then (2) says
\[
d_--d_+=D.
\]
Both distances are positive, so the full span is
\[
d_-+d_+=D+2d_+>D.
\]
All three graphs lie strictly inside \(I_2\), hence
\[
B>D
\qquad\text{in the outer case.}
\tag{19o}
\]
In the central order (5c), let the distances from the rightmost
\(q_j\)-zero to the \(q_k\)- and \(q_\ell\)-zeros be \(d_k>d_\ell>0\).
Equation (2) gives
\[
d_k+d_\ell=D,
\]
so \(d_k>D/2\) and
\[
B>\frac D2
\qquad\text{in the central case.}
\tag{19c}
\]

For the outer path, (16), (18), and (19o) imply
\[
\begin{aligned}
M&>\frac{\delta h_0}{2},\\
m&>Dh_2,\\
\kappa&=Ch>
\left(\frac{3\delta}{4}+1\right)h.
\end{aligned}
\tag{20o}
\]
Insert (20o) into (14):
\[
\delta h_0-Dh_2-h
>
\frac{5\delta}{9}h_0
+\frac{10D}{9}h_2
+\left(\frac{5\delta}{6}+\frac{10}{9}\right)h.
\]
After multiplying by \(18\),
\[
8\delta h_0>38Dh_2+(15\delta+38)h.
\tag{21o}
\]
Using the second inequality in (16) and \(D=\delta+2\) in (21o)
gives
\[
\begin{aligned}
16\delta h_0
&>(15\delta+38)h_0
+\bigl(76D+15\delta+38\bigr)h_2\\
&=(15\delta+38)h_0+(91\delta+190)h_2.
\end{aligned}
\]
This is exactly (6o), and (7o) follows because \(h_0,h_2>0\).

For the central path, (16), (18), and (19c) imply
\[
\begin{aligned}
M&>\frac{\delta h_0}{2},\\
m&>\frac{Dh_2}{2},\\
\kappa&=Ch>\frac{\delta+1}{2}h.
\end{aligned}
\tag{20c}
\]
Substitution in (14), followed by multiplication by \(9\), gives
\[
4\delta h_0>14Dh_2+(5\delta+14)h.
\tag{21c}
\]
Using (16) once more,
\[
\begin{aligned}
8\delta h_0
&>(5\delta+14)h_0
+\bigl(28D+5\delta+14\bigr)h_2\\
&=(5\delta+14)h_0+(33\delta+70)h_2.
\end{aligned}
\]
This is (6c), and positivity of \(h_0,h_2\) gives (7c).

Thus both minimal opposite path types are excluded throughout the
stated common-strip regime except for the explicit extreme
transverse-width ranges in (7o) and (7c).

## External sources

none
