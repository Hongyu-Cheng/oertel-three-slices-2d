---
fact_id: 9aa5e8e4ddcd1c62
kind: lemma
author: "mp_r391_profile_augmented_onezero"
assurance: LLM-verified
subgoal_id: counterexample-opposite-asymmetric-low-r
depends_on: ["0e51a47a9add571f","38b9d85f6c0c57a2","cc8c0bf6093b9357"]
source_packet_sha256: ba7645a0532ec235ef0d1fae6c38764372f5da419c93c0d96bab068d8d0e4c44
verifier_run: 4ff51eb47f934aa0
target_match: null
---

## Statement

Use the common-plane exact-cell convention of accepted fact
`0e51a47a9add571f`.  Put
\[
\pi_i=f_i-L_i,\qquad
\delta=-1-(L_1+L_2+L_3)>0,
\]
and let \(p_J=|P_J|\), \(q_J=|Q_J|\).  Under the positivity
hypotheses
\[
p_{12}p_{13}p_{23}q_1q_3q_{12}>0,
\tag{1}
\]
accepted fact `cc8c0bf6093b9357` gives the full central
\(P\)-triangle in \(A_0\).  For distinct \(i,j,k\in\{1,2,3\}\), put
\[
\alpha_i=\frac{p_i}{p_0},\qquad
\alpha_j=\frac{p_j}{p_0}.
\]
Whenever \(\alpha_i\alpha_j<1\),
\[
\boxed{\quad
p_{ij}\le
2p_0\,
\frac{\alpha_i\alpha_j(1+\alpha_i)(1+\alpha_j)}
     {(1-\alpha_i\alpha_j)^2}.
\quad}
\tag{2}
\]
Thus (2) holds cyclically for \(ij=12,13,23\).

Here is an exact one-zero table satisfying all three instances of
(2) and all scalar/cell conditions certified for the table of
accepted fact `38b9d85f6c0c57a2`.  Put
\[
D=16072081,\qquad
\delta=10,\qquad
\gamma=\frac{320000}{D},
\qquad
\varepsilon=\frac{126243}{32144162000}.
\tag{3}
\]
The endpoint \(P\)-masses are
\[
\begin{array}{c|rrrrrrr}
J&0&1&2&3&12&13&23\\ \hline
p_J&
\frac{16000000}{D}&
\frac{24009}{D}&\frac{24009}{D}&\frac{24009}{D}&
\frac{18}{D}&\frac{18}{D}&\frac{18}{D}.
\end{array}
\tag{4}
\]
Keep the \(Q\)-table from accepted fact `38b9d85f6c0c57a2`:
\[
\begin{array}{c|rrrrrrr}
H&1&2&3&12&13&23&123\\ \hline
q_H&
\frac{11}{2000}&0&\frac1{2000}&
\frac3{2000}&\frac1{2000}&\frac3{2000}&\frac1{2000}.
\end{array}
\tag{5}
\]
In particular, \(q_2=0\) and every other non-forced endpoint cell is
positive.

Define the following exact base tables:
\[
\begin{array}{c|rrrrrrr}
G&1&2&3&12&13&23&123\\ \hline
\bar\rho_G&
\frac{4327}{15000}&
\frac{2603}{10000}&
\frac{2611}{10000}&
\frac{61}{45000}&
\frac{19}{18000}&
\frac{607}{18000}&
\frac{18}{125}\\[1mm]
\bar r_G&
\frac{1039}{3600}&
\frac{293}{1125}&
\frac{4703}{18000}&
\frac1{720}&
\frac{19}{18000}&
\frac{607}{18000}&
\frac{18}{125}.
\end{array}
\tag{6}
\]
The repaired formal midpoint and completion tables are
\[
\rho_i=\bar\rho_i-\frac{\varepsilon}{2},\qquad
r_i=\bar r_i-\frac{\varepsilon}{2}
\quad(i=1,2,3),
\tag{7}
\]
\[
\rho_{ij}=\bar\rho_{ij},\qquad
r_{ij}=\bar r_{ij}
\quad(ij=12,13,23),
\tag{8}
\]
\[
\rho_{123}=\bar\rho_{123}+\frac{3\varepsilon}{2},
\qquad
r_{123}=\bar r_{123}+\frac{3\varepsilon}{2}.
\tag{9}
\]
Put \(x_G=r_G-\rho_G\) and \(s_3=1/2000\).  Then
\[
M=1,\qquad m=\frac1{100},\qquad
k_0=\sum_G\rho_G=\frac{99}{100},\qquad
k=\sum_Gr_G=\frac{1981}{2000},
\qquad
\sum_Gx_G=\frac1{2000}.
\tag{10}
\]

For
\[
u_i=\sum_{J\ni i}p_J,\quad
v_i=\sum_{H\ni i}q_H,\quad
b_i^0=\sum_{G\ni i}\rho_G,\quad
b_i=\sum_{G\ni i}r_G,\quad
d_i=u_i+v_i,
\tag{11}
\]
all three exact crossings hold:
\[
d_i+b_i=\frac{4001}{9000}\qquad(i=1,2,3).
\tag{12}
\]
Both canonical tails are strict, \(W=0\), and
\[
\frac mM<\frac38,\qquad M-m<k<M+m.
\tag{13}
\]
If
\[
\mathcal R_X(c_1,c_2,c_3)
=5(c_1+c_2+c_3)-6\min_i c_i-4X,
\tag{14}
\]
then the four convex three-cap tests are strict:
\[
\mathcal R_M(M-u_1,M-u_2,M-u_3)>0,\quad
\mathcal R_m(v_1,v_2,v_3)>0,
\tag{15}
\]
\[
\mathcal R_{k_0}(b_1^0,b_2^0,b_3^0)>0,\quad
\mathcal R_k(b_1,b_2,b_3)>0.
\tag{16}
\]

With \(\Phi(a,c)=(\sqrt a+\sqrt c)^2/4\), the ordinary and
common-fan midpoint gates hold strictly:
\[
\Phi(M,m)<k_0,\qquad
\frac{3p_0+m}{4}+\frac{p_0}{\delta}<k_0.
\tag{17}
\]
All nine forced exact-cell capacities are strict:
\[
\rho_i>\Phi(p_0,q_i),\qquad
\rho_i>\Phi(p_i,q_i)\qquad(i=1,2,3),
\tag{18}
\]
\[
\rho_{12}>\Phi(p_{12},q_{12}),\qquad
\rho_{13}>\Phi(p_{13},q_{13}),\qquad
\rho_{23}>\Phi(p_{23},q_{23}).
\tag{19}
\]
The completion quantities
\[
h_0=\frac{2(M+m+k_0)}9=\frac49,\qquad
F_i=d_i+b_i^0-h_0
\tag{20}
\]
satisfy
\[
F_1=F_2=F_3=-\frac1{15000},\qquad
\sum_{G\ni i}x_G=\frac1{5625}.
\tag{21}
\]
Consequently both completion filters of accepted fact
`38b9d85f6c0c57a2` remain strict.  The opposite conditions also
remain strict:
\[
\rho_1+\rho_2+\rho_{12}>\Phi(p_0,q_{12}),
\qquad
\rho_{13}+\rho_{23}+\rho_{123}>s_3,
\tag{22}
\]
\[
k_0>\Phi(p_0,q_3)+\Phi(p_0,q_{12})+s_3,
\tag{23}
\]
\[
2p_0>
q_3+4q_{12}+
\Phi(p_0,q_3)+\Phi(p_0,q_{12})+4s_3.
\tag{24}
\]

The \(P\)-table (4) is not merely formal.  In
\((\pi_1,\pi_2)\)-coordinates, with
\(\pi_3=10-\pi_1-\pi_2\), the triangle
\[
C_0=\{\pi_1,\pi_2,\pi_3\ge-3/400\}
\tag{25}
\]
has inverse area Jacobian \(\gamma\) and realizes every entry of
(4).  The statement makes no geometric-realizability claim for
(5) or for (7)--(9).  Thus the first remaining planar test is exact
realizability of (5) by one convex \(A_2\) in the same shifted fan;
if that passes, the next test is the actual Minkowski-average
\(\rho\)-table.

## Proof

We first prove (2).  Fix distinct \(i,j,k\), and use
\[
x=\pi_i,\qquad y=\pi_j,\qquad
\pi_k=\delta-x-y
\tag{26}
\]
as affine coordinates.  The coordinate change between any two such
pairs has determinant of absolute value one, so the inverse area
Jacobian is the same \(\gamma\) for every pair.  By (1) and accepted
fact `cc8c0bf6093b9357`,
\[
T_\delta=\operatorname{conv}\{(0,0),(\delta,0),(0,\delta)\}
\subseteq(\pi_i,\pi_j)(A_0)
\tag{27}
\]
and
\[
p_0=\frac{\gamma\delta^2}{2}.
\tag{28}
\]

Take any point \(z=(-a,-b)\), \(a,b\ge0\), of the closed
\(P_{ij}\)-chamber.  Convexity and (27) give
\[
\operatorname{conv}\{z,(\delta,0),(0,\delta)\}
\subseteq(\pi_i,\pi_j)(A_0).
\tag{29}
\]
Its part in the \(P_i\)-chamber contains a triangle of coordinate
area
\[
\frac{a\delta^2}{2(\delta+b)},
\tag{30}
\]
and its part in the \(P_j\)-chamber contains a triangle of coordinate
area
\[
\frac{b\delta^2}{2(\delta+a)}.
\tag{31}
\]
Indeed, the first triangle has vertices
\[
(0,0),\quad(0,\delta),\quad
\left(-\frac{a\delta}{\delta+b},0\right),
\]
and the second is obtained by interchanging the coordinates.
Multiplying (30)--(31) by \(\gamma\) and using (28) gives
\[
a\le\alpha_i(\delta+b),\qquad
b\le\alpha_j(\delta+a).
\tag{32}
\]
When \(\alpha_i\alpha_j<1\), substitution yields
\[
a\le
\frac{\alpha_i\delta(1+\alpha_j)}
     {1-\alpha_i\alpha_j},
\qquad
b\le
\frac{\alpha_j\delta(1+\alpha_i)}
     {1-\alpha_i\alpha_j}.
\tag{33}
\]
Every point of \(P_{ij}\) lies in the resulting rectangle.
Its physical area is at most
\[
\gamma\delta^2
\frac{\alpha_i\alpha_j(1+\alpha_i)(1+\alpha_j)}
     {(1-\alpha_i\alpha_j)^2},
\]
which is (2) by (28).  This argument is invariant under the three
choices of \(ij\), proving all cyclic instances.

We next verify the repaired exact datum.  Set
\[
\tau=\frac3{4000},\qquad a=\tau\delta=\frac3{400}.
\tag{34}
\]
The central triangle in (25) has coordinate area \(\delta^2/2\).
Each singleton cell has coordinate area
\[
a\delta+\frac{a^2}{2}=\frac{24009}{320000},
\tag{35}
\]
and each doubleton cell is a square of coordinate area
\[
a^2=\frac9{160000}.
\tag{36}
\]
Multiplication by \(\gamma=320000/D\) gives exactly (4).
Equivalently,
\[
p_0=\frac1{(1+3\tau)^2},\qquad
p_i=p_0(2\tau+\tau^2),\qquad
p_{ij}=2p_0\tau^2.
\tag{37}
\]
Thus the entries sum to one.  If
\(\alpha=2\tau+\tau^2\), then
\[
\alpha-\tau(1-\alpha)=\tau+3\tau^2+\tau^3>0.
\tag{38}
\]
Hence
\[
p_{ij}=2p_0\tau^2
<
2p_0\left(\frac{\alpha}{1-\alpha}\right)^2,
\tag{39}
\]
so all three profile inequalities are strict.

For comparison with accepted fact `38b9d85f6c0c57a2`, put bars on
its quantities.  Directly from (3)--(4),
\[
u_i=\frac{24045}{D}
=\frac3{2000}-\varepsilon
=\bar u_i-\varepsilon.
\tag{40}
\]
The transformation (7)--(9) preserves both middle row totals and
changes every middle cap sum by the same amount:
\[
b_i^0=\bar b_i^0+\varepsilon,\qquad
b_i=\bar b_i+\varepsilon.
\tag{41}
\]
It also leaves every completion cell unchanged:
\[
x_G=\bar r_G-\bar\rho_G.
\tag{42}
\]
Since the \(Q\)-table is unchanged,
\[
d_i=\bar d_i-\varepsilon.
\tag{43}
\]
Equations (41)--(43) prove (10)--(12), (20)--(21), and \(W=0\).
They also make both strict tails stronger.  Positivity follows from
\[
0<\varepsilon<\frac1{1000}.
\tag{44}
\]
The totals are unchanged, so (13) and the ordinary inequality in
(17) are unchanged.

Uniformly increasing the three arguments of the residual (14) by
\(\varepsilon\) increases that residual by \(9\varepsilon\).
For \(A_0\), the three cap areas \(M-u_i\) increase uniformly by
\(\varepsilon\); for the two middle tables, (41) gives the same
increase.  The \(A_2\) caps are unchanged.  Therefore every positive
residual certified in accepted fact `38b9d85f6c0c57a2` remains
positive, proving (15)--(16).

The new \(p_0\) is smaller than \(997/1000\).  Thus the common-fan
left side in (17) is smaller than the already certified value
\(16999/20000<99/100\).  This proves (17).

We check (18)--(19).  Write
\[
\Delta=\frac{997}{1000}-p_0.
\]
Exact subtraction gives
\[
\Delta-2\varepsilon
=\frac{11869257}{8036040500}>0.
\tag{45}
\]
For fixed \(c\ge0\), monotonicity of the square-root term gives
\[
\Phi(a,c)-\Phi(a',c)\ge\frac{a-a'}4
\qquad(a\ge a'\ge0).
\tag{46}
\]
Accepted fact `38b9d85f6c0c57a2` certifies
\[
\bar\rho_i-\Phi(997/1000,q_i)>\frac1{90000}.
\]
Equations (7), (45), and (46) therefore give
\(\rho_i>\Phi(p_0,q_i)\).

Also \(p_i<3/2000\), \(q_i\le11/2000\), and
\[
\Phi(a,c)\le\frac{a+c}{2}.
\tag{47}
\]
Thus \(\Phi(p_i,q_i)<7/2000\), whereas every \(\rho_i>1/4\).
This proves the second set of inequalities in (18).  Finally,
\(p_{ij}<1/2000\), the three \(\rho_{ij}\) are unchanged, and
\(\Phi\) is increasing in each argument.  The strict doubleton
capacities from accepted fact `38b9d85f6c0c57a2` therefore imply
(19).

The completion discrepancies \(F_i\) are unchanged by
(41)--(43), as are the completion cells (42).  The independent
completion-filter right side
\[
M+m-k_0-\frac52\sum_i d_i+3\max_i d_i
\]
increases by \(9\varepsilon/2\).  Hence both old strict completion
certificates remain valid.

For (22), the first left side decreases by exactly
\(\varepsilon\), while
\[
\bar\rho_1+\bar\rho_2+\bar\rho_{12}-\frac{27}{100}
=\frac{25211}{90000}
>\varepsilon.
\tag{48}
\]
Moreover \(\Phi(p_0,q_{12})<
\Phi(997/1000,q_{12})<27/100\).  The second left side in (22)
increases by \(3\varepsilon/2\), so both inequalities follow from
the old strict ones.  Monotonicity of \(\Phi\) immediately preserves
(23).

Finally,
\[
\Delta=\frac{23864757}{16072081000}<\frac1{500}.
\tag{49}
\]
Accepted fact `38b9d85f6c0c57a2` bounds the old right side of (24)
by a rational number lying \(130897/90000\) below
\(2(997/1000)\).  Replacing the left side by \(2p_0\) loses only
\(2\Delta<1/250\), while replacing the two \(\Phi\)-terms decreases
the right side.  Since \(130897/90000>1/250\), (24) remains strict.

All identities and comparisons in (3), (37), (40), (44)--(45), and
(49), together with
\[
2p_0\left(\frac{p_i/p_0}{1-p_i/p_0}\right)^2-p_{ij}
=
\frac{13851645400222542}
 {4102114013495768830561}>0,
\]
were independently checked over \(\mathbb Q\) with SageMath \(10.8\).
No floating-point feasibility decision is used.

## External sources

none
