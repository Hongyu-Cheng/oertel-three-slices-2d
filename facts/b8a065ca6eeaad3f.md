---
fact_id: b8a065ca6eeaad3f
kind: lemma
author: "mp_r344_triangle_quarter_away"
assurance: LLM-verified
subgoal_id: counterexample-triangle-n3-matrix-search
depends_on: ["09393c6edf1fc4e2","64760c76cadff481","91028112118edaa8"]
source_packet_sha256: 2539ac1ddc00d63f9009111bcad5c5b038e999cadeca4f5adba8610fd1477449
verifier_run: 5e0e387260b74361
target_match: null
---

## Statement

Let
\[
\Delta=\operatorname{conv}\{e_1,e_2,e_3\},\qquad |\Delta|=1,
\]
and define
\[
\mathcal C(z;\alpha)
=\left|\{\lambda\in\Delta:z\cdot\lambda\ge\alpha\}\right|.
\]
Assume the exact \(N=3\) barycentric system of accepted fact
`64760c76cadff481` in the surviving orientation of accepted fact
`09393c6edf1fc4e2`, with
\[
A=|\det U|=\frac14,\qquad B=|\det V|=1,\qquad
t=\frac{2(1+A+B)}9=\frac12.
\]
For any scale \(\delta>0\), put
\[
R=\delta L,\qquad \tau=\delta\sigma.
\]
Then
\[
\mathbf1^\top R=\delta\mathbf1^\top,\qquad
\sum_{i=1}^3\tau_i>\delta,
\]
and the exact row masses are
\[
M_i=
\mathcal C(R_{i*};0)
+\frac14\mathcal C((RU)_{i*};-\tau_i)
+\mathcal C((RV)_{i*};\tau_i).
\tag{1}
\]

Suppose that for some \(p,a,b>0\) with \(p>a+b\), and some permutation
matrices \(\Pi,\Gamma\),
\[
\Pi R\Gamma=
R(p,a,b):=
\begin{pmatrix}
p&-a&-b\\
-b&p&-a\\
-a&-b&p
\end{pmatrix}.
\tag{2}
\]
Then
\[
\boxed{\quad
\max_{1\le i\le3}(M_i-t)>\frac1{36}.
\quad}
\tag{3}
\]
In particular, no real or rational strict feasible point of the full iff
system occurs in the chamber (2).

Moreover, the member (2) lies outside the projective
\(\ell_\infty\)-tube of radius \(1/50\) around
\[
P=3I-\mathbf1\mathbf1^\top
\]
from accepted fact `91028112118edaa8` if and only if
\[
\boxed{\quad
\max\left\{\frac{99}{p},\frac{49}{a},\frac{49}{b}\right\}
>
\min\left\{\frac{101}{p},\frac{51}{a},\frac{51}{b}\right\}.
\quad}
\tag{4}
\]
Thus (3) excludes the whole sharply specified outside-tube family given
by (2) and (4).

## Proof

Row permutations only reorder the middle caps, and column permutations
only permute the three vertex values in each middle cap.  Hence the sum
of the middle caps is unchanged by the two permutations in (2).

Put
\[
d=p-a-b>0.
\]
Every row of \(R(p,a,b)\) is a permutation of \((p,-a,-b)\).  This is
the exact one-positive-vertex branch of the cap formula in accepted fact
`64760c76cadff481`, so every middle cap equals
\[
c(p,a,b)
=\mathcal C(p,-a,-b;0)
=\frac{p^2}{(p+a)(p+b)}.
\tag{5}
\]
The comparison with \(4/9\) has the exact numerator identity
\[
\begin{aligned}
9p^2-4(p+a)(p+b)
&=(a-b)^2+6d(a+b)+5d^2\\
&>0.
\end{aligned}
\tag{6}
\]
Consequently
\[
c(p,a,b)>\frac49,
\qquad
\sum_{i=1}^3\mathcal C(R_{i*};0)>\frac43.
\tag{7}
\]
This is a genuine nonsingular cap chamber.  Indeed,
\[
\det R(p,a,b)
=d\left(3a^2+3ab+3b^2+3ad+3bd+d^2\right)>0.
\tag{8}
\]

The three small-end caps in (1) cover \(\Delta\).  If some
\(\lambda\in\Delta\) were outside all of them, then
\[
(RU)_{i*}\lambda<-\tau_i
\qquad(i=1,2,3).
\]
Since
\[
\mathbf1^\top RU
=\delta\mathbf1^\top U
=\delta\mathbf1^\top,
\]
summing would give
\[
\delta
<-\sum_i\tau_i
<-\delta,
\]
which is impossible.  Therefore
\[
\sum_{i=1}^3
\mathcal C((RU)_{i*};-\tau_i)\ge1.
\tag{9}
\]
The three large-end terms in (1) are nonnegative.  Equations (7) and
(9) imply
\[
\sum_{i=1}^3M_i
>
\frac43+\frac14
=\frac{19}{12}.
\]
Taking the maximum and subtracting \(t=1/2\) gives
\[
\max_i(M_i-t)
>
\frac{19}{36}-\frac12
=\frac1{36},
\]
which proves (3).  Notice that no shape, compatibility-slack, allocation,
or determinant-sign information about \(U,V\) was discarded.

It remains to identify exactly which members of (2) are new relative to
the accepted balanced tube.  Let \(x=c^{-1}>0\) be the projective
scaling used in that tube.  Its tolerance is \(1/50<1\).  Therefore a
positive entry of \(xR(p,a,b)\) cannot be paired with a negative entry
of \(P\), and a negative entry cannot be paired with a positive entry
of \(P\).  The three positive entries must be aligned with the three
diagonal \(2\)'s.  Once this is done, all six remaining entries are
paired with \(-1\).  Hence tube membership is equivalent to
\[
\frac{99}{50}\le xp\le\frac{101}{50},\qquad
\frac{49}{50}\le xa\le\frac{51}{50},\qquad
\frac{49}{50}\le xb\le\frac{51}{50}.
\tag{10}
\]
Equivalently, the three closed intervals
\[
\left[\frac{99}{50p},\frac{101}{50p}\right],\qquad
\left[\frac{49}{50a},\frac{51}{50a}\right],\qquad
\left[\frac{49}{50b},\frac{51}{50b}\right]
\tag{11}
\]
have a common point.  Their intersection is empty exactly when their
largest lower endpoint exceeds their smallest upper endpoint.  Cancelling
the common factor \(1/50\) gives (4).  This proves the exact
inside-versus-outside assertion, including all row and column permutation
orbits.

The outside-tube family is nonempty and is not excluded merely because a
middle cap is already at least \(1/2\).  Take
\[
(p,a,b)=(21,12,8).
\]
Then \(d=1\),
\[
\det R=973,\qquad
c(p,a,b)=\frac{147}{319}<\frac12.
\]
The largest lower endpoint in (4) is \(49/8\), while the smallest upper
endpoint is \(51/12=17/4\), so this rational matrix lies strictly outside
the accepted tube.  The aggregate estimate gives the exact row-gap lower
bound
\[
\frac{147}{319}+\frac1{12}-\frac12
=\frac{169}{3828}
>\frac1{36}.
\]

For an independent exact audit, SageMath 10.8 factored (8), reduced the
numerator in (6) to
\[
(a-b)^2+6d(a+b)+5d^2,
\]
and returned for the displayed rational member
\[
d=1,\quad \det R=973,\quad c=147/319,\quad
\text{gap}=169/3828,\quad
\max\text{ lower}=49/8>\min\text{ upper}=17/4.
\]
Wolfram Language 14.3 independently returned `True` for both polynomial
identities and for the exact quantified positivity of (6) and (8) over
\(a,b,d>0\); it also returned `False` for existence of a positive scaling
placing the rational member in the radius-\(1/50\) tube.  The proof above
does not depend on numerical approximation.

## External sources

none
