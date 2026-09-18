---
fact_id: 0f2b9e704aeaceb3
kind: lemma
author: "mp_r378_mixedarea_literature"
assurance: LLM-verified
subgoal_id: canonical-single-double-three-crossing-overlap
depends_on: []
source_packet_sha256: 4c5a8e2b64832d7df3f8e94715f4c5f406d0ac00d76a2846ec04174510f2adc2
verifier_run: 0db8996b508d4724
target_match: null
---

## Statement

Let \(\Delta>2\), and put
\[
 L_1=L_2=L_3=-\frac{\Delta+1}{3},
 \qquad
 s=\frac{\Delta+2}{\Delta}>1.
\tag{1}
\]
On the affine plane \(r_1+r_2+r_3=1\), set
\[
 f_i=\Delta r_i+L_i.
\tag{2}
\]
Define the second normalized coordinates by
\[
 \tau_i=-\frac{f_i+L_i}{\Delta+2}.
\tag{3}
\]
Then
\[
 \tau_1+\tau_2+\tau_3=1,\qquad
 r_i=\frac{2(\Delta+1)}{3\Delta}-s\tau_i.
\tag{4}
\]
Areas are measured in the \(r\)-coordinate normalization, so a
polygon described in \(\tau\)-coordinates has \(s^2\) times its
\(\tau\)-coordinate area.

Choose
\[
 \alpha_1,\alpha_2,\alpha_3,\theta,\rho,\chi,\omega,x,y,z>0,
 \qquad
 0<\theta<1,\qquad x+y+z=1,
\tag{5}
\]
and assume
\[
 \rho z\le\omega y,\qquad
 \chi z\le\omega x.
\tag{6}
\]
Let
\[
 A_0=\left\{
 r_1+r_2+r_3=1:
 r_i\ge-\alpha_i\ (i=1,2,3),\
 r_3\le\theta
 \right\},
\tag{7}
\]
and let \(A_2\) be the triangle with \(\tau\)-coordinate vertices
\[
\begin{aligned}
 y_1&=(1+\rho+\omega,-\rho,-\omega),\\
 y_2&=(-\chi,1+\chi+\omega,-\omega),\\
 y_3&=(x,y,z).
\end{aligned}
\tag{8}
\]
Write
\[
 R=1+\rho+\chi+\omega,\qquad H=\omega+z,
\tag{9}
\]
\[
 P=A_0\cap\{r_1,r_2,r_3\ge0\},\qquad
 p=|P|,\qquad m=|A_2|.
\tag{10}
\]

For \(J\subseteq\{1,2,3\}\), the small-endpoint sign cell is
\[
 Q_J=A_2\cap
 \{\tau_i\ge0\ (i\in J),\ \tau_i<0\ (i\notin J)\},
\tag{11}
\]
up to null boundary segments.  The row-1 corner \(Q_2\) and the total
area have the exact values
\[
 |Q_2|=\frac{s^2\chi^2H}{2(\chi+x)},
\qquad
 m=\frac{s^2RH}{2}.
\tag{12}
\]
The large empty cell and its area are
\[
 P=\operatorname{conv}\{
 (1-\theta,0),(1,0),(0,1),(0,1-\theta)\},
\qquad
 p=\theta-\frac{\theta^2}{2}.
\tag{13}
\]

Define
\[
 \Phi(t)=
 |A_0\cap\{f_1\le t\}|
 +|A_2\cap\{f_1\le-t\}|.
\tag{14}
\]
Assume that \(L_1\) is an actual lower crossing in the following
literal sense: there are real numbers \(c_1,h\) such that
\[
 c_1+\Phi(L_1)=h,\qquad
 L_1=\inf\{t\in\mathbb R:c_1+\Phi(t)<h\}.
\tag{15}
\]
Finally assume the scalar restriction
\[
 \frac pm>
 \beta:=\frac{93+12\sqrt{21}}{50}.
\tag{16}
\]
Then these hypotheses are inconsistent.  In fact, (15) already
forces \(p/m<2\), while \(\beta>2\).

## Proof

Equations (2)-(4) give
\[
 f_i+L_i=\Delta r_i+2L_i=-(\Delta+2)\tau_i.
\tag{17}
\]
The linear part of the \(r\)-to-\(\tau\) relation is a homothety of
ratio \(s\), which proves the stated \(s^2\) area factor.

We first compute only the small-endpoint data used in row \(1\).
In \((\tau_1,\tau_2)\)-coordinates, the base
\([y_1,y_2]\) has vector \((-R,R)\), and its affine height from
\(y_3\) is \(H\).  Hence
\[
 |A_2|_\tau=\frac{RH}{2},
\]
which proves the formula for \(m\) in (12).

The line \(\tau_1=0\) meets the base at
\[
 a_2=(0,1+\omega,-\omega).
\tag{18}
\]
It meets \([y_2,y_3]\) at
\[
 b_2=(0,1+\varepsilon,-\varepsilon),
\qquad
 \varepsilon=\frac{\omega x-\chi z}{\chi+x}\ge0,
\tag{19}
\]
where nonnegativity is exactly the second inequality in (6).
The coordinate length of \([a_2,b_2]\) is therefore
\[
 \ell=(1+\omega)-(1+\varepsilon)
 =\frac{\chi(\omega+z)}{\chi+x}
 =\frac{\chi H}{\chi+x}>0.
\tag{20}
\]
The portion with \(\tau_1<0\) is the triangle \(Q_2\), with transverse
coordinate height \(\chi\) and base length \(\ell\).  Thus
\[
 |Q_2|_\tau=\frac{\chi\ell}{2}
 =\frac{\chi^2H}{2(\chi+x)}.
\]
Multiplying by \(s^2\) proves the other formula in (12).

For \(A_0\), imposing \(r_i\ge0\) in (7) gives
\[
 0\le r_3\le\theta.
\]
The four vertices in (13) follow by intersecting the two boundary
lines with the coordinate simplex.  Shoelace gives
\[
 p=\theta-\frac{\theta^2}{2}.
\tag{21}
\]

It remains to extract the exact consequence of the actual crossing.
Write \(t=L_1+\eta\).  By (2), the first cap of \(A_0\) is cut at
\[
 r_1=\frac{\eta}{\Delta}.
\]
At \(r_1=0\), its section is
\[
 1-\theta\le r_2\le1+\alpha_3,
\]
so its coordinate length is \(\theta+\alpha_3\).  The section length
varies continuously near \(0\), and Fubini's formula therefore gives
\[
 \left.
 \frac{d}{d\eta}
 |A_0\cap\{f_1\le L_1+\eta\}|
 \right|_{\eta=0+}
 =\frac{\theta+\alpha_3}{\Delta}.
\tag{22}
\]

By (17), the second cap in (14) is
\[
 A_2\cap
 \left\{\tau_1\ge\frac{\eta}{\Delta+2}\right\}.
\]
At \(\eta=0\), its section is exactly \([a_2,b_2]\), of
\(\tau\)-coordinate length \(\ell\).  Accounting for the \(s^2\)
area factor gives
\[
 \left.
 \frac{d}{d\eta}
 |A_2\cap\{f_1\le-L_1-\eta\}|
 \right|_{\eta=0+}
 =-\frac{s^2\ell}{\Delta+2}
 =-\frac{s\ell}{\Delta}.
\tag{23}
\]
Consequently the right derivative exists and equals
\[
 \Phi'(L_1+)
 =\frac{\theta+\alpha_3-s\ell}{\Delta}.
\tag{24}
\]

We now use every quantifier in (15).  Since the infimum there equals
\(L_1\), for every \(\delta>0\) there is
\(t\in(L_1,L_1+\delta)\) with
\[
 \Phi(t)<\Phi(L_1).
\tag{25}
\]
If the right derivative in (24) were positive, the definition of a
right derivative would instead give
\(\Phi(t)>\Phi(L_1)\) throughout some interval
\((L_1,L_1+\delta)\), contradicting (25).  Hence
\[
 \theta+\alpha_3\le s\ell.
\tag{26}
\]

Finally, (9), (12), (13), (20), and (26) give
\[
\begin{aligned}
 \frac pm
 &<
 \frac{s\ell}{s^2RH/2}\\
 &=
 \frac{2\chi}{sR(\chi+x)}
 <2.
\end{aligned}
\tag{27}
\]
The first strict inequality uses
\[
 p=\theta-\frac{\theta^2}{2}
 <\theta<\theta+\alpha_3\le s\ell;
\]
the last uses \(s>1\), \(R>1\), and
\(\chi/(\chi+x)<1\).  On the other hand,
\[
 \beta-2=\frac{12\sqrt{21}-7}{50}>0,
\]
because \(144\cdot21>49\).  Thus (16) gives \(p/m>2\), contradicting
(27).  No other canonical hypothesis is used.

## External sources

none
