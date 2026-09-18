---
fact_id: ab193fb25d3fcfa9
kind: lemma
author: "mp_r160_regime_a_thin_strip"
assurance: LLM-verified
subgoal_id: regime-a-homothetic-thin-strip-family
depends_on: []
source_packet_sha256: fbc286077edd47c4c47d60b9b60a13054d0d0a32453ac2f5d86ea3d1af88141e
verifier_run: ebf71ed73e2f4a6a
target_match: null
---

## Statement

Let \(0<h<1/\sqrt3\), let \(\lambda=(1+h)/2\), and assume that \(s\) lies in the Regime A strip with \(r=h^2\), meaning that either
\[
0<h^2\leq\frac15,\qquad 1-h^2<s<1+h^2,
\]
or
\[
\frac15<h^2<\frac13,\qquad 1-h^2<s<2-4h^2.
\]
For \(w>0\), put
\[
A_0=\{(x,y):0\leq x+y\leq1/w,\ |x-y|\leq w\},
\qquad
A_2=hA_0.
\]
Let \(K\) be any compact two-dimensional convex body of area \(s\) containing
\[
\frac{A_0+A_2}{2}=\lambda A_0.
\]
Define
\[
c_i=|K\cap\{x\leq0\}|,\qquad
c_\ell=|K\cap\{y\leq0\}|,\qquad
c_j=|K\cap\{x+y\geq-1\}|,
\]
and
\[
u_i=|A_0\cap\{x\leq0\}|,\qquad
u_\ell=|A_0\cap\{y\leq0\}|.
\]
If
\[
w\left(\frac{4s}{\lambda}-\lambda\right)\leq1,
\]
then
\[
\max\{c_i+(1+h^2)u_i,\ c_\ell+(1+h^2)u_\ell,\ c_j+h^2\}
\geq\frac{2(1+h^2+s)}9.
\]
The conclusion includes equality in the thinness condition and all cases in which a cutting line is supporting or contains a nontrivial face.

## Proof

Use the invertible linear coordinates
\[
\sigma=x+y,\qquad \eta=x-y.
\]
The absolute determinant of the map \((x,y)\mapsto(\sigma,\eta)\) is \(2\). Hence the image \(P\) of \(K\) has \((\sigma,\eta)\)-area \(2s\). The image of \(\lambda A_0\) is the rectangle
\[
R=[0,\lambda/w]\times[-\lambda w,\lambda w]\subseteq P.
\]

Fix any \(p=(\sigma,\eta)\in P\). By convexity, \(P\) contains the convex hull of \(p\) with each of the two full horizontal edges
\[
E_-=[0,\lambda/w]\times\{-\lambda w\},
\qquad
E_+=[0,\lambda/w]\times\{\lambda w\}.
\]
These convex hulls are possibly degenerate triangles. Their \((\sigma,\eta)\)-areas are respectively
\[
\frac{\lambda}{2w}|\eta+\lambda w|,
\qquad
\frac{\lambda}{2w}|\eta-\lambda w|.
\]
Each is contained in \(P\), whose area is \(2s\). Therefore
\[
|\eta+\lambda w|\leq\frac{4sw}{\lambda},
\qquad
|\eta-\lambda w|\leq\frac{4sw}{\lambda}.
\]
The first inequality gives \(\eta\leq 4sw/\lambda-\lambda w\), while the second gives \(\eta\geq\lambda w-4sw/\lambda\). Consequently every point of \(P\) satisfies
\[
|\eta|\leq w\left(\frac{4s}{\lambda}-\lambda\right).
\]
The right side is nonnegative; for example, containment gives \(s\geq|\lambda A_0|=\lambda^2\). The thinness hypothesis now yields
\[
|\eta|\leq1\qquad\text{on }P.
\]

If a point of \(P\) has \(\sigma<-1\), then
\[
\sigma+\eta<0,\qquad \sigma-\eta<0,
\]
because \(\eta\leq1\) and \(\eta\geq-1\). Since \(x=(\sigma+\eta)/2\) and \(y=(\sigma-\eta)/2\), this proves the pointwise inclusion
\[
K\cap\{x+y<-1\}\subseteq K\cap\{x<0,\ y<0\}.
\]
The set on the left is exactly the complement in \(K\) of the closed \(j\)-cap. Thus it has area \(s-c_j\), and the inclusion into each closed side cap gives
\[
c_i\geq s-c_j,\qquad c_\ell\geq s-c_j.
\]

Put
\[
t=\frac{2(1+h^2+s)}9.
\]
If \(c_j+h^2\geq t\), the third term proves the result. Otherwise \(c_j<t-h^2\), so both side estimates give
\[
c_i,\ c_\ell>s-t+h^2.
\]
Both branches of the Regime A strip have \(s>1-h^2\). Hence
\[
(s-t+h^2)-t
=\frac{5(s+h^2)-4}{9}>0.
\]
It follows that \(c_i>t\) and \(c_\ell>t\). Since \(u_i,u_\ell\geq0\), both side expressions in the asserted maximum are then strictly greater than \(t\).

No transversality was used. The triangle-area argument remains valid for degenerate triangles and for support faces. If the thinness bound is an equality, the strict inequality \(\sigma<-1\) still forces both \(x<0\) and \(y<0\). Finally, every defining cap is closed, so a cutting line or support face belongs to the stated cap rather than being discarded. This covers all equality, support-face, and zero-cell boundary cases.

## External sources

none
