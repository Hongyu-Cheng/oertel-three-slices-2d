---
fact_id: 003adef77e7c9efe
kind: lemma
author: "mp_r371_triangle_single_single"
assurance: LLM-verified
subgoal_id: counterexample-triangle-n3-matrix-search
depends_on: []
source_packet_sha256: 66bb10c2db525b99e8c5d8e2cb1cacdbe0c7d1ae637e06f98a4b4d6883d39619
verifier_run: b2217b840d1046e2
target_match: null
---

## Statement

Let \(q>1\), let \(\{1,j,k\}=\{1,2,3\}\), and let \(P_0,P_2\) be
nondegenerate triangles in
\[
H_{1+q}:=\left\{x:\sum_{\ell=1}^3x_\ell=1+q\right\},
\qquad
H_{1-q}:=\left\{x:\sum_{\ell=1}^3x_\ell=1-q\right\},
\]
respectively.  Let \(g_0\) be the centroid of \(P_0\).  Assume
\[
(g_0)_1>1+q,\qquad
(g_0)_j<0,\qquad
(g_0)_k<0,
\tag{1}
\]
assume that the one-positive \(j\)-cell is active,
\[
P_0\cap\{x_j>0,\ x_1<0,\ x_k<0\}\ne\varnothing,
\tag{2}
\]
and assume that \(P_2\) is cap-free:
\[
P_2\subseteq\{x_1\leq0,\ x_2\leq0,\ x_3\leq0\}.
\tag{3}
\]
Put
\[
A=|P_0|,\qquad B=|P_2|,
\qquad \frac AB<\frac38.
\tag{4}
\]
For an affine functional \(f\), write
\[
\operatorname{width}_f(P)
:=\max_{x\in P}f(x)-\min_{x\in P}f(x).
\]
Then, for
\[
f(x)=x_1-x_j,
\]
one has the exact strict width mismatch
\[
\boxed{
\frac{\operatorname{width}_f(P_0)}
{\operatorname{width}_f(P_2)}
>
\frac{3(q+1)}{2(q-1)}
>
\frac32.}
\tag{5}
\]
Consequently \(P_0\) and \(P_2\) are not homothetic, even allowing a negative
homothety factor.  More quantitatively,
\[
\frac{
\operatorname{width}_f(P_0)/
\operatorname{width}_f(P_2)}
{\sqrt{A/B}}
>\sqrt6.
\tag{6}
\]
In particular, the two triangles cannot have the same three unoriented edge
directions.  Thus no exact parallel-edge or Brunn--Minkowski equality
endpoint pair exists under (1)--(4).

## Proof

Put
\[
s=1+q,\qquad t=q-1,
\]
so \(s>0\), \(t>0\), and the endpoint planes are \(H_s\) and \(H_{-t}\).
Let
\[
a\leq b\leq c
\]
be the three values of \(f=x_1-x_j\) at the vertices of \(P_0\).  Since
\(f\) is affine, these are its minimum, middle vertex value, and maximum on
\(P_0\).

By (2), there is \(x\in P_0\) with \(x_j>0\), \(x_1<0\), and \(x_k<0\).
Because \(x_1+x_j+x_k=s\), one has
\[
x_j=s-x_1-x_k>s.
\]
Therefore
\[
f(x)=x_1-x_j<-s,
\qquad\text{so}\qquad
a<-s.
\tag{7}
\]

The centroid value of an affine functional on a triangle is the average of
its three vertex values.  Hypothesis (1) gives
\[
f(g_0)=(g_0)_1-(g_0)_j>s,
\]
and hence
\[
a+b+c>3s.
\tag{8}
\]
Since \(b\leq c\), equations (7)--(8) imply
\[
a+2c\geq a+b+c>3s,
\qquad
c>\frac{3s-a}{2}.
\]
It follows that
\[
\operatorname{width}_f(P_0)
=c-a
>
\frac{3s-3a}{2}
>3s
=3(q+1).
\tag{9}
\]
This is where the singleton centroid condition strengthens the elementary
two-cell width \(2s\) to \(3s\).

Now take any \(z\in P_2\).  From (3) and
\(\sum_\ell z_\ell=-t\), each coordinate satisfies
\[
-t\leq z_\ell\leq0.
\]
Consequently
\[
-t\leq z_1-z_j\leq t,
\]
so
\[
\operatorname{width}_f(P_2)\leq2t=2(q-1).
\tag{10}
\]
The triangle is nondegenerate, so its width in the nonconstant direction
\(f\) is positive.  Dividing (9) by (10) proves (5).

Suppose next that \(P_0\) were a homothetic copy of \(P_2\):
\[
P_0=z+\lambda P_2
\qquad(\lambda\ne0).
\tag{11}
\]
Translations do not change widths, and a scalar homothety multiplies every
width by \(|\lambda|\).  It multiplies planar area by \(\lambda^2\).  Thus
(11) would give
\[
\frac{\operatorname{width}_f(P_0)}
{\operatorname{width}_f(P_2)}
=|\lambda|
=\sqrt{\frac AB}
<\sqrt{\frac38}
<1,
\tag{12}
\]
contradicting (5).  Combining (5) with (12)'s area scale gives
\[
\frac{
\operatorname{width}_f(P_0)/
\operatorname{width}_f(P_2)}
{\sqrt{A/B}}
>
\frac{3/2}{\sqrt{3/8}}
=\sqrt6,
\]
which proves (6).

Finally, two nondegenerate planar triangles with the same three unoriented
edge directions are homothetic up to a possible negative factor.  Indeed,
choose corresponding cyclic edge vectors \(v_1,v_2,v_3\) for one triangle,
so \(v_1+v_2+v_3=0\) and \(v_1,v_2\) are independent.  The corresponding
edge vectors of the other triangle have the form
\(\lambda_i v_i\), after reversing all cyclic orientations if necessary.
Closure gives
\[
(\lambda_1-\lambda_3)v_1
+(\lambda_2-\lambda_3)v_2=0,
\]
so independence forces
\(\lambda_1=\lambda_2=\lambda_3\).  The triangles therefore differ by a
translation and a scalar homothety, contrary to (12).  This proves the final
assertion and completes the chamber obstruction.

## External sources

none
