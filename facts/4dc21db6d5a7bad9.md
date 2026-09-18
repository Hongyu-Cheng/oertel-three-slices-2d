---
fact_id: 4dc21db6d5a7bad9
kind: counterexample
author: "r104_support_depth_audit"
assurance: LLM-verified
subgoal_id: support-contact-depth-criterion-parameter-audit
depends_on: ["15bb2c1680a0254e","4e176b68a1636efc","d54b7af318521d6b"]
source_packet_sha256: 86bff573ffbe5cc3ebe0c7f781098b37c3f56f9f7258ab8d422ae9058a191112
verifier_run: a077bf023cd040b9
target_match: null
---

## Statement

Accepted fact `15bb2c1680a0254e` supplies the full residual strip in the area ratios \(r=m/M\) and \(s=k/M\).  Accepted fact `4e176b68a1636efc` supplies the strict survivor gate after sorting \(\{a,d_2,d_3\}\).  The following exact rational choice satisfies those constraints and both displayed same-direction cap/complement inequalities:
\[
M=1,\qquad m=\frac12,\qquad k=1,\qquad a=\frac1{16},
\]
\[
u_2=u_3=\frac1{16},\qquad
v_2=v_3=\frac14,\qquad
d_i=u_i+v_i=\frac5{16}\quad(i=2,3).
\]
With
\[
t=\frac{2(M+m+k)}9,\qquad
p=\sqrt{\frac{M}{u_2}},\qquad
q=\sqrt{\frac{M}{u_3}},
\]
\[
C=\frac{pq-p-q}{p+q},\qquad
B_i=\frac1{\sqrt{1+u_i/v_i}-1},
\]
one nevertheless has
\[
C<\max\{B_2,B_3\}.
\]
Thus the numerical premise used by accepted fact `d54b7af318521d6b` is not forced by the audited scalar constraints.  No assertion is made that these cap numbers are simultaneously realized by convex bodies or that they form a geometric counterexample.

## Proof

First,
\[
M=1\ge\frac12=m>0,\qquad k=1>0,\qquad
0<t=\frac{2(1+1/2+1)}9=\frac59<1=M.
\]
For the residual strip of accepted fact `15bb2c1680a0254e`,
\[
r=\frac mM=\frac12,\qquad s=\frac kM=1,\qquad
\rho=\frac{27-2\sqrt{26}}{25}.
\]
The comparison \(r<\rho\) is exact:
\[
\frac12<\rho
\quad\Longleftrightarrow\quad
4\sqrt{26}<29,
\]
and both sides of the last inequality are positive, while
\[
(4\sqrt{26})^2=416<841=29^2.
\]
Also \(9/25<r\le1/2\), so the applicable residual endpoints are
\[
L(r)=\frac{3r+2\sqrt r-1}{2}
=\frac14+\frac{\sqrt2}{2},
\qquad
U(r)=1+r=\frac32.
\]
Since both sides are positive and
\[
(2\sqrt2)^2=8<9=3^2,
\]
one has \(2\sqrt2<3\), and hence
\[
L(r)=\frac14+\frac{\sqrt2}{2}<1=s<\frac32=U(r).
\]
At the branch point \(r=1/2\), the other upper formula is also
\(2-r=3/2\), so there is no endpoint ambiguity.  For completeness, all raw
strict residual inequalities hold:
\[
1-r=\frac12<1<\frac32=1+r,\qquad 1<2-r=\frac32,
\]
\[
1>\frac{3r+2\sqrt r-1}{2}=L(r),
\]
and the compatibility lower bound also holds, since \(2\sqrt2<3\) gives
\[
\frac{(1+\sqrt r)^2}{4}
=\frac38+\frac{\sqrt2}{4}
<\frac38+\frac38=\frac34<1=s.
\]

Next, for each \(i=2,3\),
\[
0<\frac1{16}=u_i<M,\qquad
0<\frac14=v_i<m,\qquad
d_i=\frac5{16}<\frac12=m,
\]
and \(0<a=1/16\le m\).  The sorting required by the survivor gate of
accepted fact `4e176b68a1636efc` is
\[
\lambda=\frac1{16},\qquad
\mu=\nu=\frac5{16}.
\]
Consequently,
\[
4\lambda+5\mu
=\frac4{16}+\frac{25}{16}
=\frac{29}{16}
<\frac{32}{16}
=4m.
\]

The two cap inequalities are identical for \(i=2,3\).  For the first one,
\[
t-d_i=\frac59-\frac5{16}=\frac{35}{144},
\]
whereas
\[
\frac{(\sqrt{u_i}+\sqrt{v_i})^2}{4}
=\frac{(1/4+1/2)^2}{4}
=\frac9{64}.
\]
Their exact difference is
\[
\frac{35}{144}-\frac9{64}=\frac{59}{576}>0.
\]
For the complement inequality,
\[
k-t+d_i=1-\frac59+\frac5{16}=\frac{109}{144},
\]
and
\[
\frac{(\sqrt{M-u_i}+\sqrt{m-v_i})^2}{4}
=\frac{(\sqrt{15/16}+\sqrt{1/4})^2}{4}
=\frac{19+4\sqrt{15}}{64}.
\]
Because \(15<16\), positivity permits taking square roots and gives
\(\sqrt{15}<4\).  Therefore
\[
\frac{19+4\sqrt{15}}{64}
<\frac{35}{64}
<\frac{109}{144},
\]
where the final rational comparison has exact difference
\[
\frac{109}{144}-\frac{35}{64}=\frac{121}{576}>0.
\]
Thus all four same-direction inequalities hold strictly.

Finally,
\[
p=q=\sqrt{\frac1{1/16}}=4,
\qquad
C=\frac{16-4-4}{4+4}=1.
\]
For both \(i=2,3\),
\[
\frac{u_i}{v_i}=\frac14,
\]
so
\[
B_i
=\frac1{\sqrt{5/4}-1}
=\frac2{\sqrt5-2}
=4+2\sqrt5.
\]
The denominator is positive because \(2<\sqrt5\), which follows exactly by
squaring the positive quantities and using \(4<5\).  Hence
\[
C=1<4+2\sqrt5=B_2=B_3
=\max\{B_2,B_3\}.
\]
This strict reverse shows that the criterion in accepted fact
`d54b7af318521d6b` cannot be deduced from the audited scalar constraints
alone.  Since no common convex bodies or common cutting planes have been
constructed, the example is only a scalar survivor and not a geometric
counterexample.

## External sources

none
