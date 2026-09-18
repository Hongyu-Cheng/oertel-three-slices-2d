---
fact_id: eee2bdfe64ccf5b1
kind: lemma
author: "mp_r13_equality_normalization"
assurance: LLM-verified
subgoal_id: minkowski-equality-family
depends_on: ["8ad0785e5b4ae9ef","d7bdfc054d5093e8","ecee03aff61db31e"]
source_packet_sha256: 346ae699a24a09b586a780db48728338f2f17b76d41af5b17cae5f7acf3772a9
verifier_run: 24b5b7a4231b4e89
target_match: null
---

## Statement

Let \(A_0,A_1,A_2\subset\mathbb R^2\) be compact convex bodies with nonempty interiors and
\[
M:=\frac{A_0+A_2}{2}\subseteq A_1.
\]
Write
\[
a_i=|A_i|,\qquad r_i=\sqrt{a_i},
\]
and let \(c_i\) be the centroid of \(A_i\). In the locked polytopal slice setting, accepted fact `8ad0785e5b4ae9ef` supplies the displayed compatibility inclusion, while accepted fact `d7bdfc054d5093e8` identifies
\[
r_0+r_2\le 2r_1
\]
as the exact scalar area condition.

The following are equivalent:

1. \(r_0+r_2=2r_1\).

2. Both
\[
A_1=\frac{A_0+A_2}{2}
\]
and equality holds in the planar Brunn-Minkowski inequality:
\[
\left|\frac{A_0+A_2}{2}\right|^{1/2}
=\frac{r_0+r_2}{2}.
\]

3. There is a compact two-dimensional convex body \(K\subset\mathbb R^2\), of area \(1\) and centroid \(0\), such that
\[
A_0=c_0+r_0K,\qquad
A_1=c_1+r_1K,\qquad
A_2=c_2+r_2K,
\]
with
\[
c_1=\frac{c_0+c_2}{2},
\qquad
2r_1=r_0+r_2.
\]
If the \(A_i\) are polytopes, \(K\) is a polytope.

In this case set
\[
d:=\frac{c_0-c_2}{2}=c_0-c_1=c_1-c_2.
\]
The height shear from accepted fact `ecee03aff61db31e`,
\[
F_d(x,z)=(x,z+(x-1)d),
\]
maps the three slices to
\[
c_1+r_0K,\qquad c_1+r_1K,\qquad c_1+r_2K.
\]
After the common planar translation by \(-c_1\), the canonical placement is therefore
\[
r_0K,\qquad r_1K,\qquad r_2K.
\]
This affine normalization preserves all three areas, total mass, and every halfspace depth.

The condition \(A_1=(A_0+A_2)/2\) alone is strictly weaker. For example,
\[
A_0=[0,1]\times[0,1],\qquad
A_2=[0,2]\times[0,1],\qquad
A_1=[0,3/2]\times[0,1]
\]
satisfy \(A_1=(A_0+A_2)/2\), but their Brunn-Minkowski inequality is strict.

## Proof

Assume first that \(r_0+r_2=2r_1\). By planar Brunn-Minkowski and compatibility,
\[
r_1
=\frac{r_0+r_2}{2}
\le |M|^{1/2}
\le |A_1|^{1/2}
=r_1.
\]
Thus every inequality is an equality. In particular,
\[
|M|=|A_1|
\]
and equality holds in Brunn-Minkowski for \(A_0,A_2\).

We also have \(M=A_1\) as sets. Indeed, if \(M\subsetneq A_1\), choose \(x\in A_1\setminus M\). Since \(M\) is compact and convex, a linear functional strictly separates \(x\) from \(M\). Joining \(x\) to any interior point of \(A_1\), one obtains an interior point of \(A_1\) still strictly separated from \(M\). A sufficiently small open disk around that point lies in \(A_1\setminus M\), contradicting \(|M|=|A_1|\). This proves condition 2.

Apply the equality theorem quoted below to \(A_0,A_2\). There are \(v\in\mathbb R^2\) and \(\lambda>0\) such that
\[
A_2=v+\lambda A_0.
\]
Area comparison gives
\[
a_2=\lambda^2a_0,
\qquad
\lambda=\frac{r_2}{r_0}.
\]
Define
\[
K:=\frac{A_0-c_0}{r_0}.
\]
Then \(K\) has area \(1\), centroid \(0\), and
\[
A_0=c_0+r_0K.
\]
Affine covariance of the centroid gives
\[
c_2=v+\lambda c_0,
\]
so
\[
A_2=c_2+r_2K.
\]
Since \(K\) is convex, \(r_0K+r_2K=(r_0+r_2)K\). Hence
\[
A_1=M
=\frac{c_0+c_2}{2}+\frac{r_0+r_2}{2}K
=\frac{c_0+c_2}{2}+r_1K.
\]
Because \(K\) has centroid \(0\), this representation shows
\[
c_1=\frac{c_0+c_2}{2}.
\]
Thus condition 3 holds.

Conversely, assume condition 3. Convexity of \(K\) gives
\[
\frac{A_0+A_2}{2}
=\frac{c_0+c_2}{2}+\frac{r_0+r_2}{2}K
=c_1+r_1K
=A_1.
\]
Because \(|K|=1\),
\[
\left|\frac{A_0+A_2}{2}\right|^{1/2}
=|A_1|^{1/2}
=r_1
=\frac{r_0+r_2}{2},
\]
so condition 2 holds. Condition 2 immediately implies condition 1 because \(A_1=M\) and \(r_1=|A_1|^{1/2}\). This proves all equivalences.

For the affine placement, the centroid relation gives
\[
d=c_0-c_1=c_1-c_2.
\]
Accepted fact `ecee03aff61db31e` says that \(F_d\) replaces the slice bodies by
\[
A_0-d,\qquad A_1,\qquad A_2+d.
\]
Using the representations above,
\[
A_0-d=c_1+r_0K,\qquad
A_1=c_1+r_1K,\qquad
A_2+d=c_1+r_2K.
\]
The common planar translation \((x,z)\mapsto(x,z-c_1)\) then gives the canonical triple \((r_0K,r_1K,r_2K)\). This translation is an ambient Euclidean isometry preserving the three slice planes, their two-dimensional Hausdorff measures, and closed halfspaces. It therefore preserves halfspace depth. Together with `ecee03aff61db31e`, this proves the full depth-preserving normalization.

Finally, for the stated rectangular example,
\[
\frac{A_0+A_2}{2}=[0,3/2]\times[0,1]=A_1,
\]
and
\[
(a_0,a_1,a_2)=\left(1,\frac32,2\right).
\]
However,
\[
1+\sqrt2<\sqrt6=2\sqrt{\frac32},
\]
because \(3+2\sqrt2<6\). Thus Brunn-Minkowski is strict. Accepted fact `8ad0785e5b4ae9ef` also confirms that this exact-Minkowski triple is compatible with a locked-type polytope. Hence the full family \(A_1=(A_0+A_2)/2\) properly contains the normalized equality family.

## External sources

Daniel A. Klain, “On the Equality Conditions of the Brunn-Minkowski Theorem,” Proceedings of the American Mathematical Society 139 (2011), 3719–3726, Theorem 1.1. The theorem states that compact convex sets with nonempty interiors attain equality in Brunn-Minkowski for a parameter in \((0,1)\) if and only if they are homothetic. Primary-source [full text](https://arxiv.org/abs/1005.1409); [publication DOI](https://doi.org/10.1090/S0002-9939-2011-10822-0).

Applicability check: \(A_0,A_2\) are compact convex subsets of \(\mathbb R^2\) with nonempty interiors, and the proof establishes equality at parameter \(1/2\). Thus the theorem yields an exact positive homothety \(A_2=v+\lambda A_0\), not merely equality up to null sets.
