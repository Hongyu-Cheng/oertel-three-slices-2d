---
fact_id: c0a4f6ae5d1dab55
kind: lemma
author: "mp_r9_extreme_witness"
assurance: LLM-verified
subgoal_id: extreme-nested-triangle-depth
depends_on: ["1e5a9785593e5f6a","400272f6de6c67bb"]
source_packet_sha256: e590928f002146f49bbb2e2487020b16c750df1f7750d007c9f0039fa9a00f5a
verifier_run: 2c7a543126a1439a
target_match: null
---

## Statement

Let \(V_0,V_1,V_2\in\mathbb R^2\) be affinely independent, and let
\[
\Delta=\operatorname{conv}\{V_0,V_1,V_2\},\qquad D:=|\Delta|>0.
\]
Interpret every homothety below as centered at \(V_0\). Set
\[
u=\frac{201}{200},\qquad v=\frac{101}{1000},
\]
\[
A_0=V_0+u(\Delta-V_0),\qquad A_1=\Delta,\qquad
A_2=V_0+v(\Delta-V_0),
\]
and
\[
S=(\{0\}\times A_0)\cup(\{1\}\times A_1)\cup(\{2\}\times A_2),
\qquad
T:=|A_0|+|A_1|+|A_2|.
\]
Define
\[
r=\frac{33119}{100000},\qquad
w=1-2r=\frac{16881}{50000},
\qquad
c=wV_0+rV_1+rV_2.
\]
Then \(c\in\operatorname{int}\Delta\), and
\[
h_S(1,c)\ge
\frac{1010113}{2250000}D
=\frac{2T}{9}.
\]

## Proof

Put
\[
k=\frac{u+v}{2}=\frac{553}{1000},
\qquad
t=\frac{1010113}{2250000}.
\]
If \(U\) is uniform on \(\Delta\), define a coupling of the uniform measures on \(A_0,A_2\) by
\[
X_0=V_0+u(U-V_0),\qquad
X_2=V_0+v(U-V_0).
\]
Its midpoint is
\[
\frac{X_0+X_2}{2}=V_0+k(U-V_0),
\]
hence is uniform on \(V_0+k(\Delta-V_0)\). Since
\[
\min\{|A_0|,|A_2|\}=v^2D,
\]
the planar measure from accepted fact `1e5a9785593e5f6a` is
\[
\eta(E)=|\Delta\cap E|+
v^2D\,
\frac{|(V_0+k(\Delta-V_0))\cap E|}{k^2D}.
\tag{1}
\]

We prove that every closed planar halfspace whose boundary contains \(c\) has \(\eta\)-mass at least \(tD\). Apply the affine map taking \(V_0,V_1,V_2\) to
\[
e_0=(0,0),\qquad e_1=(1,0),\qquad e_2=(0,1).
\]
Halfspaces and relative areas are preserved. Thus \(c=(r,r)\), with barycentric coordinates \((w,r,r)\), and for a planar halfspace \(B\),
\[
\frac{\eta(B)}D
=
\frac{|\Delta_0\cap B|}{|\Delta_0|}
+
v^2\frac{|k\Delta_0\cap B|}{|k\Delta_0|},
\qquad
\Delta_0=\operatorname{conv}\{e_0,e_1,e_2\}.
\tag{2}
\]

First suppose that \(B\) contains \(e_0\) and the other two vertices are outside or on its boundary. Normalize an affine functional defining \(B\) so that
\[
\ell(e_0)=1,\qquad \ell(e_1)=-a,\qquad \ell(e_2)=-b,
\qquad a,b\ge0.
\]
The condition \(\ell(c)=0\) is
\[
a+b=s,\qquad s=\frac wr=\frac{33762}{33119}.
\tag{3}
\]
The outer cap has relative area
\[
\frac1{(1+a)(1+b)}\ge4r^2.
\tag{4}
\]
Set
\[
c_0=\frac{1-k}{k}=\frac{447}{553}.
\]
If \(a,b\le c_0\), then
\[
\ell(ke_1)=1-k-ka\ge0,\qquad
\ell(ke_2)=1-k-kb\ge0,
\]
so \(k\Delta_0\subseteq B\). Equations (2) and (4) give
\[
\frac{\eta(B)}D
\ge4r^2+v^2
=t+\frac{205949}{22500000000}>t.
\tag{5}
\]
Otherwise, one of \(a,b\) exceeds \(c_0\). Since \(s/2<c_0<s\), the concavity of
\[
(1+a)(1+s-a)
\]
and symmetry in \(a,b\) give
\[
\frac{|\Delta_0\cap B|}{|\Delta_0|}
\ge
\frac1{(1+c_0)(1+s-c_0)}
=
\frac{10128088271}{22181000000}
=
t+\frac{1531528627}{199629000000}>t.
\tag{6}
\]

Now suppose that \(B\) contains \(e_1\) and the other vertices are outside or on its boundary. Normalize
\[
\ell(e_1)=1,\qquad \ell(e_0)=-a,\qquad \ell(e_2)=-b,
\qquad a,b\ge0.
\]
Then
\[
wa+rb=r,\qquad
b=1-\frac wr a,\qquad
0\le a\le\frac rw.
\tag{7}
\]
The outer cap has relative area \(1/((1+a)(1+b))\). On the inner triangle, the functional values at \(e_0,ke_1,ke_2\) are
\[
-a,\qquad A:=k-(1-k)a,\qquad -(1-k)a-kb.
\]
Moreover,
\[
A\ge\frac{kw-(1-k)r}{w}>0,
\qquad
kw-(1-k)r=\frac{3866193}{100000000}.
\]
Thus the inner intersection is the corner triangle at \(ke_1\), with relative area
\[
\frac{A^2}{k^2(1+a)(1+b)}.
\]
Consequently,
\[
\frac{\eta(B)}D
=
\frac{1+(v^2/k^2)(k-(1-k)a)^2}
{(1+a)(2-(w/r)a)}.
\tag{8}
\]
Exact subtraction of \(t\) gives
\[
\frac{\eta(B)}D-t
=
\frac{Q(a)}
{18230558887800000(1+a)(2-(w/r)a)},
\tag{9}
\]
where
\[
Q(a)=
8464818648133851a^2
-8326157679147098a
+2\,047\,707\,014\,719\,051.
\]
The leading coefficient is positive, and the discriminant is
\[
-8972398413094743608108960000<0.
\]
Hence \(Q(a)>0\) for every real \(a\), so (9) is positive throughout the interval (7). The case in which \(B\) contains only \(e_2\) follows by exchanging \(e_1,e_2\).

It remains to consider a side containing two vertices. Any one-vertex outer cap through \(c\) has relative area at most
\[
U=\frac{w}{1-r}=\frac{33762}{66881}.
\tag{10}
\]
Indeed, for an \(e_0\)-cap, (3) makes \((1+a)(1+b)\) a concave quadratic on \(0\le a\le s\), so the cap area is maximized at an endpoint and is at most \(r/(1-r)\). For an \(e_1\)-cap, (7) again makes the denominator concave; its endpoint cap areas are \(1/2\) and \(w/(1-r)\). The \(e_2\)-case is symmetric. Therefore the outer-triangle contribution of a two-vertex side is at least \(1-U\), and
\[
\frac{\eta(B)}D
\ge1-U
=t+\frac{6960382447}{150482250000}>t.
\tag{11}
\]
If the boundary passes through a vertex, the two sides are endpoint cases of the one-vertex calculations above. Thus (5), (6), (9), and (11) cover every planar halfspace through \(c\), proving
\[
\eta(B)\ge tD.
\tag{12}
\]

For every non-slice-parallel closed halfspace through \((1,c)\), accepted fact `1e5a9785593e5f6a` and (12) give three-slice mass at least \(tD\). The two slice-parallel halfspaces have masses
\[
(u^2+1)D\quad\text{and}\quad(1+v^2)D,
\]
both greater than \(D>tD\). Accepted fact `400272f6de6c67bb` shows that these cases exhaust the boundary-through-\((1,c)\) halfspaces and that restricting to such boundaries does not change depth. Hence
\[
h_S(1,c)\ge tD.
\]
Finally,
\[
T=|A_0|+|A_1|+|A_2|
=(u^2+1+v^2)D
=\frac{1010113}{500000}D,
\]
so \(tD=2T/9\), as claimed.

## External sources

none
