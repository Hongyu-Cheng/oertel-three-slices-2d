---
fact_id: ca6c285cd23ef4dc
kind: lemma
author: "mp_r74_two_cap_complementary_triangle"
assurance: LLM-verified
subgoal_id: canonical-root-tail-two-cap-allocation
depends_on: ["f93a19566af88e9a"]
source_packet_sha256: 3621d1314302038d00c187fe11ef1fdc1b8bf5bb8192c530225a38b3c1b21a47
verifier_run: d05ffa3c19ba4f51
target_match: null
---

## Statement

Use the six rays and sector names of accepted fact `f93a19566af88e9a`:
\[
r_0=(1,0),\quad r_1=(0,1),\quad r_2=(-1,1),\quad
r_3=(-1,0),\quad r_4=(0,-1),\quad r_5=(1,-1),
\]
with sectors \(P,W_x,N_x,O,N_y,W_y\) in cyclic order. Let \(T\) be a nondegenerate triangle containing the origin in its interior, with vertices
\[
A\in\overline{W_x},\qquad B\in\overline O,\qquad
C\in\overline{W_y},
\]
where no vertex is the origin. Denote the six sector areas of \(T\) by the corresponding capital letters. Suppose
\[
\int_T x\,dA\ge0,\qquad \int_T y\,dA\ge0
\]
and
\[
N_x-W_y=N_y-W_x=:e.
\]
Then \(e\le0\). Consequently, no triangle with vertices in the three open sectors \(W_x,O,W_y\) satisfies these hypotheses with \(e>0\). In particular, under the original moment hypotheses,
\[
(e+W_x+W_y+O)^2\ge4e(P+W_x+W_y).
\]
The conclusion remains valid when any of \(A,B,C\) lies on either boundary ray of its indicated closed sector.

## Proof

Put \(s=|T|>0\), and let \(G\) be the centroid of \(T\). The moment assumptions are exactly
\[
x(G)\ge0,\qquad y(G)\ge0.
\]
The balance relation gives
\[
W_x+N_x+O=W_y+N_y+O=:c.
\]
Thus the two one-vertex caps
\[
T\cap\{y\ge0\}\quad\hbox{at }A,\qquad
T\cap\{x\ge0\}\quad\hbox{at }C
\]
have the same area \(s-c\). Set
\[
k=\frac{s-c}{s}.
\]

Let the line \(y=0\) meet \(AB\) and \(AC\) at the fractions \(r,s_1\in(0,1]\) measured from \(A\). The value \(1\) is allowed when the corresponding other vertex lies on \(y=0\). Directly from determinants,
\[
\frac{|T\cap\{y\ge0\}|}{|T|}=r s_1.
\]
Likewise, let \(x=0\) meet \(CA\) and \(CB\) at fractions \(u,v\in(0,1]\) measured from \(C\). Then
\[
\frac{|T\cap\{x\ge0\}|}{|T|}=uv.
\]
Hence
\[
rs_1=uv=k.
\]
The determinant calculation just used is elementary: a corner triangle whose two edge vectors are \(r(B-A)\) and \(s_1(C-A)\) has area \(rs_1|T|\), and similarly at \(C\).

Define nonnegative numbers
\[
R=\frac1r-1,\qquad S=\frac1{s_1}-1,\qquad
U=\frac1u-1,\qquad V=\frac1v-1.
\]
Let \((\alpha,\beta,\gamma)\) be the barycentric coordinates of the origin relative to \(A,B,C\). They are all positive. In barycentric coordinates \((\lambda_A,\lambda_B,\lambda_C)\), the line \(y=0\) has equation
\[
(1+R)\lambda_B+(1+S)\lambda_C=1.
\]
Since it contains the origin,
\[
\alpha=R\beta+S\gamma. \tag{1}
\]
The centroid has barycentric coordinates \((1/3,1/3,1/3)\). Since \(y(G)\ge0\), it is in the closed \(A\)-cap, so
\[
R+S\le1. \tag{2}
\]
Similarly, the line \(x=0\) has equation
\[
(1+U)\lambda_A+(1+V)\lambda_B=1,
\]
and therefore
\[
\gamma=U\alpha+V\beta,\qquad U+V\le1. \tag{3}
\]

The equality \(rs_1=uv=k\) is equivalent to
\[
(1+R)(1+S)=(1+U)(1+V)=\frac1k.
\]
Put
\[
H=R+S+RS=U+V+UV=\frac{1-k}{k}. \tag{4}
\]
Here \(H>0\). Indeed, \(H=0\) would make (1) give \(\alpha=0\), contrary to the origin being interior.

We also have \(US<1\). By (2) and (3), equality \(US=1\) could occur only when
\[
U=S=1,\qquad R=V=0.
\]
In that case both displayed barycentric line equations reduce to
\(\lambda_A=\lambda_C\), so the distinct lines \(x=0\) and \(y=0\) would coincide. This is impossible.

Substituting (1) into (3), and then using (1) once more, gives
\[
\frac{\gamma}{\beta}=\frac{UR+V}{1-US},\qquad
\frac{\alpha}{\beta}=\frac{R+SV}{1-US}. \tag{5}
\]
We next prove that both ratios are at most \(H\). First,
\[
H(1-US)-(R+SV)
=S(1+R-V-HU). \tag{6}
\]
If \(H\le1\), then \(V+HU\le V+U\le1\). If \(H\ge1\), then
\[
V+HU=U+V+(H-1)U\le H,
\]
while (2) gives
\[
H-1=R+S+RS-1\le RS\le R.
\]
Thus \(V+HU\le1+R\) in both cases, and the right side of (6) is nonnegative. Similarly,
\[
H(1-US)-(UR+V)
=U(1+V-R-HS). \tag{7}
\]
For \(H\le1\), \(R+HS\le R+S\le1\). For \(H\ge1\),
\[
R+HS=R+S+(H-1)S\le H,
\]
and (3) gives \(H-1\le UV\le V\). Hence the right side of (7) is also nonnegative. Equations (5) now yield
\[
\alpha\le H\beta,\qquad \gamma\le H\beta. \tag{8}
\]

It remains to compare the cap cut off at \(B\) by \(x+y=0\). Let this line meet \(BA\) and \(BC\) at fractions \(m,n\in(0,1]\) measured from \(B\). The endpoint value \(1\) occurs exactly when \(A\) or \(C\) lies on the corresponding ray \(r_2\) or \(r_5\). The negative \(x+y\) cap has normalized area
\[
h:=\frac{|T\cap\{x+y\le0\}|}{s}=mn. \tag{9}
\]
Its barycentric line equation at the origin is
\[
\frac{\alpha}{m}+\frac{\gamma}{n}=1.
\]
Put \(X=\alpha/m\). Since \(m,n\le1\),
\[
\alpha\le X\le1-\gamma=\alpha+\beta,
\]
and (9) becomes
\[
h=\frac{\alpha\gamma}{X(1-X)}.
\]
The function \(1/[X(1-X)]=1/X+1/(1-X)\) is convex on \((0,1)\). Its maximum on the displayed interval is therefore attained at an endpoint. Consequently,
\[
h\le
\max\left\{\frac{\gamma}{\beta+\gamma},
\frac{\alpha}{\alpha+\beta}\right\}.
\]
Using (8) and then (4),
\[
h\le\frac{H}{1+H}=1-k=\frac cs. \tag{10}
\]

Finally,
\[
hs=N_x+O+N_y,
\]
so balance gives
\[
hs-c=N_y-W_x=N_x-W_y=e.
\]
Inequality (10) proves \(e\le0\). Since all sector areas are nonnegative, this also gives
\[
(e+W_x+W_y+O)^2\ge0\ge4e(P+W_x+W_y).
\]

All ray-boundary cases were included directly by allowing
\(r,s_1,u,v,m,n=1\), equivalently allowing any of
\(R,S,U,V\) to vanish. The only potentially singular case \(US=1\) was excluded above from the distinctness of the two fan lines. No fraction can be zero while the triangle is nondegenerate and the fan point is interior. Any further degenerate vertex limit inherits \(e\le0\) by continuity of the areas of a triangle clipped by the six fixed closed sectors.

The complementary-parity triangle in accepted fact `f93a19566af88e9a` does not contradict this result: its centroid is
\[
\frac13\bigl((-4,6)+(-4,-22)+(3,-1)\bigr)
=\left(-\frac53,-\frac{17}3\right),
\]
so it violates both nonnegative centroid moment hypotheses.

## External sources

none
