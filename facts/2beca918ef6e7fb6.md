---
fact_id: 2beca918ef6e7fb6
kind: lemma
author: "r121-full-translation"
assurance: LLM-verified
subgoal_id: nine-cover-full-translation
depends_on: ["89eb6334d7b8b1d8","8f5f00ddd4f22d2f","a58dc34569c34d62"]
source_packet_sha256: 18c19fd8156b605294ccce6b835f93334c31671f0a405b0f2ae9032d4e957976
verifier_run: d90c5db797844c02
target_match: null
---

## Statement

Use the exact objects of accepted fact `89eb6334d7b8b1d8`, explicitly
\[
\Delta=\operatorname{conv}\{(0,0),(1,0),(0,1)\},
\qquad g=\left(\frac13,\frac13\right),
\]
and the quadrilateral \(Q\) with cyclic vertices
\[
q_0=\left(\frac1{20},\frac1{20}\right),\quad
q_1=\left(\frac{11}{20},\frac{21}{400}\right),\quad
q_2=\left(\frac12,\frac{23}{400}\right),\quad
q_3=\left(\frac1{10},\frac{21}{400}\right).
\]
For every \(v=(a,b)\in\mathbb R^2\), set
\[
A_0=\Delta,\qquad A_1=\Delta+v,\qquad A_2=Q.
\]
Then the exact compatibility set is
\[
\begin{aligned}
\mathcal V
&=\left\{v:\frac{\Delta+Q}{2}\subseteq\Delta+v\right\}\\
&=\left\{(a,b):a\leq\frac1{40},\ b\leq\frac1{40},\ a+b\geq-\frac{159}{800}\right\}\\
&=\operatorname{conv}\left\{
\left(\frac1{40},\frac1{40}\right),
\left(\frac1{40},-\frac{179}{800}\right),
\left(-\frac{179}{800},\frac1{40}\right)
\right\}.
\end{aligned}
\]
Moreover, for every \(v\in\mathcal V\), put
\[
S_v=\bigcup_{i=0}^2(\{i\}\times A_i),\qquad
T=\sum_{i=0}^2|A_i|=\frac{16027}{16000},\qquad
t=\frac{2T}{9}=\frac{16027}{72000}.
\]
For a closed halfspace \(H\subseteq\mathbb R^3\), let
\[
\mu_v(H)=\sum_{i=0}^2
\left|\{z\in A_i:(i,z)\in H\}\right|,
\]
and define \(h_{S_v}(y)=\inf\{\mu_v(H):H\text{ is a closed halfspace containing }y\}\).  Then
\[
h_{S_v}((1,g+v))
\geq \frac29+\frac{27}{16000}
=t+\frac{21}{16000}>t.
\]
Consequently, for every \(v\in\mathcal V\), no collection of closed halfspaces of \(S_v\)-mass strictly below \(t\), even of arbitrary cardinality, covers \(\{1\}\times(\Delta+v)\) by its interiors.  Thus the middle-slice condition in accepted fact `8f5f00ddd4f22d2f` fails uniformly throughout the full compatible translation polygon.

## Proof

The translated triangle has the exact facet description
\[
\Delta+v=\{(x,y):x\geq a,\ y\geq b,\ x+y\leq1+a+b\}.
\tag{1}
\]
The extrema of an affine functional on a Minkowski average are the averages of its extrema on the two summands.  From the displayed vertices,
\[
\min_Qx=\min_Qy=\frac1{20},
\qquad
\max_Q(x+y)=q_{1,x}+q_{1,y}=\frac{241}{400}.
\]
Since
\[
\min_\Delta x=\min_\Delta y=0,
\qquad
\max_\Delta(x+y)=1,
\]
we obtain
\[
\min_{(\Delta+Q)/2}x=\min_{(\Delta+Q)/2}y=\frac1{40},
\qquad
\max_{(\Delta+Q)/2}(x+y)=\frac{641}{800}.
\tag{2}
\]
By (1), containment of \((\Delta+Q)/2\) in \(\Delta+v\) is equivalent to its satisfying the three facet inequalities.  Equation (2) therefore gives exactly
\[
a\leq\frac1{40},\qquad b\leq\frac1{40},\qquad
\frac{641}{800}\leq1+a+b,
\]
which is the asserted inequality description of \(\mathcal V\).  Intersecting its three boundary lines gives the three displayed vertices, so this is the asserted two-dimensional triangle.

The same three inequalities have a second useful interpretation.  The set \(Q-2v\) is contained in \(\Delta\) if and only if
\[
\min_Qx-2a\geq0,\qquad
\min_Qy-2b\geq0,\qquad
\max_Q(x+y)-2(a+b)\leq1.
\]
Substituting the three extrema of \(Q\) shows that these conditions are respectively
\[
a\leq\frac1{40},\qquad b\leq\frac1{40},\qquad
a+b\geq-\frac{159}{800}.
\]
Hence
\[
v\in\mathcal V\quad\Longleftrightarrow\quad Q-2v\subseteq\Delta.
\tag{3}
\]

Shoelace evaluation of the displayed cyclic vertex list gives
\[
|Q|=\frac{27}{16000}.
\]
Translation preserves \(|\Delta|=1/2\), so the asserted values of \(T\) and \(t\) follow.

Fix \(v\in\mathcal V\), and let \(H\) be a closed halfspace containing \((1,g+v)\).  The whole-space halfspace, if allowed, has mass \(T\) and satisfies the claimed lower bound.  If \(H\) is proper and its boundary does not contain \((1,g+v)\), translate its boundary parallel toward this point until it does.  The resulting closed halfspace is contained in \(H\), so it is enough to prove the lower bound when the boundary passes through \((1,g+v)\).

First suppose that the planar part of the normal is nonzero.  Then for some \(u\in\mathbb R^2\setminus\{0\}\) and \(\beta\in\mathbb R\), the halfspace can be written
\[
H=\{(h,z):L(z-v)+\beta(h-1)\geq0\},
\qquad L(w)=u\cdot(w-g).
\tag{4}
\]
At height \(1\), writing \(z=w+v\) with \(w\in\Delta\), its contribution is
\[
|\Delta\cap\{L\geq0\}|.
\]
The centroid-cap estimate in accepted fact `a58dc34569c34d62` gives
\[
|\Delta\cap\{L\geq0\}|\geq\frac29.
\tag{5}
\]

If the height-\(2\) section of \(H\) contains all of \(Q\), then (5) gives
\[
\mu_v(H)\geq\frac29+|Q|
=\frac29+\frac{27}{16000}.
\tag{6}
\]
Suppose instead that this section does not contain all of \(Q\).  Choose \(q\in Q\) outside the closed section.  By (4),
\[
L(q-v)+\beta<0.
\tag{7}
\]
At height \(0\), the section on \(A_0=\Delta\) is
\[
\Delta\cap\{L\geq\beta+u\cdot v\}.
\tag{8}
\]
Let \(-A=\min_{w\in\Delta}L(w)\); since \(L\neq0\) and \(L(g)=0\), one has \(A>0\).  Equations (3) and (7) imply
\[
\begin{aligned}
\beta+u\cdot v
&<-L(q-v)+u\cdot v\\
&=-L(q-2v)\\
&\leq A,
\end{aligned}
\tag{9}
\]
because \(q-2v\in\Delta\).  Thus the section (8) contains \(\Delta\cap\{L\geq A\}\).  The exact two-cap estimate in accepted fact `a58dc34569c34d62`, combined with the height-\(1\) contribution, yields
\[
\begin{aligned}
\mu_v(H)
&\geq |\Delta\cap\{L\geq0\}|
 +|\Delta\cap\{L\geq A\}|\\
&\geq\frac6{25}+\frac1{11700}\\
&=\left(\frac29+\frac{27}{16000}\right)
  +\frac{30281}{1872000}
>\frac29+\frac{27}{16000}.
\end{aligned}
\tag{10}
\]

If the planar part of the normal vanishes, a proper boundary-through-height-\(1\) halfspace contains either the height-\(1\) and height-\(2\) slices, of mass \(1/2+27/16000\), or the height-\(0\) and height-\(1\) slices, of mass \(1\).  Both masses exceed the right-hand side of (6).  Equations (6) and (10), together with this final case, show that every closed halfspace containing \((1,g+v)\) has mass at least
\[
\frac29+\frac{27}{16000}.
\]
Taking the infimum proves the depth bound.  Finally,
\[
\frac29+\frac{27}{16000}-t
=\frac79\,\frac{27}{16000}
=\frac{21}{16000}>0.
\]

The point \(g+v\) lies in the interior of \(\Delta+v\).  If interiors of strict-low closed halfspaces covered the middle slice, one of those interiors would contain \((1,g+v)\).  Its closed halfspace would then contain that point but have mass below \(t\), contradicting the depth bound.  This proves uniform middle protection and, by accepted fact `8f5f00ddd4f22d2f`, rules out a direct three-slice strict-low cover for every \(v\in\mathcal V\).

## External sources

none
