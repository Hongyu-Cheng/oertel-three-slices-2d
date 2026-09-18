---
fact_id: ecfebb3fd79fcd5d
kind: lemma
author: "r127_above_o12"
assurance: LLM-verified
subgoal_id: triangle-above-half-o12-three-supports
depends_on: ["48d8328cbba82dba","b8734f5137d2af29"]
source_packet_sha256: 50f0b2602118bcf1846940e027de4624d6294e04bceedca28c3ce0de035e9ac6
verifier_run: 4e174932292a450f
target_match: null
---

## Statement

Assume the full transformed triangular system of accepted fact `b8734f5137d2af29` with
\[
t=\frac{2(1+A+B)}9>\frac12,
\qquad (I_0,I_1)=(\{1\},\{2,3\}).
\]
There is no compatible strict system in any of the three all-nonzero common-column support representatives
\[
(\{1\},\{2\},\{3\}),\qquad
(\{1,2\},\{1\},\{3\}),\qquad
(\{1,2\},\{3\},\{3\}),
\]
and there is no such system in any necessary weak-sign boundary stratum.  Thus the complete above-half orbit \(\mathcal O_{12}\), including the boundaries on which zeros occur only in row \(1\), is infeasible.

## Proof

Put
\[
X_i:=Au_i,\qquad Y_i:=Bv_i,\qquad
\beta:=\frac{2(A+B-1)}9=t-\frac49.
\tag{1}
\]
For \(i=2,3\), accepted facts `48d8328cbba82dba` and `b8734f5137d2af29` give
\[
\frac49\le c_i<\frac12,qquad
X_i+Y_i<t-c_i\le\beta.
\tag{2}
\]
Moreover,
\[
0<A<B<1+A,qquad A+B>\frac54,qquad
\beta<\frac{4A}{9}.
\tag{3}
\]

We first record a compatibility consequence that applies whenever the unique positive columns of rows \(2\) and \(3\) are distinct.  For \(j=0,1,2\), define
\[
K_j:=P_j\cap\{z_2\le0,\ z_3\le0\}.
\tag{4}
\]
Set
\[
X:=X_2+X_3,qquad Y:=Y_2+Y_3,qquad E:=X+Y.
\]
The closed-cap definitions and the union bound give
\[
|K_0|\ge A-X,qquad |K_2|\ge B-Y.
\tag{5}
\]
This is literal on every endpoint zero-level stratum: the complement of \(K_j\) is contained in the union of the two strict positive-coordinate sets, whose areas are no larger than the corresponding closed-cap areas.  By (2),
\[
E<2\beta<\frac{8A}{9}<A<B,
\tag{6}
\]
so both lower bounds in (5) are positive.

Compatibility gives the actual containment
\[
\frac{K_0+K_2}{2}\subseteq K_1.
\tag{7}
\]
Indeed, the midpoint of two points whose second and third coordinates are nonpositive again has both coordinates nonpositive.  Planar Brunn-Minkowski applied in the common translation plane, together with (5)-(7), yields
\[
2\sqrt{|K_1|}
\ge \sqrt{|K_0|}+\sqrt{|K_2|}
\ge \sqrt{A-X}+\sqrt{B-Y}.
\tag{8}
\]

For fixed \(E=X+Y<A\), the function
\[
f(r)=\sqrt{A-r}+\sqrt{B-E+r},\qquad 0\le r\le E,
\]
is concave.  Its minimum is at an endpoint, and \(A<B\) gives
\[
\sqrt{A-E}+\sqrt B\le \sqrt A+\sqrt{B-E}.
\]
Consequently (6) implies
\[
\sqrt{A-X}+\sqrt{B-Y}
\ge\sqrt{A-E}+\sqrt B
>\sqrt{A-2\beta}+\sqrt B.
\tag{9}
\]

The last expression has a uniform exact lower bound.  Put
\[
s:=A+B,\qquad \eta:=B-A.
\]
Then \(s>5/4\), \(0<\eta<1\), and
\[
A-2\beta=\frac{s+8-9\eta}{18},
\qquad B=\frac{s+\eta}{2}.
\tag{10}
\]
For fixed \(s\), let
\[
F_s(\eta)
=\sqrt{\frac{s+8-9\eta}{18}}
 +\sqrt{\frac{s+\eta}{2}}.
\]
The second radicand is larger than the first because
\[
\frac{s+\eta}{2}-\frac{s+8-9\eta}{18}
=\frac{8s+18\eta-8}{18}>0.
\]
Therefore
\[
F_s'(\eta)
=-\frac{1}{4\sqrt{(s+8-9\eta)/18}}
 +\frac{1}{4\sqrt{(s+\eta)/2}}<0.
\]
Since \(\eta<1\) and the resulting expression is increasing in \(s\),
\[
\begin{aligned}
\sqrt{A-2\beta}+\sqrt B
&>\sqrt{\frac{s-1}{18}}+\sqrt{\frac{s+1}{2}}\\
&>\sqrt{\frac1{72}}+\sqrt{\frac98}
=\frac5{3\sqrt2}
>\frac2{\sqrt3}.
\end{aligned}
\tag{11}
\]
The final strict comparison follows by squaring: \(25/18>4/3=24/18\).  Equations (8)-(11) force
\[
|K_1|>\frac13.
\tag{12}
\]

We now prove the opposite bound when rows \(2\) and \(3\) have distinct positive columns.  After one common column permutation, write
\[
L_{2*}=(-a,p,-b),qquad
L_{3*}=(-c,-d,q),
\tag{13}
\]
where all six displayed parameters are positive and
\[
p\ge a+b,qquad q\ge c+d.
\tag{14}
\]
These inequalities include either middle-mean boundary.  Subtract the nonnegative centroid value from each affine row.  On \(\Delta\), this only enlarges its nonpositive halfplane.  The shifted row \(2\) has sum zero and can be written
\[
(-r,r+s,-s),\qquad r,s>0,
\]
while shifted row \(3\) has sum zero and can be written
\[
(-u,-v,u+v),\qquad u,v>0.
\]
Their zero lines pass through the centroid
\(G=(e_1+e_2+e_3)/3\).  The first line meets the edge \(e_1e_2\) at
\[
E_2=(1-\alpha)e_1+\alpha e_2,qquad
\alpha=\frac{r}{2r+s}<\frac12,
\]
and the second meets \(e_1e_3\) at
\[
E_3=(1-\gamma)e_1+\gamma e_3,qquad
\gamma=\frac{u}{2u+v}<\frac12.
\]
A direct sign inspection shows that the intersection of the two enlarged nonpositive halfplanes inside \(\Delta\) is exactly
\[
Q=\operatorname{conv}\{e_1,E_2,G,E_3\}.
\]
In the affine coordinates \(e_1=(0,0),e_2=(1,0),e_3=(0,1)\), its ordinary area is \((\alpha+\gamma)/6\), whereas the ordinary area of \(\Delta\) is \(1/2\).  Hence its normalized area is
\[
|Q|=\frac{\alpha+\gamma}{3}<\frac13.
\tag{15}
\]
Since \(K_1\subseteq Q\), (15) contradicts (12).  This excludes the first two all-nonzero representatives in the statement.  Notice that equality of either original row mean causes no loss: the corresponding enlargement is then equality, while \(\alpha,\gamma<1/2\) remains strict because every \(I_1\)-row is all-nonzero.

The same argument excludes every row-1 zero boundary.  Indeed, the accepted boundary catalog gives singleton positive supports in rows \(2,3\), no zeros in those rows, column cover, a nonempty negative support in every row, and \(Z_1\ne\varnothing\).  If rows \(2,3\) had the same positive column \(r\), column cover would force row \(1\) to be positive in both other columns.  Its required negative support would then force its entry in column \(r\) to be negative, leaving no zero entry in row \(1\), a contradiction.  Thus every actual row-1 zero boundary has distinct positive columns in rows \(2,3\), and (4)-(15) applies to it literally.

It remains to exclude the third all-nonzero representative, where rows \(2\) and \(3\) have the same positive column.  In its fixed common labeling write
\[
L_{2*}=(-a,-b,p),qquad
L_{3*}=(-c,-d,q),
\qquad a,b,c,d,p,q>0.
\tag{16}
\]
Because \(c_2,c_3<1/2\), the exact one-positive cap formulas give
\[
(p+a)(p+b)>2p^2,qquad
(q+c)(q+d)>2q^2.
\tag{17}
\]
Put \(P=p+q\) and
\[
D=(P+a+c)(P+b+d).
\]
For positive \(x,y,u,v\),
\[
\sqrt{(x+u)(y+v)}\ge\sqrt{xy}+\sqrt{uv},
\tag{18}
\]
because the difference of the squares is
\((\sqrt{xv}-\sqrt{uy})^2\).  Apply (18) with
\[
x=p+a,\quad y=p+b,\quad u=q+c,\quad v=q+d.
\]
Using (17), we obtain
\[
\sqrt D
\ge\sqrt{(p+a)(p+b)}+\sqrt{(q+c)(q+d)}
>\sqrt2(p+q)=\sqrt2P,
\]
and therefore
\[
D>2P^2.
\tag{19}
\]

The common column equations force
\[
L_{1*}=(1+a+c,\ 1+b+d,\ 1-P).
\tag{20}
\]
The third support representative requires \(1-P<0\), so \(P>1\).  The exact two-positive cap formula for (20) is
\[
c_1
=1-\frac{(P-1)^2}{(P+a+c)(P+b+d)}
=1-\frac{(P-1)^2}{D}.
\tag{21}
\]
Equations (19)-(21) give
\[
c_1>1-\frac{P^2}{D}>\frac12.
\tag{22}
\]
But row \(1\in I_0\), so accepted fact `b8734f5137d2af29` gives
\[
c_1<\kappa=\frac{2(1+B-A)}9<\frac49,
\tag{23}
\]
contradicting (22).

The three all-nonzero supports and the row-1 zero catalog are exhaustive by accepted fact `b8734f5137d2af29`.  The argument retained the common vertex labeling, both middle-mean boundaries, the exact closed cap formulas, all endpoint zero levels, determinant nonzero, and the literal strict row inequalities.  The distinct-support contradiction used full midpoint compatibility, while the same-support contradiction already follows from a weaker subset of the continuous requirements.  Hence no full compatible strict system exists in \(\mathcal O_{12}\).

## External sources

none
