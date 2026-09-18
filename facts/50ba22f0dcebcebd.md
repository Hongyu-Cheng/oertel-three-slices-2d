---
fact_id: 50ba22f0dcebcebd
kind: lemma
author: "mp_r385_opposite_rotated_cone"
assurance: LLM-verified
subgoal_id: counterexample-opposite-asymmetric-low-r
depends_on: ["38b9d85f6c0c57a2","5b75ecd9ec86dbcf","6f6869df3d151764","a7747c32a219e2c9","cc8c0bf6093b9357","cf1a8ff16a0da82a"]
source_packet_sha256: b18f4359fa71919a5345c5c01a92155f954fa53212b0295aa746067a4f51d05f
verifier_run: 4a0e129e6a4d43af
target_match: null
---

## Statement

Put
\[
f_1(x,y)=x,\qquad f_2(x,y)=y,\qquad
f_3(x,y)=-1-x-y,\qquad L_1=L_2=L_3=-100.
\tag{1}
\]
Let
\[
P=\left(-\frac{100001}{1000},-\frac{10000001}{100000}\right),
\quad
V=\left(\frac{19713}{100},-\frac{61331}{625}\right),
\quad
R=\left(3,-\frac{197}{2}\right),
\tag{2}
\]
\[
A_0=\operatorname{conv}\{P,V,R\}.
\tag{3}
\]
Let
\[
c=\left(-\frac{99}{2},\frac{991}{10}\right),\qquad
a=\left(302,\frac{19}{10}\right),\qquad
s=\left(0,\frac1{100000}\right),
\tag{4}
\]
\[
A_2=
c+\left[-\frac12,\frac12\right]a
+\left[-\frac12,\frac12\right]s,
\qquad
B=\frac{A_0+A_2}{2}.
\tag{5}
\]
Then \(A_0,A_2,B\) are rational two-dimensional convex polygons.  The
tangent cone of \(A_0\) at \(P\) intersects the interiors of all three
large-endpoint cap regions
\[
\{x\le-100\},\qquad \{y\le-100\},\qquad \{x+y\ge99\}.
\tag{6}
\]
The endpoint normal fans are transverse, the three endpoint cuts are
proper and transverse, and
\[
0<\frac{|A_2|}{|A_0|}<\frac38.
\tag{7}
\]
Writing \(p_i=f_i-L_i\), \(q_i=f_i+L_i\), the exact cells
\[
P_J=A_0\cap\{p_j\le0:j\in J,\ p_j>0:j\notin J\},
\]
\[
Q_J=A_2\cap\{q_j\le0:j\in J,\ q_j>0:j\notin J\}
\tag{8}
\]
have \(p_{\varnothing}>0\) and the positive opposite pair
\[
q_{\{3\}}>0,\qquad q_{\{1,2\}}>0.
\tag{9}
\]
All three right-orientation derivatives at the levels in (1) are
strictly negative.  The endpoint applications of accepted fact
`5b75ecd9ec86dbcf` are strict.

Finally, the scalar completion interval of accepted fact
`6f6869df3d151764` and the convex three-cap cutoff of accepted fact
`a7747c32a219e2c9` have a common interior point: \(A=20\).  Every zero
line \(\{f_i=0\}\) crosses the interior of \(B\), so the strict
support-clearance premise of accepted fact `cf1a8ff16a0da82a` is absent
in all three rows.  This statement does not assert that a compatible
convex \(K\) exists.

## Proof

The three vertices in (2) are counterclockwise because
\[
\det(V-P,R-P)=\frac{2530453709}{10000000}>0.
\tag{10}
\]
Moreover,
\[
-100-P_x=\frac1{1000},\qquad
-100-P_y=\frac1{100000},\qquad
V_x+V_y-99=\frac1{2500}.
\tag{11}
\]
Thus \(P\) lies strictly in the first two regions in (6), while \(V\)
lies strictly in the third.  Since
\[
P+\operatorname{cone}\{V-P,R-P\}
\]
is two-dimensional and contains \(A_0\), (11) proves the tangent-cone
claim.  Exact clipping gives the three positive large-endpoint caps
\[
(u_1,u_2,u_3)=
\left(
\frac{2530453709}{612095802620000000},
\frac{2530453709}{561126740820000000},
\frac{2530453709}{7269486730695500000}
\right).
\tag{12}
\]

The endpoint and midpoint areas are
\[
M:=|A_0|=\frac{2530453709}{20000000},\qquad
m:=|A_2|=\frac{151}{50000},\qquad
k_0:=|B|=\frac{9595744919}{100000000}.
\tag{13}
\]
In particular,
\[
\frac mM=\frac{60400}{2530453709}<\frac38.
\tag{14}
\]
Exact clipping of the small endpoint at level \(100\) gives
\[
(v_1,v_2,v_3)=
\left(
\frac{601}{200000},
\frac{5587}{1900000},
\frac{304567}{101300000}
\right).
\tag{15}
\]

For a cut \(f_i=t\), let the projection density be the line-section
length divided by the norm of the linear part of \(f_i\).  At the
large-endpoint levels \(-100\), the densities are
\[
(\rho^0_1,\rho^0_2,\rho^0_3)=
\left(
\frac{2530453709}{306047901310000},
\frac{2530453709}{2805633704100},
\frac{2530453709}{1\,453\,897\,346\,139\,100}
\right),
\tag{16}
\]
while at the small-endpoint levels \(100\) they are
\[
(\rho^2_1,\rho^2_2,\rho^2_3)=
\left(
\frac1{100000},
\frac{151}{95000},
\frac{151}{15195000}
\right).
\tag{17}
\]
Their differences are
\[
\rho^0_1-\rho^2_1
=-\frac{5300253041}{3\,060\,479\,013\,100\,000}<0,
\tag{18}
\]
\[
\rho^0_2-\rho^2_2
=-\frac{1832575869641}{2\,665\,352\,018\,895\,000}<0,
\tag{19}
\]
\[
\rho^0_3-\rho^2_3
=-\frac{1\,810\,882\,551\,587\,491}{220919701745836245000}<0.
\tag{20}
\]
Equations (12), (15), and (16)-(20) show that all six cuts are proper
and that all three lower crossings have the required strict
orientation.

For completeness, put
\[
e_1=V-P,\qquad e_2=R-V,\qquad e_3=P-R.
\]
The determinants of these three edge directions against the two
generators \(a,s\) of \(A_2\) are
\[
\begin{array}{c|rr}
&\det(e_j,a)&\det(e_j,s)\\ \hline
j=1&-\dfrac{7873}{25000}&\dfrac{297131}{100000000}\\[1mm]
j=2&-\dfrac{1284931}{5000}&-\dfrac{19413}{10000000}\\[1mm]
j=3&\dfrac{804066}{3125}&-\dfrac{103001}{100000000}.
\end{array}
\tag{21}
\]
All six values are nonzero.  Against tangent directions
\((0,1),(1,0),(1,-1)\) of the three cutting lines, the corresponding
determinants are
\[
\begin{array}{c|rrr}
j=1&\dfrac{297131}{1000}&-\dfrac{187041}{100000}&
-\dfrac{29900141}{100000}\\[1mm]
j=2&-\dfrac{19413}{100}&\dfrac{463}{1250}&
\dfrac{486251}{2500}\\[1mm]
j=3&-\dfrac{103001}{1000}&\dfrac{150001}{100000}&
\dfrac{10450101}{100000}.
\end{array}
\tag{22}
\]
This proves both claimed transversality statements.

The exact cell audit in the convention (8) gives
\[
p_{\varnothing}
=\frac{708778275366974997175890328469}
{5601985706178293944540620000}>0,
\tag{23}
\]
\[
p_{\{1,2\}}=\frac{3047876709}{891398942620000000}>0,
\qquad
p_{\{1,3\}}=p_{\{2,3\}}=0,
\tag{24}
\]
\[
q_{\{1\}}=0,\qquad
q_{\{3\}}=\frac3{200000}>0,\qquad
q_{\{1,2\}}=\frac{1359}{101300000}>0.
\tag{25}
\]
Thus (9) is a genuine positive opposite pair.  Equations (24)-(25)
also show that accepted fact `cc8c0bf6093b9357` does not obstruct this
endpoint pair: three of its six required positive cells are exactly
zero.  The formal survivor in accepted fact `38b9d85f6c0c57a2` has
\(m/M=1/100\) and all three \(P\)-doubletons positive.  The present
construction instead supplies simultaneous rational planar
realizations of \(A_0,A_2,B\), but in the different boundary class
\(p_{\{1,3\}}=p_{\{2,3\}}=q_{\{1\}}=0\), with
\(m/M=60400/2530453709\).  It therefore does not claim to realize that
formal table.

Applying accepted fact `5b75ecd9ec86dbcf` to
\(-p_i/299\) on \(A_0\) and to \(q_i/301\) on \(A_2\), the exact
three-cap residuals are respectively
\[
\frac{
157951051306024373772615004459524555925536239
}{
249680206752984261167952879481961220000000
}>0
\tag{26}
\]
and
\[
\frac{57884951}{3849400000}>0.
\tag{27}
\]
Hence neither endpoint gate is being bypassed.

Exact Minkowski addition followed by clipping at the three zero lines
gives
\[
(b_1,b_2,b_3)=
\left(
\frac{3203450752179}{60400000000},
\frac{74483373429}{2000000000},
\frac{264042158263769}{6078000000000}
\right).
\tag{28}
\]
With
\[
h_0=\frac{2(M+m+k_0)}9,\qquad
F_i=u_i+v_i+b_i-h_0,
\]
the defects are
\[
F_1=
\frac{59885164376080138150589}
{16636763915211600000000},
\tag{29}
\]
\[
F_2=
-\frac{39008195865043650320207}
{3198422422674000000000},
\tag{30}
\]
\[
F_3=
-\frac{1589407059454011396894980443}
{265103642095003494000000000}.
\tag{31}
\]
The exact ordering is \(F_1>F_3>F_2\).  Accepted fact
`6f6869df3d151764` therefore gives the scalar interval
\[
L\le A\le U,
\tag{32}
\]
where
\[
L=\frac92F_1
=\frac{59885164376080138150589}
{3697058647824800000000},
\tag{33}
\]
\[
U=-3(F_1+F_2+F_3)
=
\frac{
42354215356979399235878229679446945185278952895151
}{
967526447794103865706183933039713930403120000000
}.
\tag{34}
\]

Write \(d_i=u_i+v_i\).  Their exact order is
\(d_3>d_1>d_2\).  Accepted fact `a7747c32a219e2c9` gives the additional
cutoff
\[
A\le G:=M+m-k_0-\frac52(d_1+d_2+d_3)+3d_3,
\tag{35}
\]
\[
G=
\frac{
367086130552534233735438519945484402660504769021
}{
12013987348436720186748972678473269003350000000
}.
\tag{36}
\]
The rational value \(A=20\) lies strictly in the intersection because
\[
20-L=
\frac{14056008580415861849411}
{3697058647824800000000}>0,
\tag{37}
\]
\[
U-20=
\frac{
23003686401097321921754551018652666577216552895151
}{
967526447794103865706183933039713930403120000000
}>0,
\tag{38}
\]
\[
G-20=
\frac{
126806383583799830000459066376019022593504769021
}{
12013987348436720186748972678473269003350000000
}>0.
\tag{39}
\]
This proves the claimed scalar-plus-three-cap overlap.

Both sides of each zero cut contain positive midpoint area.  Indeed,
the three values in (28) are positive, and their complementary areas
are
\[
\left(
\frac{2592379178897}{60400000000},
\frac{117431524951}{2000000000},
\frac{319187217913051}{6078000000000}
\right)>0
\tag{40}
\]
componentwise.  Since \(B\) is convex and two-dimensional, every line
\(\{f_i=0\}\) therefore crosses \(\operatorname{int}B\).  Neither of
its closed sides contains \(B\), so the strict containing-halfplane
premise of the positive support-clearance conclusion in accepted fact
`cf1a8ff16a0da82a` fails in every row.

At the interior value \(A=20\), any exact convex completion would have
to satisfy
\[
\left|(K\setminus B)\cap\{f_i\le0\}\right|
=\frac{40}{9}-F_i.
\tag{41}
\]
The three required values are
\[
\left(
\frac{14056008580415861849411}
{16636763915211600000000},
\frac{53223406632483650320207}
{3198422422674000000000},
\frac{2767645468765138036894980443}
{265103642095003494000000000}
\right).
\tag{42}
\]
They are all strictly between \(0\) and \(20\), and their sum exceeds
\(20\), exactly as required by the scalar identities.  Thus (42) is a
fully rational simultaneous-realizability target for the remaining
convex \(K\) search.  SageMath \(10.8\) over \(\mathbb Q\)
independently constructed all polygons, clips, line sections,
Minkowski sums, cells, residuals, order comparisons, and margins in
(10)-(42).  No floating-point output is used in this certificate.

## External sources

none
