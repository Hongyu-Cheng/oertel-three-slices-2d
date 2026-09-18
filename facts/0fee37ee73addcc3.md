---
fact_id: 0fee37ee73addcc3
kind: final
author: "r134_final_composition"
assurance: LLM-verified
subgoal_id: r134-final-three-slice-centerpoint
depends_on: ["30d5406c9459a845","851e063a1b9908a3","9414163c0331b8f2","c4077ad10a0441a5","cddd2c95c0ff12e3"]
source_packet_sha256: 7625c455ee23d0b46e3e312d7ffa06897d167b94043a99420aa9338e8ec72c56
verifier_run: 52ff66fe4f514d22
target_match: true
---

## Statement

For every compact polytope \(C\subset\mathbb R^3\) such that
\[
S:=C\cap(\mathbb Z\times\mathbb R^2)
=(\{0\}\times A_0)\cup(\{1\}\times A_1)\cup(\{2\}\times A_2),
\]
where each \(A_i\subset\mathbb R^2\) is a nonempty two-dimensional convex body, put \(a_i=|A_i|\) and \(T=a_0+a_1+a_2\). For \(y\in S\), define
\[
h_S(y)=\inf\left\{\mathcal H_2(S\cap H):
H\subset\mathbb R^3\text{ is a closed halfspace and }y\in H\right\}.
\]
Here \(\mathcal H_2(S\cap H)\) is the sum of the planar areas contributed by the three slices. There exists \(y^*\in S\) such that \(h_S(y^*)\ge2T/9\).

## Proof

First, the assertion (N) in accepted fact `cddd2c95c0ff12e3` follows from accepted fact `9414163c0331b8f2`. To check its full quantified domain, fix arbitrary \(\rho,\sigma>1\) and \(0<a,b<1\) with \(a(2\sigma-1)\le\sigma\) and \(b(2\rho-1)\le\rho\). These are within the extension-factor domain of `9414163c0331b8f2`, and its two base-hit conditions are the same weak inequalities. With identical parameters in the two facts, their formulas agree exactly:
\[
\begin{aligned}
C_L&=\frac{\sigma(\rho-a)^2}{\rho+\sigma-2\sigma a},&
C_R&=\frac{\rho(\sigma-b)^2}{\rho+\sigma-2\rho b},\\
D_3&=\frac{(2\rho\sigma-\rho-\sigma)^2(a+b-2ab)}
{2(\rho+\sigma-2\sigma a)(\rho+\sigma-2\rho b)}.
\end{aligned}
\]
All denominators are positive by `9414163c0331b8f2`. If \(C_L\ge C_R\ge1\) and \(C_L+C_R<\rho\sigma\), that fact applies with exactly these cap floors, ordering, and strict pair sum. Its singleton area is \((a+b)/2\), and its conclusion gives \(((a+b)/2)^2\le D_3\le C_LD_3\). The second inequality uses \(C_L\ge1\) and the nonnegative overlap area \(D_3\). This proves every instance of (N), including equality in either base-hit constraint.

We now establish the universal planar assertion required by accepted fact `30d5406c9459a845`. Let \(K\subset\mathbb R^2\) be any compact convex body with nonempty interior, let \(z\in\operatorname{int}K\), and let \(Q_1,Q_2,Q_3\) be any three closed halfplanes whose boundary lines pass through \(z\), with nonzero, pairwise nonparallel oriented normals admitting a strictly positive linear dependence. Label the caps so that \(c_1\ge c_2\ge c_3\), where \(c_j=|K\cap Q_j|\), and put \(s_3=|K\setminus(Q_1\cup Q_2)|\) and \(h=5c_1/4+c_2-|K|\). We claim that \(h\ge0\) and
\[
4s_3\le\left(\frac32\sqrt{c_1}+\sqrt h\right)^2.
\tag{1}
\]

We prove \(h\ge0\) directly using accepted theorem `851e063a1b9908a3`. If \(c_1+c_2\ge|K|\), then \(h\ge c_1/4\ge0\). Otherwise translate the center to the origin and positively rescale the defining forms so that \(Q_i-z=\{v:\ell_i(v)\le0\}\) and \(\ell_1+\ell_2+\ell_3=0\). The cap area \(|(K-z)\cap\{\ell_1+t\ell_2\ge0\}|\) varies continuously for \(0\le t\le1\). Indeed, these forms are nonzero, and the cutting lines have planar area zero. At \(t=0\) the area is \(|K|-c_1>c_2\), and at \(t=1\) it is \(c_3\le c_2\). Hence some \(t\in(0,1]\) gives area \(c_2\). The forms \(\ell_1,t\ell_2,-\ell_1-t\ell_2\) are nonzero, pairwise nonparallel, and sum to zero. Apply `851e063a1b9908a3` to the body \(K-z\) and these forms, with its total area \(A=|K|\) and its cap triple \((b_1,b_2,b_3)=(c_1,c_2,c_2)\). Since the minimum cap is \(c_2\), its inequality gives \(5(c_1+2c_2)-6c_2\ge4|K|\), or \(5c_1+4c_2\ge4|K|\). Thus \(h\ge0\) in all cases.

Because (N) has been proved, accepted fact `cddd2c95c0ff12e3` gives (1) for every nondegenerate triangle. At this invocation its planar total-area symbol \(a_1\) means \(|K|\); its \(c_j,s_3,h\) have exactly the meanings just defined. Its natural parameters \(\rho,\sigma\) are vertex extension factors and \(a,b\) are line parameters, with the same meanings as in `9414163c0331b8f2`; they are not the slice areas \(a_i\). In particular, its lines \(x\le-a y/(1-a)\) and \(x\ge b y/(1-b)\) are precisely the halfplanes \(Q_L,Q_R\) of that fact, because \(1-a,1-b>0\).

The area normalization in this triangle implication is common to all its areas. If \(\tau>0\) is the area of the minimized third cap, then the normalized total is \(|K|/\tau=\rho\sigma\), the normalized first two caps are \(c_1/\tau,c_2/\tau\), the normalized singleton is \(s_3/\tau\), the normalized overlap is \(|K\cap Q_1\cap Q_2|/\tau\), and the normalized radical argument is \(h/\tau\). In that geometry \(C_L,C_R\) are the first two normalized caps, possibly interchanged, and \(D_3\) is the normalized overlap; the minimized third cap has area one. Reflection interchanges \((\rho,\sigma,a,b,C_L,C_R)\) with \((\sigma,\rho,b,a,C_R,C_L)\), preserving both cap floors and the strict pair sum. Consequently the cap order required in (N) matches exactly. The conclusion of `cddd2c95c0ff12e3` already undoes this common normalization: both sides of (1) scale linearly with planar area. Its accepted implication covers all triangle configurations, including side hits and limiting extension factors equal to one, so no restriction from the natural domain remains in its triangle conclusion.

For general \(K\), apply accepted fact `c4077ad10a0441a5` with its planar \(a_1=|K|\), its scalar \(u=h\), and unchanged \(z,Q_j,c_j,s_3\). It proves (1) if \(c_1+c_2\ge|K|\). Otherwise the cap ordering implies \(c_i+c_j<|K|\) for every distinct pair. That fact therefore supplies a nondegenerate triangle \(\Delta\) with \(z\in\operatorname{int}\Delta\), the same total area and each of the same three cap areas, and \(|\Delta\setminus(Q_1\cup Q_2)|\ge s_3\). The halfplanes and their oriented normals have not changed. Applying the triangle conclusion to \(\Delta\) gives
\[
4s_3\le4|\Delta\setminus(Q_1\cup Q_2)|
\le\left(\frac32\sqrt{c_1}+\sqrt h\right)^2,
\]
because \(|\Delta|=|K|\) preserves \(h\). This proves (1) with all the required planar quantifiers.

We have now proved exactly the planar hypothesis of accepted fact `30d5406c9459a845`: the body, interior point, closed halfplanes, normal conditions, cap ordering, singleton area, and radical all match. Apply that implication to the compact polytope \(C\) in the statement, retaining its original \(A_i,a_i,T,S,h_S\) without any normalization. Its hypotheses require precisely these three nonempty two-dimensional slices, and its conclusion supplies \(y^*\in S\) with \(h_S(y^*)\ge2T/9\). By the stated definition of depth, every closed halfspace containing this same point has slice-area sum at least \(2T/9\). This proves the assertion for every polytope in the locked problem.

## External sources

none
