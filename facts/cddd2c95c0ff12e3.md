---
fact_id: cddd2c95c0ff12e3
kind: lemma
author: "r133_triangle_product"
assurance: LLM-verified
subgoal_id: r133-triangle-sector-product-proof
depends_on: ["64760c76cadff481","851e063a1b9908a3"]
source_packet_sha256: f94eb5e343bfc523b04fb4793daf8b28515e96fe2436ac1df6e14904c8137a34
verifier_run: 235ff6cbeefb47b9
target_match: null
---

## Statement

Consider the following assertion about four real parameters, called (N). For every \(\rho,\sigma>1\) and \(0<a,b<1\) satisfying
\[
a(2\sigma-1)\le\sigma,\qquad b(2\rho-1)\le\rho,
\]
define
\[
\begin{aligned}
H&=2\rho\sigma-\rho-\sigma,&
X&=\rho+\sigma-2\sigma a,&
Y&=\rho+\sigma-2\rho b,\\
C_L&=\frac{\sigma(\rho-a)^2}{X},&
C_R&=\frac{\rho(\sigma-b)^2}{Y},&
D_3&=\frac{H^2(a+b-2ab)}{2XY}.
\end{aligned}
\]
The assertion (N) is
\[
C_L\ge C_R\ge1,\qquad C_L+C_R<\rho\sigma
\quad\Longrightarrow\quad
\left(\frac{a+b}{2}\right)^2\le C_LD_3.                 \tag{N}
\]
All its displayed denominators are positive under the stated parameter constraints.

If (N) is true, then every nondegenerate triangle \(K\), every \(z\in\operatorname{int}K\), and every three closed halfplanes \(Q_1,Q_2,Q_3\) with concurrent, pairwise nonparallel boundary lines through \(z\) and strictly positively dependent oriented normals have the following property. With
\[
a_1=|K|,\qquad c_i=|K\cap Q_i|,\qquad
c_1\ge c_2\ge c_3,\qquad
s_3=|K\setminus(Q_1\cup Q_2)|,
\]
one has \(h=5c_1/4+c_2-a_1\ge0\) and
\[
4s_3\le\left(\frac32\sqrt{c_1}+\sqrt h\right)^2.       \tag{1}
\]
Equivalently, any triangle violating (1) yields parameters satisfying every hypothesis of (N) and its strict opposite inequality.

The local parameters \(\rho,\sigma\) are vertex extension factors, not endpoint area ratios. The parameters \(a,b\) are line parameters. In the proof, \(C_L,C_R\) are the two caps \(c_1,c_2\), possibly interchanged, after one explicitly stated common area normalization. The symbols \(s_3,D_3,a_1\) keep their geometric meanings under that same normalization. Accepted fact 64760c76cadff481 is used only for its elementary triangular-cap area formula; none of its matrix or endpoint-area notation is reused. Accepted fact 851e063a1b9908a3 is used with the exact area and cap aliases specified below.

## Proof

First we establish \(h\ge0\), independently of (N). If \(c_1+c_2\ge a_1\), then \(h\ge c_1/4\). Otherwise orient defining forms so that \(Q_i=\{\ell_i\le0\}\) and positively rescale them to satisfy \(\ell_1+\ell_2+\ell_3=0\). The halfplanes
\[
\{\ell_1+t\ell_2\ge0\},\qquad 0\le t\le1,
\]
have continuously varying cap areas. The area at \(t=1\) is \(c_3\le c_2\), whereas the area at \(t=0\) is \(a_1-c_1>c_2\). Some \(t\in(0,1]\) therefore gives cap area \(c_2\). Its defining forms \(\ell_1,t\ell_2,-\ell_1-t\ell_2\) are pairwise nonparallel and sum to zero. Apply accepted fact 851e063a1b9908a3 with its total area \(A=a_1\) and cap triple \((b_1,b_2,b_3)=(c_1,c_2,c_2)\). It gives \(5c_1+4c_2\ge4a_1\), which is \(h\ge0\).

The complement of \(Q_1\cup Q_2\) is contained in \(Q_3\) up to null boundary lines, so \(s_3\le c_3\le c_1\). Consequently, if \(c_1+c_2\ge a_1\), then \(h\ge c_1/4\) proves (1) immediately. We henceforth assume \(c_1+c_2<a_1\).

We replace only the third cut. Its normal is allowed to vary over the closed positive-balancing arc determined by the first two cuts. In form coordinates this arc consists of \(\{(1-t)\ell_1+t\ell_2\ge0\}\), \(0\le t\le1\). Its endpoint cap areas are \(a_1-c_1\) and \(a_1-c_2\), both strictly greater than \(c_2\). The original third cap is an interior member of this arc and has area at most \(c_2\). Thus a minimum cap on this compact arc occurs in its interior. The new third cap has positive area, at most \(c_2\), and leaves \(a_1,c_1,c_2,s_3,D_3,h\) unchanged, where
\[
D_3=|K\cap Q_1\cap Q_2|=s_3-a_1+c_1+c_2.             \tag{2}
\]

Its full chord is bisected by \(z\). To see this including a line through a vertex, translate \(z\) to the origin and write the area of a rotating cap as the integral of one half of the squared radial function over a semicircle of directions. The radial function is positive and continuous because the origin is interior to the triangle. Differentiating the two moving integration endpoints gives one half of the difference of the squared lengths of the two chord radii. The cap-area function is continuously differentiable even when a chord endpoint passes a triangle vertex. At its interior minimum the two radii therefore have equal lengths.

Moreover the minimizing cap is triangular. If its boundary avoids all vertices but the cap contains two vertices, its complement is a vertex triangle. In affine coordinates on the two incident edges of that complementary vertex, let the fixed point have coordinates \((x,y)\), with \(x,y>0\). A cutting line with edge intercepts \(p,q>0\) satisfies \(x/p+y/q=1\), and the complementary cap area is a fixed positive multiple of
\[
pq=\frac{yp^2}{p-x}.
\]
Its derivative vanishes only at \(p=2x\), where it has a strict local minimum. Thus the two-vertex cap has a strict local maximum there, contradicting minimization. If the minimizing line passes a vertex, either side of the cut is itself a triangle, and the minimizing side is still a triangular cap with one original vertex strictly on its side. Its other original vertex on the cutting line causes only the endpoint case treated below.

Apply an invertible affine map taking \(z\) to \((0,0)\), the two chord endpoints to \((-1,0),(1,0)\), and the vertex of this triangular cap to \((0,1)\). All areas in the rest of the normalized argument are the original areas divided by the area of the minimized third cap. In particular that cap has area \(1\). We reuse the geometric area symbols under this common normalization. The triangle is
\[
K=\operatorname{conv}\{(0,1),(-\rho,1-\rho),(\sigma,1-\sigma)\},
\qquad \rho,\sigma\ge1,
\qquad a_1=\rho\sigma.                              \tag{3}
\]
For any \(\rho,\sigma>1\), the origin has positive barycentric coefficients \(1/(2\rho)\) and \(1/(2\sigma)\) at the two lower vertices, and coefficient \(1-1/(2\rho)-1/(2\sigma)\) at the upper vertex. Thus all triangles with these strict extension factors contain the origin in their interiors. If the third chord contains no original vertex, then \(\rho,\sigma>1\). The case of equality in one extension factor will follow by continuity. The two remaining oriented cuts, after possibly interchanging them, have the form
\[
Q_L=\{x\le\lambda y\},\qquad Q_R=\{x\ge\mu y\},
\qquad \lambda<\mu.
\]
Indeed, positive balance with the third cut \(\{y\ge0\}\) makes the two horizontal coefficients have opposite signs and makes \(\mu-\lambda>0\). Their areas satisfy \(C_L,C_R\ge1\), and \(c_1=\max(C_L,C_R)\), \(c_2=\min(C_L,C_R)\).

The upper cap is the triangle \(0\le y\le1\), \(|x|\le1-y\). Its area to the left of the line \(x=t y\) is
\[
\mathcal P(t)=
\begin{cases}
1/[2(1-t)],&t\le0,\\
1-1/[2(1+t)],&t\ge0.
\end{cases}                                        \tag{4}
\]
These expressions follow by the two edge-intercept products in accepted fact 64760c76cadff481. Also \(s_3=\mathcal P(\mu)-\mathcal P(\lambda)\). If both slopes have the same sign, or either slope is zero without strict signs on both sides, then \(s_3\le1/2\). Since \(c_1\ge1\) and \(h\ge0\), the right side of (1) divided by four is at least \(9/16>1/2\). Thus these cases satisfy (1).

It remains to prove the product inequality when \(\lambda<0<\mu\). Set
\[
\lambda=-\frac{a}{1-a},\qquad \mu=\frac{b}{1-b},
\qquad 0<a,b<1.
\]
Then (4) gives \(s_3=(a+b)/2\). We now prove, assuming (N), that
\[
\max(C_L,C_R)D_3\ge s_3^2                            \tag{5}
\]
for every such normalized triangle with \(C_L,C_R\ge1\) and \(C_L+C_R<a_1\). This strict pair sum is inherited from the original cuts and was not changed by minimizing the third cap.

First suppose \(\rho,\sigma>1\). The lower ray of the left line meets the base between the two lower vertices exactly when \(a(2\sigma-1)\le\sigma\). The analogous condition for the right line is \(b(2\rho-1)\le\rho\). These statements follow by evaluating \(x-\lambda y\) at \((\sigma,1-\sigma)\), and \(x-\mu y\) at \((-\rho,1-\rho)\), respectively.

If both rays meet the base, the triangular-cap formulas give exactly \(C_L,C_R\) in (N). For example, the left cap's two intercept fractions at \((-\rho,1-\rho)\) give \(C_L=\sigma(\rho-a)^2/X\). To verify the overlap formula directly, the base has equation
\[
(\sigma-\rho)x+(\rho+\sigma)y=-H.
\]
Reflect its lower portion in the origin. The radial endpoint at slope \(t=x/y\) then has height \(H/[\rho+\sigma+(\sigma-\rho)t]\). Integrating one half of its squared height from \(\lambda\) to \(\mu\) gives \(D_3=H^2(a+b-2ab)/(2XY)\). The same expression follows by the area of the triangle between the two lower rays and the base. Positivity of \(X,Y\) follows, for example, from \(X\ge\rho-\sigma/(2\sigma-1)>0\), and the symmetric inequality for \(Y\). If \(C_R>C_L\), reflection \(x\mapsto-x\) interchanges \((\rho,\sigma,a,b,C_L,C_R)\) with \((\sigma,\rho,b,a,C_R,C_L)\). The cap floors and the inherited strict pair sum are preserved by this reflection. Consequently (N) proves (5) for either cap order, including base-vertex hits.

For the remaining cases define \(R(t)=t^2/(2t-1)\) for \(1/2<t<1\). Its useful identities are
\[
R(t)-1=\frac{(1-t)^2}{2t-1},\qquad
R'(t)<0,\qquad R''(t)=\frac{2}{(2t-1)^3}>0.          \tag{6}
\]
If the left lower ray meets a side beyond the right lower vertex, then \(a>1/2\), \(\sigma\ge a/(2a-1)\), and the complement of \(Q_L\) is the vertex triangle at \((0,1)\) of area \(R(a)\). Hence
\[
C_L=a_1-R(a),\qquad D_3=C_R-R(a)+s_3.               \tag{7}
\]
The symmetric statement holds for the right ray. Formulas (7) remain valid at the corresponding base-vertex equality.

We first dispose of the case where both lower rays meet sides. Reflection permits us to assume \(C_L\ge C_R\). Then
\[
a\ge b>1/2,\qquad
C_L=a_1-R(a),\quad C_R=a_1-R(b),\quad
D_3=a_1-R(a)-R(b)+s_3.
\]
The side-hit conditions and cap floor imply
\[
a_1\ge\frac{ab}{(2a-1)(2b-1)},\qquad
a_1\ge1+R(b).                                     \tag{8}
\]
Here the strict pair sum is \(a_1<R(a)+R(b)\). Decreasing \(a_1\) preserves this strict inequality. For fixed \(a,b\), the product \(C_LD_3\) is increasing in \(a_1\) wherever \(C_L,D_3>0\), since its derivative is \(C_L+D_3\). We may therefore take \(a_1\) to be the larger of the two lower bounds in (8). These endpoint expressions are geometrically feasible: extension factors satisfying the two side-hit lower bounds and prescribed product exist precisely when the first bound in (8) holds. Thus \(D_3>0\) throughout the comparison.

If the first bound in (8) is larger, set \(\rho=b/(2b-1)\), \(\sigma=a/(2a-1)\). Both rays then meet base vertices. The cap floor follows from the assumed order of the two bounds, and the strict pair sum follows from the preceding monotonicity observation. Thus (N) applies. If the second bound is larger, then \(C_R=1\), \(C_L=1+R(b)-R(a)\ge1\), and \(D_3=1-R(a)+s_3\). The dominance of that second bound says
\[
a\ge p(b),\qquad
p(t)=\frac{t^2+2t-1}{(2t-1)(t+2)}.
\]
Direct differentiation gives \(p'(t)=-(t^2+1)/[(2t-1)^2(t+2)^2]<0\). Since \(a\ge b\), it follows that \(a\ge p(a)\), or \(2a^3+2a^2-4a+1\ge0\). The latter cubic is convex on \([1/2,3/4]\) and has endpoint values \(-1/4\) and \(-1/32\). It is therefore strictly negative throughout that interval. Thus \(a>3/4>1/\sqrt2\). As \(1/2<s_3\le a\),
\[
s_3(1-s_3)\ge a(1-a)\ge\frac{(1-a)^2}{2a-1}=R(a)-1.
\]
Hence \(D_3\ge s_3^2\), which proves (5) because \(C_L\ge1\). This completes both-side hits.

We next prove an endpoint fact for one side hit. Suppose the left ray meets a side, the right ray meets the base, and \(C_L=C_R=1\). Put \(a_1=1+R(a)\). The side-hit condition gives
\[
\rho=\frac{a_1}{\sigma}\le t_0:=a+2-\frac1a.
\]
In particular \(t_0\ge\rho>1\). The right cap, expressed using \(\rho\), is
\[
C_R=\frac{(a_1-\rho b)^2}{a_1+\rho^2(1-2b)}.
\]
The denominator is positive in the base-hit case. The exact identity
\[
C_R-\left(\frac{2a_1}{\rho}-\frac{a_1}{\rho^2}-1\right)
=\frac{(-a_1+a_1\rho-\rho^2+b\rho^2)^2}
{\rho^2[a_1+\rho^2(1-2b)]}\ge0                       \tag{9}
\]
is also the elementary minimum formula for a vertex cap. The expression in parentheses decreases for \(\rho\ge1\), its derivative being \(-2a_1(\rho-1)/\rho^3\). Therefore \(C_R=1\) and \(\rho\le t_0\) imply
\[
0\ge\frac{2a_1}{t_0}-\frac{a_1}{t_0^2}-2
=\frac{2-2a-a^2}{a^2+2a-1}.
\]
The denominator is positive because \(t_0>1\). It follows that \(a\ge\sqrt3-1>1/\sqrt2\), and also \(a>2/3\).

The equation \(C_R=1\), now expressed using \(\sigma\), is
\[
R(a)\sigma^2-2a_1b\sigma+a_1(b^2+2b-1)=0.
\]
Its discriminant is \(4a_1[b^2+R(a)(1-2b)]\ge0\). If \(b>1/2\), this gives \(R(a)\le R(b)\), hence \(b\le a\) by (6). If \(b\le1/2\), then \(b<a\) immediately. Thus \(s_3\in[a/2,a]\). The concave function \(x(1-x)\) takes its minimum on this interval at \(x=a\), because
\[
\frac a2\left(1-\frac a2\right)-a(1-a)=\frac{a(3a-2)}4\ge0.
\]
Consequently \(s_3(1-s_3)\ge a(1-a)\ge R(a)-1\). Equation (7) now gives \(D_3\ge s_3^2\). This proves the product when both caps equal one in the one-side case.

Next suppose there is one left side hit and one right base hit, with \(C_L=1\), \(C_R\ge1\), and \(C_L+C_R<a_1\). By (7), the strict pair sum is precisely \(C_R<R(a)\). Keep \(a,b,a_1=1+R(a)\) fixed and vary \(\sigma\), setting \(\rho=a_1/\sigma\). Then
\[
C_R(\sigma)=\frac{a_1(\sigma-b)^2}{\sigma^2+a_1(1-2b)},
\quad
\frac{dC_R}{d\sigma}
=\frac{2a_1(\sigma-b)[a_1(1-2b)+b\sigma]}
{[\sigma^2+a_1(1-2b)]^2}\ge0.                        \tag{10}
\]
The last inequality is exactly the right base-hit condition \(b(2\rho-1)\le\rho\), rewritten as \(b\sigma\ge a_1(2b-1)\). Decrease \(\sigma\) until either \(C_R=1\), the left side hit becomes a base-vertex hit at \(\sigma=a/(2a-1)\), or the right base hit becomes a side hit at \(b\sigma=a_1(2b-1)\). One of these events must occur: the first geometric lower bound on \(\sigma\) is greater than one, and decreasing \(\sigma\) increases \(\rho\), so neither triangle degeneracy nor \(\rho=1\) obstructs the motion. If \(b\le1/2\), the second geometric event is absent, which does not affect the argument.

All intermediate triangles contain the origin in their interiors, so \(D_3>0\). By (10), decreasing \(\sigma\) decreases \(C_R\), and hence preserves the strict bound \(C_R<R(a)\). Thus every invocation of (N) or the previously proved both-side case at a stopping point retains its strict pair hypothesis. Along the motion \(s_3,R(a)\) are fixed, and \(C_R D_3=C_R(C_R-R(a)+s_3)\) increases with \(C_R\), since its derivative is \(C_R+D_3>0\). Thus it suffices to prove the product at the stopping point. The three respective stopping cases have already been proved: both caps equal one, both rays meet the base by (N), or both rays meet sides. Since \(C_L=1\le C_R\), this proves (5) on the entire one-side cap-floor family.

Finally consider an arbitrary one-left-side, one-right-base configuration with \(C_L,C_R\ge1\) and \(C_L+C_R<a_1\). Keep the triangle and \(b\) fixed and vary \(a\) up to its limiting value one. The left side-hit interval begins at \(a_0=\sigma/(2\sigma-1)\). Because \(C_L=a_1-R(a)\ge1\) and \(R(a)>1\), we have \(a_1>2\). There is a unique \(a_*\in(1/2,1)\) with \(R(a_*)=a_1-1\). Put \(a_{\min}=\max(a_0,a_*)\), which is no larger than the given \(a\). The strict pair sum is \(C_R<R(a)\). Since \(R\) is strictly decreasing as a function of \(a\), decreasing \(a\) increases \(R(a)\). Thus the strict inequality persists from the given value of \(a\) down to \(a_{\min}\). At \(a_{\min}\), either both rays meet the base with both caps at least one and strict pair sum, or the exterior cap is one and the same strict pair sum holds. In either event (5) is already proved with all required hypotheses.

Throughout \([a_{\min},1)\), \(C_L=a_1-R(a)\) increases, \(C_R\) is constant, \(s_3=(a+b)/2\) is affine, and \(D_3=C_R-R(a)+s_3>0\). At the limiting endpoint \(a=1\), the continuous formulas give
\[
C_L=a_1-1>1,\qquad
s_3=\frac{1+b}{2}\le1,\qquad
D_3=C_R-1+s_3\ge s_3.
\]
Thus the product with either cap factor is at least \(s_3^2\) at that endpoint. The following interpolation may pass beyond the strict-pair region, but it invokes (N) only at the lower endpoint and in the already proved cap-floor reduction. The endpoint at \(a=1\) uses only this direct estimate.

If \(C_L(a_{\min})\ge C_R\), then \(C_L\) remains the larger cap. The desired inequality is equivalent to
\[
a_1\ge F(a):=R(a)+\frac{s_3(a)^2}{D_3(a)}.
\]
This function is convex. Indeed, writing primes for derivatives in \(a\), direct differentiation, using \(s_3''=0\) and \(D_3''=-R''\), gives
\[
F''=R''\left(1+\frac{s_3^2}{D_3^2}\right)
+\frac{2(s_3'D_3-s_3D_3')^2}{D_3^3}\ge0.             \tag{11}
\]
Both endpoints satisfy \(F\le a_1\), so convexity gives the same inequality throughout the interval. If instead \(C_R\ge C_L(a_{\min})\), the function
\[
G(a)=C_R D_3(a)-s_3(a)^2
\]
is concave, with \(G''=-C_RR''-2(s_3')^2<0\). It is nonnegative at both endpoints, and hence throughout. Since the larger cap is always at least \(C_R\), this also proves (5), including a later reversal of cap order. Reflection treats one right side hit and one left base hit. This completes all opposite-sign cases for \(\rho,\sigma>1\).

If one of \(\rho,\sigma\) in (3) equals one, increase both extension factors by positive numbers tending to zero. These larger triangles contain the original triangle, retain the same upper triangular cap of area one, and preserve the lower bounds \(C_L,C_R\ge1\). Their upper singleton area is unchanged. The original strict gap \(a_1-C_L-C_R>0\) is also preserved for all sufficiently small such enlargements, by continuity of the total and cut areas. Apply the just-proved opposite-sign product inequality to those sufficiently small enlargements and pass to the limit by the same continuity. This handles a minimizing third chord passing through a triangle vertex. The same-sign estimate did not require strict extension factors. Equality of ray and base-vertex positions was included in the non-strict base-hit conditions and continuous formulas throughout.

We have therefore proved either (1) directly in the same-sign cases, or the product \(s_3^2\le c_1D_3\) in the opposite-sign cases. In the latter cases, (2) and completing the square give
\[
\left(s_3-\frac{c_1}{2}\right)^2\le c_1h,
\qquad
s_3\le\frac{c_1}{2}+\sqrt{c_1h}.
\]
The exact identity
\[
\frac14\left(\frac32\sqrt{c_1}+\sqrt h\right)^2
-\left(\frac{c_1}{2}+\sqrt{c_1h}\right)
=\frac{(\sqrt{c_1}-2\sqrt h)^2}{16}\ge0
\]
proves (1). Undoing the common affine area normalization preserves (1), since both sides scale linearly in area. The replacement of the third cap left every quantity in (1) unchanged, so (1) holds for the original cuts. This proves the conditional statement, and its contrapositive gives the asserted actual natural-cell product counterexample from any triangle violation of (1).

## External sources

None. All non-predecessor steps are proved above. The exact square identity (9), its substitution at \(t_0\), and \(R''\) were also checked by rational simplification in local Wolfram Language 14.3.0, WolframScript 1.13.0, with exact symbolic inputs and exit status zero; those checks are not used in place of the displayed algebraic proofs.
