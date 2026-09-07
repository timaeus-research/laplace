**Recommendation: proceed, but use R2 with recursively defined circle integrals—not R1’s holomorphy-under-the-integral lemma as the critical path.** Authorise a **10-unit capped tranche**, with a genuine two-coordinate gate after unit 3.

I cannot independently inspect #31 or the repository here; this recommendation uses the status and scouted facts in your message.

## 1. Lowest-risk route: R2, with recursive normalised contour operators

The key architectural choice is:

> Apply the dimension induction to slices of the original function, not to coefficient functions.

This avoids proving that parameter-dependent Cauchy coefficients are holomorphic. Continuity, integral bounds, and dominated interchange still need work, but they are necessary for either route and are quantitatively controlled.

I would initially avoid making `torusIntegral` the implementation interface. Define the iterated contour operator recursively along `Fin.cons`, then identify it with `torusIntegral` later if useful. This removes `TorusIntegrable` bookkeeping from the first gate without changing the mathematics.

### Normalise each contour integral

For \(r>0\), write
\[
A_r(g)=\frac1{2\pi i}\oint_{|w|=r}w^{-1}g(w)\,dw.
\]
The supplied circle-integral estimate gives
\[
\|A_r(g)\|\le C
\qquad\text{if }\|g(w)\|\le C\text{ on }|w|=r.
\]

Its recursive \(d\)-coordinate version \(A_r^{[d]}\) therefore satisfies the same bound on the distinguished boundary. Define
\[
c_\gamma
  =A_r^{[d]}\left(w\mapsto F(w)\prod_i w_i^{-\gamma_i}\right).
\]
Thus
\[
\|c_\gamma\|\le M r^{-|\gamma|}.
\]

This normalisation keeps the \(2\pi r\) cancellations out of subsequent proofs. Treat \(d=0\) as evaluation and the empty product explicitly.

### Prove the iterated Cauchy formula first

The useful intermediate theorem is
\[
F(z)=
A_r^{[d]}\left(
 w\mapsto F(w)\prod_i(1-z_i/w_i)^{-1}
\right),
\qquad |z_i|<r.
\]

Its induction uses:

1. the one-variable Cauchy formula in the first coordinate;
2. the induction hypothesis for the tail slice \(z'\mapsto F(w,z')\), with \(w\) on the contour;
3. continuity/integrability of the resulting expressions.

**No coefficient function is submitted to the analytic induction hypothesis.** If the recursive integration order is chosen to match this proof, no contour-order interchange is intrinsically necessary either.

Next expand the kernel:
\[
\prod_i(1-z_i/w_i)^{-1}
 =
\sum_{\gamma:\mathrm{Fin}\ d\to\mathbb N}
 \prod_i(z_i/w_i)^{\gamma_i}.
\]
The uniform majorant on the integration torus is
\[
M\prod_i q_i^{\gamma_i},
\qquad q_i=|z_i|/r<1,
\]
and
\[
\sum_\gamma M\prod_iq_i^{\gamma_i}
   =M\prod_i(1-q_i)^{-1}.
\]

That supplies dominated interchange and produces a **`HasSum` theorem**, not merely a `tsum` equality:
\[
\operatorname{HasSum}
 \left(\gamma\mapsto c_\gamma\prod_i z_i^{\gamma_i}\right)(F(z)).
\]

In Lean, I would permit the proof to perform these interchanges one coordinate at a time, using `Fin.consEquiv`. There is no need to force a single global multivariate sum/integral theorem.

### The weighted estimate is an explicit deliverable

For \(0\le b<r\),
\[
\sum_\gamma \|c_\gamma\|b^{|\gamma|}
 \le M(1-b/r)^{-d}.
\]

This is the bridge into the existing coefficient-family theorem. Do not leave it as an informal consequence of pointwise convergence.

## 2. Hypotheses, and what R1 actually needs

### Continuity and boundedness are not sufficient for R1’s IH

Your diagnosis is correct. If the IH is the analytic bridge, applying it to \(a_n\) requires analyticity of \(a_n\). Continuity and boundedness alone do not imply a power-series representation.

Changing the IH to separate holomorphy does not entirely remove the obligation: one must still prove that each \(a_n\) is separately holomorphic. That may reduce differentiation under the integral to a one-complex-dimensional parameter, but it remains a new analytic lemma.

### Use continuity plus coordinatewise disc holomorphy as the working hypothesis

For the contour proof, a convenient internal hypothesis is:

- \(F\) is continuous on the closed polydisc \(P_r\);
- for every coordinate, **with all other coordinates fixed anywhere in their closed discs**, the corresponding slice is holomorphic on the open disc of radius \(r\).

The quantification over boundary values of the other coordinates matters: the induction freezes coordinates on integration contours.

No Osgood theorem is needed. We never infer joint holomorphy from separate holomorphy; we only use the latter to invoke one-variable Cauchy formulas.

This working hypothesis is easy to supply from the paper:

1. choose
   \[
   \max(0,b)<r<R;
   \]
2. use \(P_r\subset D_R\);
3. obtain continuity on \(P_r\) from differentiability on the open set \(D_R\);
4. compose \(F\) with coordinate insertion maps to obtain holomorphic slices;
5. obtain a nonnegative uniform bound \(M\) by compactness of \(P_r\).

The external theorem should therefore accept the paper’s natural hypothesis
`DifferentiableOn ℂ F (openPolydisc R)`.
The separate-holomorphy interface can remain internal.

A small specification point: “holomorphic on the closed polydisc” is ambiguous mathematically. Do not base the final paper-facing API on that phrase. The larger open polydisc gives all required boundary regularity cleanly.

## 3. Unit plan and the go/no-go gate

Here is my proposed **10-unit cap**, with two checkpoints rather than an unconditional ten-unit commitment.

| Unit | Deliverable |
|---|---|
| 1 | Polydisc geometry, compactness/bounds, and the joint-holomorphy-to-slice adapter. |
| 2 | Normalised circle operator: linearity, norm bound, continuity for compact continuous parameter families, and a dominated-series interchange lemma. |
| 3 | **Two-coordinate quantitative gate:** extraction, coefficient bound, reconstruction, and product-geometric domination. |
| 4 | Recursive finite-dimensional contour operator; continuity and norm bound by dimension induction. |
| 5 | Iterated Cauchy representation under the internal slice hypothesis. |
| 6 | Multi-index geometric summability, kernel expansion, and reconstruction as `HasSum`. |
| 7 | Weighted coefficient mass bound at \(b<r\); package the holomorphic bridge. |
| 8 | Real-parts adapter and application to \(\xi,\eta\); connect to `thm_TaylorTree_coeffFamily`. |
| 9 | Slice coefficient uniqueness/derivative identification, reusing the one-variable pilot. |
| 10 | Multi-index derivative identification, final paper-facing statement, and review. |

This is a budget, not a claim that every row necessarily fits the project’s unit size.

### Gate after unit 3

The gate should contain, for a genuinely two-variable function,
\[
\|c_{m,n}\|\le Mr^{-(m+n)}
\]
and
\[
\operatorname{HasSum}_{(m,n)}
  \bigl(c_{m,n}z_0^m z_1^n\bigr)
  \bigl(F(z_0,z_1)\bigr),
\]
with the summable majorant
\[
M q_0^m q_1^n.
\]

It must also exercise **continuity of an inner contour integral in an outer parameter**, in a lemma general enough to reuse in the dimension induction.

A two-coordinate norm bound alone is **not** a pass. Nor is an iterated `tsum` identity with convergence obligations postponed.

**Go:** extraction and reconstruction compile using reusable contour-interface lemmas.

**No-go:** reconstruction still requires an unproved integral/sum interchange, or the proof depends on an ad hoc two-dimensional parameter argument that does not generalise.

On no-go, stop this tranche and report the precise missing lemma. Do not automatically launch R1 as a second open-ended investigation.

## 4. Identifying the derivatives

The target should be explicit about notation:
\[
\gamma!:=\prod_i(\gamma_i!),
\qquad
c_\gamma=\frac{\partial^\gamma F(0)}{\gamma!}.
\]

In particular, this is **not** a denominator of \(|\gamma|!\); that denominator belongs to a different homogeneous/multilinear-series normalisation.

### Recommended proof: coefficient uniqueness, coordinate by coordinate

Reuse the one-variable derivative identification rather than beginning with general multivariate Fréchet-series combinatorics.

Split the multi-index as \((n,\beta)\), and define
\[
H_n(z')=\sum_\beta c_{n,\beta}(z')^\beta.
\]
The quantitative bounds provide the convergence and regrouping needed for
\[
F(z_0,z')=\sum_n H_n(z')z_0^n.
\]

For fixed \(z'\), compare this series with the slice’s one-variable Cauchy series. Uniqueness and the pilot’s derivative formula give
\[
H_n(z')
 =\frac1{n!}
   \left.\frac{d^n}{dz_0^n}F(z_0,z')\right|_{z_0=0}.
\]

Now repeat in the remaining coordinates. This identifies \(c_\gamma\) with the corresponding successive coordinate derivatives divided by \(\gamma!\).

The important bookkeeping obligation is to carry the function identity on the remaining open polydisc, **not just at the origin**, so that subsequent coordinate derivatives can be taken. Existence of those successive derivatives follows from the remaining series and repeated one-variable identification. This avoids a standalone theorem differentiating the original contour integral in several parameters.

Define the initial mixed-partial operator in a fixed coordinate order. If the paper’s notation demands order independence, prove that separately or derive it by running the identification in another order; do not introduce derivative-commutation infrastructure prematurely.

### Is deferral acceptable?

**Yes as a milestone; no as an unqualified completion claim for the paper’s literal formula.**

After unit 8, it is legitimate to have:

- an analytic-input Taylor-tree theorem;
- coefficients given by explicit Cauchy integrals;
- coefficient representation and quantitative bounds;
- derivative notation still awaiting identification.

That is substantially stronger than R3: it genuinely derives coefficient-family data from the paper’s holomorphy hypothesis.

But uniqueness of the representing coefficients does not, by itself, discharge the formal derivative formula. Keep that obligation visible and do not label it already proved.

## 5. Continue or hand off?

**Continue now.** The remaining gap has a concrete mathematical reduction, the necessary one-variable infrastructure is present, and the standing instruction supports bounded autonomous implementation.

My instruction would be:

> Execute units 1–3 using recursive normalised circle integrals. Continue through unit 8 only if the quantitative two-coordinate reconstruction gate passes. Reserve units 9–10 for derivative notation and final review. Do not weaken holomorphy to an assumed convergent series, and do not exceed the ten-unit tranche silently.

If the quantitative bridge lands but derivative identification overruns, preserve it as a reviewed endpoint and hand off **that precise notation-identification gap**. The strategically important move now is to avoid making joint holomorphy of coefficient functions a prerequisite for the several-variable reconstruction.
