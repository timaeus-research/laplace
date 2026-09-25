## 1. Audit

**The normalization and density are consistent with the active-truth limit**, assuming the background data supplies \(q=q_k>0\) and \(\rho>0\).

The power simplifies to
\[
\lambda=\gamma p+\beta(1-\gamma\nu)-\eta\gamma
       =\beta+\gamma(p-\nu\beta-\eta).
\]
The log order is \(k\), the dimension of the free fibre.

Your constants give exactly
\[
A\,B^{-\beta}\,q\,D^{-q\eta}
=\frac{|\sigma|^p}{q}\,|\sigma|^{-\nu\beta}\,q\,|\sigma|^{-\eta}
=|\sigma|^{p-\nu\beta-\eta}.
\]
Thus the density can equivalently be written
\[
\Gamma(\beta)|\sigma|^{p-\nu\beta-\eta}\,\mathrm{faceConst}\,
u^{q\eta-1}\,
(\mathrm{wt}|b|)(\mathrm{bridgePt}(0,u))\,
|a(\mathrm{bridgePt}(0,u))|^{-\beta}.
\]
There is **no leftover \(q\)**. This is the \(I=\varnothing\) measure predicted by (LM).

It is **concentrated on the image of the open truth segment**. Its *topological support* is contained in the closure of that image, not necessarily in the open image. It is not generally a Dirac measure at `rep 0`.

For the certificate interface, check explicitly:

- **Finiteness:** bounded trace amplitude, a positive lower bound for \(|a|\), and \(q\eta>0\) give an integrable majorant \(C u^{q\eta-1}\).
- **Measurability of the pushforward map** and the density.
- Any support/localization condition actually required by `TermData`, beyond testing against observables supported in `L'`.

Nonnegativity follows from all the factors—not just \(A\)—using \(\Gamma(\beta)>0\), \(\mathrm{faceConst}\ge0\), and the existing weight sign assumptions. The clipped extension of \(|a|\) is harmless provided it agrees on the model domain and preserves the asserted trace.

## 2. Positive face and nonvanishing

**Your concern is correct, with an important distinction.**

A zero-measure term at a smaller \(\lambda\), or at the same \(\lambda\) with a larger \(k\), can dominate the bookkeeping and produce a **valid but zero global limit**. It does not invalidate the limit theorem; it invalidates interpreting the selected pair as the true leading order.

Also, **one cannot simply discard that term**: knowing
\[
t^\lambda(\log t)^{-k}K(t)\to0
\]
does not prove negligibility at the next candidate normalization.

Your proposed geometric lemma is right under the stated nondegeneracy:
\[
0<\operatorname{vol}(F')
\iff
\exists w,\quad
(\forall i,\;0<w_i)\ \land\
(\forall j,\;c_j\cdot w<a_j).
\]
Here the nondegeneracy is exactly what makes feasible boundary equalities lie in null sets. This also covers \(k=0\) with the usual zero-dimensional volume convention.

Through the solved-pair parametrization, the correct original-coordinate formulation is
\[
\exists\alpha,\quad
(\forall j,\;0<\alpha_j),\qquad
\kappa\cdot\alpha=\delta,\qquad Q\cdot\alpha=\gamma.
\]

**Recommendation:** retain the unrestricted analytic theorem; add a positive-face wrapper or a separate nonvanishing theorem.

But positive face volume alone does **not** ensure a nonzero chart measure. You additionally need
\[
(\mathrm{wt}|b|)(\mathrm{bridgePt}(0,u))>0
\]
on a set of positive \(u\)-measure. If the chart package already supplies this, discharge it there; otherwise make it explicit. For the restricted observable interface, the nonzero mass must also be detectable by the admissible observables in `L'`.

## 3. Ranking

1. **(a) Spectator traces and wrapper:** completes the generic active-truth analytic mechanism using machinery already available.
2. **(b) LP-to-chart interface:** turns the analytic theorem into a usable phase-data certificate and exposes exactly which geometric cases remain.
3. **(d) Example identification:** provides an end-to-end regression test of constants, normalization, and measure identification.
4. **(f) Moving parameter:** directly serves the stated parameter-stability results; pointwise-in-\(\sigma\) convergence alone will not suffice.
5. **(e) Identically active coordinate constraint:** needed for coverage when nondegeneracy fails; promote this immediately if the LP interface encounters such charts.
6. **(c) Solved-pair independence:** valuable API hygiene and a strong constant check, but not an obstacle to using one chosen pair.
7. **(g) General Hironaka export:** export once the supported cases and residual degeneracies have been made explicit.

### Statement I would write for (a)

Let
\[
R(y,u)=\operatorname{rep}(\operatorname{bridgePt}(y,0,u)),
\qquad
C=A\Gamma(\beta)B^{-\beta}qD^{-q\eta}\,\mathrm{faceConst},
\]
and let \(d_\ell>0\) be the **effective spectator exponents supplied by the spectator reduction**. Define
\[
\mu=
R_*\!\left[
C\,\mathbf1_{(0,\rho)^{m'}\times(0,\rho)}
\left(\prod_\ell y_\ell^{d_\ell-1}\right)
u^{q\eta-1}
(\mathrm{wt}|b|)(y,0,\pm u)
|a(y,0,\pm u)|^{-\beta}\,dy\,du
\right].
\]

Then, under the existing spectator geometric hypotheses, the uniform bounds, and the joint measurability/active-coordinate trace assumptions,
\[
t^{\gamma p+\beta\delta-\eta\gamma}(\log t)^{-k}
\,\mathrm{modelKernelOf}(t;\varphi)
\longrightarrow \int\varphi\,d\mu
\]
for the same admissible observables. Package this as `TermData.activeTruthSpectator`.

Prove the abstract spectator trace theorem first, then obtain this wrapper by substitution.

## 4. General spectator density

**Yes: no continuity in \(y\) is needed.** Your proposed limit is correct, multiplied by the same geometric/scale prefactor:
\[
C\int_{(0,\rho)^{m'}}
\left(\prod_\ell y_\ell^{d_\ell-1}\right)
\int_0^\rho
u^{q\eta-1}W_{\rm tr}(y,u)a_{\rm tr}(y,u)^{-\beta}\,du\,dy.
\]

Sufficient assumptions are:

- joint measurability of units and traces;
- active-coordinate trace convergence for almost every \(y\), for each \(u\in(0,\rho)\), matching the inner theorem;
- uniform \(0\le W\le W_*\) and \(a\ge a_->0\);
- the existing integrable spectator majorant.

Replacing `w₀` by `W_*` in `normalised_lintegral_le` is the right argument: the damping uses only \(a_-\), not regularity of the units.

One qualification: **the frozen-\(y\) domination must include any \(y\)-dependence of the monomial scale parameters**, not merely the units. Reuse the existing spectator majorant, including any logarithmic factors it contains. Strictly positive effective \(d_\ell\) also absorb fixed powers of \(|\log y_\ell|\).

Finally, put
\[
W_{\rm tr}(y,u)=
\varphi(R(y,u))(\mathrm{wt}|b|)(y,0,\pm u)
\]
only in the proof against \(\varphi\); the defining density of the certificate measure must remain independent of \(\varphi\).