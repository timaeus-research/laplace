## Overall verdict

**The three headlines are faithful with caveats.** The kernel identification, leading coefficient, phase shift, and three modes of MGF convergence match the intended normal-crossing model. There is no missing factor of two or prior-normalisation constant.

The main issues are in the statistical interpretation and mirror wording:

1. The Lean theorems allow **signed continuous weights**, not just prior densities.
2. The formal conclusions concern **MGFs at each fixed real \(\theta\)**, not convergence of posterior probability measures.
3. The mirror’s **\(O(1/\log n)\)** claim is not established by these statements and is not justified under their general hypotheses.
4. “Unconditional” needs to distinguish XX, which assumes phase convergence, from XX′ and XX″, which do not.

| Headline | Verdict | Scope actually established |
|---|---|---|
| XX — `ncFluctMGF_tendsto` | **Faithful with caveats** | Deterministic, fixed-\(\theta\) MGF limit along any data array with \(Z_n\to z\). |
| XX′ — `ncFluctMGF_tendstoInMeasure` | **Faithful with caveats** | Fixed-\(\theta\) Gaussian-MGF approximation in probability under iid standard-normal data; no phase-convergence assumption. |
| XX″ — `ncFluctMGF_tendstoInDistribution` | **Faithful with caveats** | Convergence in distribution of the scalar posterior MGF evaluation to \(e^{Z\theta+\theta^2/2}\). |

These verdicts concern the supplied statements and their interpretation, not a re-verification of the proofs.

## 1. Definitions and posterior normalisation

### The model identification is correct

Writing \(t=x_0x_1\), the single-observation likelihood ratio is
\[
\frac{\phi(y-t)}{\phi(y)}=\exp(yt-t^2/2).
\]
Consequently,
\[
L_n(x;y)=L_n(0;y)\exp\!\left(-nt^2/2+t\sum_{i<n}y_i\right).
\]

The definitions implement precisely this:

- `ncLikelihood`: product of the \(N(x_0x_1,1)\) densities.
- `ncPhase`: \(Z_n=(\sum_{i<n}y_i)/\sqrt n\).
- `ncKernel`: \(\exp(-N^2t^2/2+Nzt)\).
- `ncPosteriorMean`: likelihood-weighted numerator divided by likelihood-weighted evidence, integrated against Lebesgue measure on `symBox 2`.
- `ncFluctMGF`: that quotient for \(\varphi(x)=e^{\theta\sqrt n\,t}\).
- `ncPhaseRV`: the same \(Z_n\), formed from the first \(n\) observations of one random sequence.

Thus the paper’s **dressed phase is \(2Z_n\)** at \(\beta=1/2\). The Gaussian posterior centre is \(Z_n\), not \(2Z_n\). “Centred at the empirical phase” should preferably say “centred at the empirical score \(Z_n\)” to avoid this terminology ambiguity.

### No missing normalisation factor

`ncPosteriorMean` initially uses the full likelihood, rather than the truth-normalised likelihood. `ncPosteriorMean_eq` gives the exact cancellation of the strictly positive truth likelihood. This is faithful to the intended posterior expectation.

The prior need not integrate to one: multiplying \(\rho\) by a positive constant leaves the quotient unchanged. A nonnegative, nonzero, finite prior weight defines the same posterior as its normalisation.

### Signed weights are the important caveat

The hypotheses are
```lean
Continuous ρ
0 < ρ 0
```
with no nonnegativity condition on the box. Accordingly, the theorems establish a stronger **analytic quotient result**, but not every permitted \(\rho\) defines a posterior probability distribution.

For a genuine prior, it is enough to require
\[
\rho\ge 0\quad\text{on the box},\qquad \rho(0)>0.
\]
Strict positivity everywhere is unnecessary. Continuity gives a positive lower bound on a neighbourhood of the origin; the Gaussian likelihood is positive everywhere. Hence the evidence is strictly positive for every finite data set, and finite because the weight and likelihood are bounded on the closed box.

For signed \(\rho\):

- finite-\(n\) evidence can vanish;
- Lean’s division then returns zero;
- even positive evidence does not turn a signed density into a probability density;
- the positive leading coefficient ensures eventual positive evidence along the phase-convergent sequences in XX;
- compact-uniform convergence ensures eventual positivity uniformly over bounded phase sets, and hence positivity with probability tending to one in the random setting.

Totalised division therefore does **not invalidate the asymptotic quotient theorem**, but it does require qualification of the phrase “posterior expectation.”

Also, `ncPosteriorMean` is defined for arbitrary \(\varphi\), without an integrability hypothesis. Its expectation interpretation requires integrability. This is automatic for the MGF observable under the stated continuity and genuine-prior conditions.

### Continuity is slightly stronger than the prose suggests

Lean assumes that \(\rho:\mathbb R^2\to\mathbb R\) is globally continuous. In particular, its restriction extends continuously to the **closed** box.

Mere continuity on the half-open box \((-1,1]^2\) is weaker and does not ensure boundedness near its excluded boundary. Paper-facing wording should say, for example:

> a nonnegative prior weight \(\rho\) extending continuously to \([-1,1]^2\), with \(\rho(0)>0\)

or simply state the global continuity assumption used in Lean.

## 2. Constants and the predicted limit

Here
\[
\lambda=\frac12,\qquad p=1,\qquad m=2,
\]
so
\[
\operatorname{leadScale}=N^{-1}\log N.
\]

Each quadrant contributes one half-line moment with phase \(2z\) or \(-2z\). There are two quadrants of each sign, and all reflected prior values at the origin equal \(\rho(0)\). Therefore the coefficient is
\[
2\rho(0)\bigl[J_1(2z)+J_1(-2z)\bigr].
\]

At \(\beta=1/2\),
\[
J_1(2z)+J_1(-2z)
=\int_{\mathbb R}e^{-s^2/2+zs}\,ds
=\sqrt{2\pi}\,e^{z^2/2}.
\]
Thus
\[
I_N(z):=\int_{(-1,1]^2}\rho(x)K_{N,z}(x)\,dx
\sim
2\rho(0)\sqrt{2\pi}e^{z^2/2}\frac{\log N}{N}.
\]

The factorial in `phaseCoeff_equal` is \(1!\) in ambient dimension two, not \(2!\). There is no missing multiplicity factor.

The tilt identity gives
\[
M_N(z,\theta)=\frac{I_N(z+\theta)}{I_N(z)}
\longrightarrow
\exp\!\left(\frac{(z+\theta)^2-z^2}{2}\right)
=e^{z\theta+\theta^2/2}.
\]
This is exactly the MGF of \(N(z,1)\).

In the paper’s sample-size convention,
\[
2\frac{\log N}{N}=\frac{\log n}{\sqrt n}.
\]
This accounts for the apparent factor-of-two change when writing the evidence asymptotic directly in \(n\).

### Independent product-coordinate check

For constant weight \(1\), the pushforward of box Lebesgue measure under \(t=x_0x_1\) has density
\[
2\log(1/|t|),\qquad 0<|t|<1.
\]
Setting \(s=Nt\) independently reproduces the coefficient above.

For the supplied polynomial weight,
\[
\rho(x)=1+0.3x_0+0.2x_1^2,
\]
the corresponding product-coordinate density is
\[
w(t)=2\log(1/|t|)+0.2(1-t^2).
\]
The odd term cancels by the symmetry \(x\mapsto-x\). Thus
\[
I_N(z)=\frac1N\int_{-N}^{N}
\left[2\log N-2\log|s|+0.2(1-s^2/N^2)\right]
e^{-s^2/2+zs}\,ds.
\]
This explains inverse-logarithmic corrections for this particular smooth example.

The target is indeed \(e^{0.475}\approx1.608014\). The supplied numerical gaps times \(\log n\) are approximately \(0.93,1.01,1.05,0.90\): consistent with the claimed numerical scale. I have not independently rerun the quadrature.

## 3. What the MGF statements justify

The precise formal conclusion is:

> For every fixed real \(\theta\), the posterior MGF is asymptotically equal to the MGF of \(N(Z_n,1)\), deterministically along convergent phase sequences or in probability under the truth.

It is reasonable to call this a **Gaussian posterior approximation at the level of fixed-argument MGFs**.

For genuine posterior probability measures, deterministic MGF convergence for all \(\theta\) does imply weak convergence to \(N(z,1)\) by a standard MGF continuity theorem. Thus the interpretation is mathematically well motivated. But that implication is not formalised here, and the random-centre formulation additionally needs an explicitly chosen mode of convergence for random posterior measures.

Consequently, avoid presenting

> “the posterior law is asymptotically \(N(Z_n,1)\)”

as the literal Lean theorem. Prefer:

> “For each fixed \(\theta\), its posterior MGF is asymptotically that of \(N(Z_n,1)\); weak convergence of posterior measures is not asserted here.”

Similarly, “the fluctuation phenomenon realised” is fair **at the level of these posterior MGF evaluations**. XX″ does not assert convergence of the entire random MGF function or of a random posterior measure.

## 4. Should-fix items

1. **Separate analytic weights from statistical priors.**  
   Keep the stronger signed-weight theorems, but document that the posterior interpretation additionally requires nonnegativity on the box. A wrapper theorem with this assumption and a finite-sample evidence-positivity lemma would make the success claim particularly clean.

2. **Remove the general \(O(1/\log n)\) assertion.**  
   None of the headline statements gives a rate. Mere continuity does not justify this rate: continuous weights with slowly decaying oscillations as functions of \(x_0x_1\) can generate larger errors. Moreover, comparison with a fixed \(z\) also inherits the unspecified rate of \(Z_n\to z\). The polynomial numerical example may be described separately as exhibiting inverse-logarithmic corrections.

3. **Qualify the posterior-law wording** as fixed-\(\theta\) MGF approximation.

4. **Replace “unconditional” with “no unresolved geometric or empirical-process assumptions.”**  
   XX explicitly assumes \(Z_n\to z\). XX′ and XX″ eliminate that assumption under the stated iid truth model. Typical iid Gaussian data should not be portrayed as discharging XX through sample-path convergence of \(Z_n\).

5. **Correct “variance 1 for every \(n\)” to “for every \(n\ge1\).”**  
   At \(n=0\), `ncPhaseRV` is identically zero.

6. **Distinguish proof inputs from theorem hypotheses.**  
   XX′ is stated with Gaussian marginal laws and full `iIndepFun`. Its probabilistic argument needs only centred unit-variance data with suitable pairwise independence; second moments alone are not the whole assumption. Suggested wording:
   > “The tightness argument uses only the zero means, unit variances, and pairwise independence implied by these hypotheses.”

   Exact Gaussianity of \(Z_n\), and thus XX″’s specified limiting law, uses the stronger Gaussian independence assumptions.

7. **State the boundary regularity accurately**, as discussed above.

The iid encoding itself is standard: `HasLaw` supplies the common Gaussian marginal law and a.e. measurability; `iIndepFun` supplies mutual independence. The XX″ limit function on \((\mathbb R,\mathrm{gaussianReal}\ 0\ 1)\) is exactly the right way to express \(e^{Z\theta+\theta^2/2}\). It does not require constructing \(Z\) on the original data space.

The conditions \(n>0\) and eventually \(\sqrt n>1\) are harmless: they enable division by \(\sqrt n\) and cancellation of the positive leading scale. They impose no substantive asymptotic restriction.

## 5. Suggested replacement for the central mirror claims

> For a nonnegative prior weight \(\rho\) extending continuously to the closed box, with \(\rho(0)>0\), the likelihood ratio is exactly the stated normal-crossing kernel. For each fixed \(\theta\), if \(Z_n\to z\) along a data sequence, the posterior MGF of \(\sqrt n\,x_0x_1\) converges to \(e^{z\theta+\theta^2/2}\) [ncFluctMGF_tendsto]. This is a Gaussian posterior approximation at the level of fixed-argument MGFs; no rate or posterior-measure convergence is asserted here.
>
> No chart-decomposition or likelihood-remainder hypothesis remains to be supplied. Under iid \(N(0,1)\) data, no phase-convergence assumption is required: compact-uniform convergence in the phase and tightness of \(Z_n\) give the MGF approximation in probability [ncFluctMGF_tendstoInMeasure]. Since \(Z_n\) is exactly standard normal for every \(n\ge1\), each fixed-\(\theta\) posterior MGF evaluation converges in distribution to \(e^{Z\theta+\theta^2/2}\), \(Z\sim N(0,1)\) [ncFluctMGF_tendstoInDistribution].

## 6. Astra #24 success gate

**Yes, substantively the example closes the stated gate.**

The observable is defined using the **actual full likelihood and its normalising evidence**, not merely an abstract chart surrogate. XX′ and XX″ are named theorems about that observable with no chart-decomposition, likelihood-remainder, or empirical-phase-convergence hypothesis left to discharge.

The qualification is semantic but important: this is an actual normalised posterior **when \(\rho\) is a genuine nonnegative prior weight**. The more general signed-weight instances are analytic extensions, not statistical posteriors. Clarifying that restriction—and deleting the unsupported rate and unqualified posterior-law claims—would make the paper-facing success statement accurate without changing the headline limits.
