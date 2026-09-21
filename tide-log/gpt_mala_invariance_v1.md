## 1. Mathematical check: A0–A4 are correct, with a few explicit hypotheses

### A1: the general ratio

Yes. Writing \(Q_M(x)=x^\top Mx\), the log ratio is
\[
-\tfrac12Q_P(y)-(x-Ay)^\top S(x-Ay)
+\tfrac12Q_P(x)+(y-Ax)^\top S(y-Ax).
\]
Assuming \(S^\top=S\), expansion gives
\[
Q_G(y)-Q_G(x)
+2x^\top SAy-2y^\top SAx,
\qquad
G=S-A^\top SA-\tfrac12P.
\]
The last two terms cancel when \(SA\) is symmetric. Thus the claimed ratio is correct.

**Symmetry of \(P\) is not needed for this algebraic identity.** It is needed for the intended precision-matrix interpretation and the MALA specialization below.

### A2: MALA

Interpret the scalar \(S\) as \((4h)^{-1}I\). For symmetric \(P\) and \(h\ne0\),
\[
A^\top SA
=\frac1{4h}(I-hP)^2
=\frac1{4h}I-\frac12P+\frac h4P^2,
\]
so
\[
G=-\frac h4P^2.
\]
Consequently,
\[
\alpha(x,y)
=\min\left(1,\exp\left[-\frac h4
\bigl(\|Py\|^2-\|Px\|^2\bigr)\right]\right).
\]
For an actual proposal distribution, require **\(h>0\)**.

### A3: pMALA

For symmetric \(P\), \(A=(1-h)I\), and \(S=P/(4h)\),
\[
G=\frac{1-(1-h)^2}{4h}P-\frac12P
=-\frac h4P.
\]
This is also correct. A normalizable, nondegenerate proposal requires **\(P\) positive definite and \(h>0\)**.

### A0: invariance

The proof is complete provided the hypotheses include:

- a σ-finite reference measure;
- a measurable, finite-valued, strictly positive target weight \(\pi\);
- a **jointly measurable**, finite-valued, strictly positive proposal weight \(q\);
- a common row integral
  \[
  \int q(x,y)\,d\mu(y)=Z,\qquad 0<Z<\infty.
  \]

Tonelli avoids needing separate integrability hypotheses on the accepted flux or the target. However, this should be phrased carefully:

> No additional integrability hypotheses are needed for invariance of the possibly infinite target measure.

To call the result an invariant **probability law**, you additionally need
\[
0<T:=\int\pi\,d\mu<\infty
\]
and normalize by \(T\). Positive-definite Gaussian targets satisfy this.

Translation invariance establishes **independence of \(x\)** of the proposal normalizer; it does not alone establish positivity or finiteness. Those come from the centered positive-definite Gaussian integral.

### A4: no ULA stability restriction

An important useful qualification: the corrected kernels have the target invariant for **every \(h>0\)**, assuming \(P\succ0\). There is no need for the ULA condition such as \(h<2/\lambda_{\max}(P)\). Large steps may have poor acceptance, but stationarity remains exact.

---

## 2. Lean formulation: start with the setwise formula, then package a kernel

Your proposed shape is sound. I would separate the definitions as follows, using `E` for the measurable set to avoid collision with the drift matrix `A`:
\[
\begin{aligned}
w(x,y)&=\operatorname{ofReal}(q(x,y)\alpha(x,y)),\\
b(x)&=\int^- y,\;w(x,y),\\
a(x)&=b(x)/Z,\\
K_{\mathrm{set}}(x,E)
&=\left(\int^- y\in E,\;w(x,y)\right)/Z
 +(1-a(x))\,\mathbf1_E(x).
\end{aligned}
\]

Prove these intermediate facts early:

1. \(0\le\alpha(x,y)\le1\);
2. \(w(x,y)\le\operatorname{ofReal}(q(x,y))\);
3. \(b(x)\le Z\);
4. \(a(x)\le1\);
5. \(a(x)+(1-a(x))=1\).

Explicitly keep `Z ≠ 0` and `Z ≠ ∞` available. Many useful ENNReal cancellation lemmas need precisely these conditions.

### Defining the constant

Avoid defining `Z` with an apparently free `x`. For the general theorem, pass `Z` and the hypothesis
```lean
∀ x, (∫⁻ y, ENNReal.ofReal (q x y) ∂μ) = Z
```
For Gaussian proposals, define it from the centered weight:
\[
Z_S=\int^- y,\operatorname{ofReal}(\exp(-y^\top Sy)).
\]
Then prove the row-integral identity by translation.

### ENNReal subtraction

The subtraction is safe **after** proving \(a(x)\le1\). Do not try to obtain invariance by subtracting an accepted mass from total target mass: that risks \(\infty-\infty\).

Instead, combine the accepted and rejected integrands:
\[
\pi(y)a(y)+\pi(y)(1-a(y))
=\pi(y)\bigl(a(y)+(1-a(y))\bigr)
=\pi(y).
\]
Here and below, the target factors in lintegrals are understood as `ofReal`.

### Should this be a `Kernel`?

I recommend:

1. prove the density/lintegral invariance theorem first;
2. package it into a `ProbabilityTheory.Kernel`;
3. prove the kernel is Markov and preserves the target measure.

At the measure level, the intended construction is simply
\[
K(x)=
\mu.\mathrm{withDensity}\bigl(y\mapsto w(x,y)/Z\bigr)
+(1-a(x))\,\delta_x.
\]
The setwise formula is then its evaluation on measurable sets.

This keeps the algebra and Tonelli proof independent of kernel API details while still delivering an actual sampler kernel. I would not make progress depend on the existence or exact signature of a `Kernel.withDensity` helper.

Also use fully explicit parentheses in the quadratic forms:
```lean
dotProduct x (P *ᵥ x)
```
rather than relying on precedence in a mixed `⬝ᵥ`/`*ᵥ` expression.

---

## 3. Tonelli and measurability: use the symmetric accepted flux

**Yes: rewrite to the minimum first.** This is the cleanest central lemma:
\[
\pi(x)q(x,y)\alpha(x,y)
=\min\{\pi(x)q(x,y),\pi(y)q(y,x)\}.
\]

Prove this over `ℝ`, using positivity of the denominator, and then transport it through `ENNReal.ofReal`. That avoids proving the acceptance-ratio algebra directly in ENNReal.

Define, for example,
\[
F(x,y)=\operatorname{ofReal}
\left(\min\{\pi(x)q(x,y),\pi(y)q(y,x)\}\right).
\]
Then establish:

- joint measurability of \(F\);
- \(F(x,y)=F(y,x)\);
- \(F(x,y)=\operatorname{ofReal}(\pi(x))\,w(x,y)\).

The accepted contribution becomes
\[
\begin{aligned}
\int^-x\;\operatorname{ofReal}(\pi(x))
 \frac{\int^-y\in E\,w(x,y)}Z
&=\frac1Z\int^-y\in E\int^-x\,F(x,y)\\
&=\int^-y\in E\;\operatorname{ofReal}(\pi(y))a(y).
\end{aligned}
\]
The rejection contribution supplies the complementary factor.

### Measurability details

For the abstract A0 theorem, assume joint measurability explicitly. Separate measurability is not enough.

For the Gaussian instance, the functions are actually **continuous**, including the acceptance probability:

- `min` preserves continuity;
- the denominator is everywhere strictly positive;
- hence the quotient is continuous.

So there is no genuine discontinuity issue here. Proving continuity and taking `.measurable` may be easier than asking automation to reconstruct everything at once.

`fun_prop` is a reasonable first attempt, but isolate helper lemmas for:

- the quadratic form;
- the residual `(x, y) ↦ y - A *ᵥ x`;
- positivity/nonvanishing of the denominator.

For Tonelli with the set integral, either:

- use the measures `μ` and `μ.restrict E`, or
- put the indicator into the integrand and use `μ.prod μ`.

Both work. The restricted-measure version often keeps the displayed integrand cleaner. Global measurability gives the required a.e. measurability under these measures.

Changing the definition of \(\alpha\) to `min(...) / (...)` is not necessary. Keep the conventional MH definition and prove the minimum-flux lemma once.

---

## 4. Gaussian identification and the pinned Mathlib

I cannot certify the September 2026 checkout’s `multivariateGaussian` density API without inspecting that checkout. I would not plan B around an assumed theorem name.

Search the local source for combinations of:

- `multivariateGaussian`, `withDensity`;
- `density`, `pdf`, `rnDeriv`;
- positive-definite covariance and Lebesgue volume.

Even if a suitable theorem exists, moving between `EuclideanSpace ℝ ι` and `ι → ℝ`, and matching normalizing constants, may be a separate piece of work.

**The normalized density-level A4 is a mathematically complete endpoint:**
\[
\nu_P
=\mathrm{volume}.\mathrm{withDensity}
\left(x\mapsto
\frac{\operatorname{ofReal}(e^{-x^\top Px/2})}{T_P}
\right),
\]
with proofs that \(\nu_P\) is a probability measure and is invariant.

One particularly useful alternative to B: exploit the seabed’s Gaussian moment results to prove that this normalized measure has mean zero and covariance \(P^{-1}\). That directly supports the note’s “lands on \(P^{-1}\)” claim without requiring identification with Mathlib’s named distribution. Be explicit that density invariance and covariance identification are separate results.

---

## 5. Scope and recommended order

I would implement:

1. **Real-valued MH acceptance and minimum-flux identity.**
2. **General setwise invariance**, on a σ-finite reference space.
3. **Kernel packaging and Markov property.**
4. **General Gaussian ratio A1.**
5. **MALA/pMALA specializations and proposal normalization.**
6. **Normalized Gaussian invariance**, plus covariance \(P^{-1}\) if the existing moment API makes it inexpensive.

A natural inexpensive strengthening is **reversibility**, not just invariance. The accepted flux is symmetric, and the rejection measure is supported on the diagonal. This is more valuable structurally than an expected-acceptance calculation.

A small strict-acceptance corollary is also easy: assuming nonzero dimension, \(P\succ0\), and \(h>0\), take \(x=0\) and \(y\ne0\). Then both MALA and pMALA have \(\alpha(0,y)<1\). State it this way rather than “ULA’s ratio is not 1”; ULA itself has no acceptance step.

I would defer expected acceptance rates and convergence. Neither is needed for the stationary-law claim, and neither follows merely from invariance.

**Vote: A**, with explicit joint measurability, \(0<Z<\infty\), \(P\succ0\), \(h>0\), and target normalization. Include kernel packaging and, if cheap, reversibility and covariance identification. Treat **B as an opportunistic API-dependent add-on**, not a prerequisite.