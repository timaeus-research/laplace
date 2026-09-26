## Ranking

1. **Second-order transport by freezing the regression residual at the base point.** This avoids differentiating the inverse, the velocity, **and** the regression coefficient.
2. **Residual-information split via the lifted measure and its pushforward.** For the finite-entropy tilt case, conditional expectation is unnecessary.
3. **Package the lift as the unique minimum-information realization of a statistic law; then prove the nested-statistic tower law.** These are genuinely structural consequences.
4. **Only afterward build operator-valued covariance differentiation.** Useful infrastructure, but not needed for item 2.
5. **Pinsker/endpoint and entropy-ordering corollaries.** Cheap and worth exporting, but less new.

There is also a sign correction worth making explicit: with your convention
\[
Dm(\theta)=-C_\theta,\qquad v_s=\theta_s',
\]
the affine response path satisfies
\[
C_s v_s=-\Delta,
\qquad
\operatorname{Cov}_{P_s}(\langle e,S\rangle,\langle v_s,S\rangle)
=-\langle e,\Delta\rangle.
\]
The final residual-curvature formula is unchanged.

---

## 1. Second-order transport: freeze the residual, not the velocity

### The trick

Fix \(s_0\), and compute the regression coefficient **only at \(s_0\)**:
\[
\operatorname{Cov}_{P_{s_0}}(\langle\beta_0,S\rangle,\langle e,S\rangle)
=
\operatorname{Cov}_{P_{s_0}}(\phi,\langle e,S\rangle)
\quad(e\in\mathbb V).
\]
Define the fixed observable
\[
r_0(x)=
\phi(x)-E_{P_{s_0}}\phi
-\langle\beta_0,S(x)-M_{s_0}\rangle .
\]
Then
\[
E_{P_{s_0}}r_0=0,\qquad
\operatorname{Cov}_{P_{s_0}}(r_0,\langle e,S\rangle)=0
\quad(e\in\mathbb V).
\]

Because \(M_s=M_0+s\Delta\), your first-order theorem gives, near \(s_0\),
\[
F'(s)=\langle\beta_0,\Delta\rangle
-\operatorname{Cov}_{P_s}(r_0,\langle v_s,S\rangle),
\qquad F(s)=E_{P_s}\phi.
\]

Now differentiate the last covariance **at \(s_0\)**. Its dependence on \(v_s\) costs only continuity, because the covariance functional multiplying \(v_s\) vanishes at \(s_0\).

Thus
\[
F''(s_0)
=
\operatorname{thirdCentral}_{P_{s_0}}
(r_0,\langle v_{s_0},S\rangle,\langle v_{s_0},S\rangle)
=
E_{P_{s_0}}
\left[r_0\langle v_{s_0},S-M_{s_0}\rangle^2\right].
\]

**Neither \(v'\) nor \(\beta'\) appears anywhere in the proof.**

### The one small calculus lemma

The elementary mechanism is:

> If \(a\) is differentiable at \(s_0\), \(a(s_0)=0\), and \(b\) is continuous at \(s_0\), then  
> \[
> \frac d{ds}\bigl(a(s)b(s)\bigr)\big|_{s_0}=a'(s_0)b(s_0).
> \]

A Lean-shaped scalar helper:

```lean
lemma HasDerivAt.mul_of_eq_zero_of_continuousAt
    {a b : ℝ → ℝ} {a' s₀ : ℝ}
    (ha : HasDerivAt a a' s₀)
    (ha₀ : a s₀ = 0)
    (hb : ContinuousAt b s₀) :
    HasDerivAt (fun s => a s * b s) (a' * b s₀) s₀
```

This statement is a proposed local helper, not an assertion about an existing Mathlib name. Prove it directly with the slope characterization of `HasDerivAt`: the difference quotient is the slope of \(a\) times \(b(s)\).

For the covariance argument, choose an orthonormal basis \(e_i\) of \(\mathbb V\) and write
\[
\operatorname{Cov}_{P_s}(r_0,\langle v_s,S\rangle)
=
\sum_i
\underbrace{\operatorname{Cov}_{P_s}(r_0,\langle e_i,S\rangle)}_{a_i(s)}
\underbrace{\langle e_i,v_s\rangle}_{b_i(s)}.
\]
Your cubic-response theorem differentiates each \(a_i\), each \(a_i(s_0)=0\), and your existing inverse-continuity theorem makes each \(b_i\) continuous.

This is finite sums, covariance bilinearity, and the helper above. **No operator-norm differentiation is needed.**

### Target theorem and hypotheses

A useful abstract theorem has these hypotheses:

- \(J\) finite; \(X\) any measurable space.
- \(\nu\) a probability measure.
- Each statistic \(S_j\), and \(\phi\), measurable and bounded.
- \(s_0\) lies in an open parameter interval \(U\).
- \(\theta:U\to\mathbb V\), with `HasDerivAt θ (v s) s` for every \(s\in U\).
- `ContinuousAt v s₀`.
- \(m(\theta_s)=M_0+s\Delta\) on \(U\).
- A coefficient \(\beta_0\in\mathbb V\) satisfying the regression equations above.

The regression coefficient’s existence can then be discharged separately by your visible-space covariance invertibility.

Schematic atlas specialization:

```lean
theorem hasDerivAt_deriv_integral_responseProjection_atlas
    (hs₀ : s₀ ∈ Set.Ioo (0 : ℝ) 1)
    (hφmeas : Measurable φ)
    (hφbdd : ∃ L : ℝ, ∀ x, |φ x| ≤ L) :
    HasDerivAt
      (fun s =>
        deriv (fun t => ∫ x, φ x ∂Π (M t)) s)
      (∫ x,
        regressionResidual φ s₀ x *
          (visiblePair (atlasVel s₀) (S x - M s₀)) ^ 2
        ∂Π (M s₀))
      s₀
```

Here the notation is schematic and inherits the atlas’s existing law/statistic/finite-rate assumptions. Prove the derivative formula on a neighborhood, then use derivative congruence to identify `deriv`.

**Recommendation:** first prove the version taking a supplied \(\beta_0\) and its covariance equations. The canonical regression-residual version should be a wrapper.

### What fixed-\(v\) differentiation alone gives

Your option (b), without more work, only differentiates a frozen-direction first-order expression. It is not yet the second derivative along the response atlas.

The frozen-residual argument supplies precisely the missing cancellation. It is option (c), but without presupposing \(v_s'\).

---

## 2. Residual split: the shortest route does not use conditional expectation

Write
\[
\mu=S_*\nu,\qquad \lambda=S_*D,\qquad
r=\frac{d\lambda}{d\mu},\qquad
D^\uparrow=\nu.\mathrm{withDensity}(r\circ S).
\]

Use ENNReal RN derivatives for the definition. Introduce real-valued logarithms only after obtaining the relevant almost-everywhere finiteness and positivity.

Assume:

- \(\nu,D\) are probability measures;
- \(S:X\to Y\) is measurable;
- \(\mathrm{KL}(D\|\nu)<\infty\).

No standard-Borel hypothesis or conditional kernel is needed.

### Step 1: prove the lift’s measure identities

The indispensable small package is
\[
S_*D^\uparrow=\lambda,\qquad
D^\uparrow(X)=1,\qquad
D^\uparrow\ll\nu,\qquad D\ll D^\uparrow.
\]

The pushforward identity is just change of variables for `withDensity`:
\[
S_*(\nu.\mathrm{withDensity}(r\circ S))
=\mu.\mathrm{withDensity}(r)=\lambda.
\]

For \(D\ll D^\uparrow\), the essential observation is
\[
D\{r\circ S=0\}=\lambda\{r=0\}=0.
\]
Together with \(D\ll\nu\), this gives the result. No conditional expectation is involved.

Schematic definition:

```lean
def statisticLift (ν D : Measure X) (S : X → Y) : Measure X :=
  ν.withDensity
    (fun x => ((D.map S).rnDeriv (ν.map S)) (S x))
```

### Step 2: prove the base-law entropy decomposition

Target:
\[
\boxed{\quad
\mathrm{KL}(D\|\nu)
=
\mathrm{KL}(D\|D^\uparrow)
+
\mathrm{KL}(\lambda\|\mu).
\quad}
\]

The required integrability comes almost entirely from finite KL and data processing:

1. Finite \(\mathrm{KL}(D\|\nu)\) gives \(D\ll\nu\) and
   \[
   \log(dD/d\nu)\in L^1(D).
   \]

2. Data processing gives
   \[
   \mathrm{KL}(\lambda\|\mu)<\infty,
   \]
   hence
   \[
   \log r\in L^1(\lambda).
   \]

3. Pushforward integration gives
   \[
   \log(r\circ S)\in L^1(D).
   \]
   It also gives integrability under \(D^\uparrow\), since its pushforward is likewise \(\lambda\).

4. The RN chain rule, with positivity checked \(D\)-a.e., yields
   \[
   \operatorname{llr}(D,D^\uparrow)
   =
   \operatorname{llr}(D,\nu)-\log(r\circ S)
   \quad D\text{-a.e.}
   \]
   The right side is integrable, proving finite residual KL and the desired identity.

For probability measures, the negative part of the log-likelihood ratio is automatically integrable; finite KL controls the positive part. That is the fact to use behind whichever finite-KL/`Integrable llr` API your version exposes.

**You do not need a dedicated `integrable_llr_map` theorem:** finite mapped KL plus the ordinary finite-KL integrability criterion suffices.

### Step 3: obtain the bounded-tilt theorem by subtraction

Let
\[
P=\nu.\mathrm{tilted}(f\circ S),
\qquad
g(y)=\frac{e^{f(y)}}{\int e^f\,d\mu}.
\]
Assume \(f\) measurable and bounded. Then \(\log g\) is bounded, \(P\) is equivalent to \(\nu\), and
\[
S_*P=\mu.\mathrm{tilted}(f).
\]

Your existing tilted-right formula gives
\[
\mathrm{KL}(D\|P)
=
\mathrm{KL}(D\|\nu)-E_\lambda\log g,
\]
while the same formula on the statistic space gives
\[
\mathrm{KL}(\lambda\|S_*P)
=
\mathrm{KL}(\lambda\|\mu)-E_\lambda\log g.
\]
Subtract using the base-law decomposition.

Schematic target:

```lean
theorem klDiv_eq_residual_add_map_tilted
    [IsProbabilityMeasure ν] [IsProbabilityMeasure D]
    (hS : Measurable S)
    (hf : Measurable f)
    (hf_bdd : ∃ L : ℝ, ∀ y, |f y| ≤ L)
    (hKL : klDiv D ν < ⊤) :
    klDiv D (ν.tilted (f ∘ S)) =
      klDiv D (statisticLift ν D S) +
      klDiv (D.map S) ((ν.tilted (f ∘ S)).map S)
```

Again, this is a target shape rather than verified declaration syntax.

**Order:** base-law split → bounded tilt → general statistic-measurable density.

---

## 3. The `klFun` identity exists, but is not an integrability-free shortcut

Put
\[
\rho=\frac{dD}{d\nu},\qquad t=r\circ S,\qquad b=g\circ S,
\]
and \(K(z)=z\log z-z+1\). Where the expressions are finite and \(t,b>0\),
\[
\boxed{
bK(\rho/b)
=
tK(\rho/t)+bK(t/b)+(\rho-t)\log(t/b).
}
\]

With appropriate zero conventions, this extends across \(t=0\) in the bounded-tilt situation, because \(t=0\) implies \(\rho=0\), \(\nu\)-a.e.

The cross term integrates to zero because
\[
S_*D=S_*D^\uparrow:
\]
\[
\int \rho\log(t/b)\,d\nu
=
\int \log(r/g)\,d\lambda
=
\int t\log(t/b)\,d\nu.
\]

But this is a **signed** cross term. Its cancellation is not a consequence of nonnegative-lintegral algebra alone. You still need integrability, or a separate truncation argument.

Under your hypotheses, integrability is easy:

- \(\log r\in L^1(\lambda)\) by mapped finite entropy;
- \(\log g\) is bounded.

So the identity is useful, but I would formalize the `llr` route first. It avoids a substantial amount of quotient/zero-case algebra.

### General \(P\) with density a function of \(S\)

Still assuming \(\mathrm{KL}(D\|\nu)<\infty\), the boundedness restriction can subsequently be removed for a probability measure
\[
P=\nu.\mathrm{withDensity}(g\circ S).
\]

Split on finiteness of \(\mathrm{KL}(\lambda\|S_*P)\):

- **Infinite:** data processing forces \(\mathrm{KL}(D\|P)=\infty\).
- **Finite:** both \(\operatorname{llr}(\lambda,\mu)\) and
  \(\operatorname{llr}(\lambda,S_*P)\) are integrable. Their difference supplies integrability of \(\log g\) under \(\lambda\), and the same subtraction proof works.

Thus the general-density extension is relatively cheap **after** the finite-base-entropy package. Removing finite base entropy as well is a different, more genuinely measure-theoretic project.

---

## 4. If you later want the operator derivative, use finite coordinates—not another IFT

For future third-order work or explicit acceleration, the clean route is:

1. Fix an orthonormal basis of \(\mathbb V\).
2. Form the matrix entries
   \[
   C_{ij}(s)=\operatorname{Cov}_{P_s}(\langle e_i,S\rangle,\langle e_j,S\rangle).
   \]
3. Differentiate each entry using `hasDerivAt_lawCov_dataPath`:
   \[
   C_{ij}'(s_0)=-T_{s_0}(e_i,e_j,v_{s_0}).
   \]
4. Assemble the finite family with the `HasDerivAt`/`HasFDerivAt` finite-`Pi` rules.
5. Transport through a fixed continuous linear equivalence between matrices and
   \(\mathbb V\toL[\mathbb R]\mathbb V\).

This genuinely proves operator-norm differentiability: finite-dimensional coordinate assembly is what supplies that step.

Then apply the Banach-algebra inverse theorem, `hasFDerivAt_ring_inverse`, at the unit supplied by your `ContinuousLinearEquiv`. Use `Ring.inverse` on the endomorphism algebra and locally identify it with your chart inverse. Finally use `.clm_apply`.

The formulas are
\[
(C^{-1})'=-C^{-1}C'C^{-1},\qquad
v'=-C^{-1}C'v,
\]
because \(Cv=-\Delta\).

This requires only the **pathwise** derivative of \(C_s\), not a joint \(C^1\) theorem for \(F(s,v)\). An implicit-function proof here would rebuild substantially more machinery than necessary.

---

## 5. The deeper cheap consequences: lift geometry and a tower law

### A. The lift is the unique least-informative realization of a statistic law

For a probability law \(\lambda\ll S_*\nu\), define
\[
L_\nu(\lambda)=\nu.\mathrm{withDensity}
\left(\frac{d\lambda}{d(S_*\nu)}\circ S\right).
\]

Then
\[
S_*L_\nu(\lambda)=\lambda,\qquad
\mathrm{KL}(L_\nu(\lambda)\|\nu)
=\mathrm{KL}(\lambda\|S_*\nu).
\]

For every finite-base-entropy \(D\) with \(S_*D=\lambda\),
\[
\mathrm{KL}(D\|\nu)
=
\mathrm{KL}(D\|L_\nu(\lambda))
+
\mathrm{KL}(L_\nu(\lambda)\|\nu).
\]

Hence the lift is the unique minimizer of relative entropy among laws realizing the **entire statistic distribution**, not merely its mean. Infinite-entropy competitors cannot improve it when the lift has finite entropy.

This gives a clean interpretation:

> The lift retains exactly the information visible through \(S\), while discarding all residual information relative to \(\nu\).

Uniqueness is just the probability-law criterion `KL = 0 ↔ equality`.

### B. Nested statistics give an exact information tower

If \(T=h\circ S\), with both maps measurable, let \(D^{\uparrow S}\) and \(D^{\uparrow T}\) be the two lifts relative to the same \(\nu\). Then
\[
\boxed{
\mathrm{KL}(D\|D^{\uparrow T})
=
\mathrm{KL}(D\|D^{\uparrow S})
+
\mathrm{KL}(D^{\uparrow S}\|D^{\uparrow T}).
}
\]

Under finite \(\mathrm{KL}(D\|\nu)\), all terms are finite. Prove this by applying the base-law split to \(D\) and to \(D^{\uparrow S}\), observing that they have the same \(T\)-pushforward.

This is an exact multiscale decomposition of invisible information—again without disintegration or conditional expectation.

### C. Endpoint observables: export, but do not mistake it for new structure

Your endpoint estimate plus Pinsker gives, for \(|\phi|\le L\),
\[
|E_{\Pi(M)}\phi-E_{\Pi(M_s)}\phi|
\le L\sqrt{2\,\mathrm{KL}(\Pi(M)\|\Pi(M_s))}
\le \frac{L\|\Delta\|}{\sqrt{\kappa_r}}(1-s).
\]
This assumes the same ball-control hypothesis as the quadratic KL estimate. For oscillation \(\operatorname{osc}\phi\), the sharper coefficient is
\[
\frac{\operatorname{osc}\phi\,\|\Delta\|}{2\sqrt{\kappa_r}}.
\]

Worth landing immediately, but the two main discoveries here are stronger: **second-order observable transport needs no inverse differentiation, and the finite-entropy residual split needs no conditional-expectation API.**