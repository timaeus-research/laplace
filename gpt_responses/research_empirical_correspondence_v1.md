The deterministic part can be made substantially sharper. The main correction is conceptual:

> Sup-norm closeness gives a **sufficient resolution guarantee**, not an information-theoretic upper bound on resolvable jet order. In particular, “resolution grows like \(\log n\)” is not a universal law without additional uniformity and statistical assumptions.

Below, all partition functions are assumed positive and all displayed integrals finite.

## 1. Sharp relative stability

Put
\[
A_L(\phi,t):=\frac{\int |\phi|e^{-tL}}{\int\chi e^{-tL}},
\qquad a=t\delta.
\]
Under your supportwise hypothesis,
\[
\boxed{
\left|\langle\phi\rangle_{K,t}-\langle\phi\rangle_{L,t}\right|
\le (e^{2a}-1)A_L(\phi,t).
}
\tag{1}
\]

This is the sharp universal bound **in terms of \(a\) and \(A_L(\phi,t)\) alone**.

Indeed, with
\[
w=e^{-t(K-L)},\qquad
b=\frac{\int\chi w e^{-tL}}{\int\chi e^{-tL}},
\]
we have \(e^{-a}\le w,b\le e^a\), and
\[
\langle\phi\rangle_K-\langle\phi\rangle_L
=\frac{\int\phi(w/b-1)e^{-tL}}{Z_L}.
\]
Thus \(|w/b-1|\le e^{2a}-1\). Sharpness is approached by concentrating the numerator where \(w=e^a\), while almost all denominator mass lies where \(w=e^{-a}\).

Consequently, your bound is correct, but not optimal. For \(0\le a\le1\),
\[
e^{2a}-1\le (e^2-1)a,
\]
so \(11\) can be replaced by \(e^2-1<6.39\). Infinitesimally, the sharp relative constant is \(2a+O(a^2)\).

### Two useful refinements

**Additive constants do not matter.** If
\[
\operatorname{osc}_{\operatorname{supp}\phi\cup\operatorname{supp}\chi}(K-L)\le \omega,
\]
then (1) improves to
\[
|\langle\phi\rangle_K-\langle\phi\rangle_L|
\le (e^{t\omega}-1)A_L.
\tag{2}
\]
This is important for empirical losses: random additive constants should be removed before estimating perturbation size.

**Bounded probability observables admit a different sharp bound.** If \(\phi=\chi f\), define
\[
dP_{L,t}=\frac{\chi e^{-tL}}{Z_L}\,dx.
\]
For bounded real \(f\),
\[
\boxed{
|P_{K,t}f-P_{L,t}f|
\le \operatorname{osc}(f)\tanh(t\omega/4).
}
\tag{3}
\]
In particular, \(\omega\le2\delta\) gives \(\operatorname{osc}(f)\tanh(t\delta/2)\). This follows from the sharp total-variation bound for a likelihood tilt with bounded log-oscillation.

Equation (1) is the right immediate replacement for your existing denominator-amplified estimate. It removes explicit \(1/Z\) amplification, although \(A_L\) itself still needs control.

---

## 2. Finite-order detection: correct, with “if” rather than “iff”

Let
\[
D_L(t)=\langle\phi\rangle_{L_2,t}-\langle\phi\rangle_{L_1,t},
\qquad
D_K(t)=\langle\phi\rangle_{K_2,t}-\langle\phi\rangle_{K_1,t}.
\]
If \(A_{L_j}(\phi,t)\le Mt^{-s}\), then
\[
\boxed{
|D_K(t)-D_L(t)|
\le E(t,\delta):=2M t^{-s}(e^{2t\delta}-1).
}
\tag{4}
\]
For \(t\delta\le1\),
\[
E(t,\delta)\le 2(e^2-1)M\delta t^{1-s}.
\tag{5}
\]

Thus:

* Under a signal hypothesis \(|D_L(t)|\ge a t^{-r}\),
  \[
  |D_K(t)|\ge a t^{-r}-E(t,\delta).
  \]
* Under a same-germ hypothesis \(|D_L(t)|\le B(t)\),
  \[
  |D_K(t)|\le B(t)+E(t,\delta).
  \]

These bounds give disjoint null/alternative ranges whenever
\[
\boxed{a t^{-r}>B(t)+2E(t,\delta).}
\tag{6}
\]
Your proposed condition is slightly stronger and therefore also sufficient.

It is **not an iff about actual distinguishability**: the perturbation bounds need not be attained, and failure of the certificate need not imply failure of a test. It is an iff only for separation of the particular worst-case intervals produced by these bounds.

For same germs, use your actual population bound \(B(t)=Ct^d e^{-\eta t}\), or absorb the polynomial into a smaller exponential rate.

### Jet specialization

Assume:

* a unique nondegenerate zero at \(0\);
* a common Hessian;
* first jet difference \(Q_k\) at degree \(k\ge3\);
* a monomial with a compact cutoff equal to one near \(0\);
* \(\operatorname{Cov}_\gamma(x^\alpha,Q_k)\ne0\).

Then, with \(q=|\alpha|\),
\[
s=q/2,\qquad r=(q+k-2)/2.
\]
The perturbation-to-signal ratio is therefore bounded by a constant times
\[
\frac{M}{a}\delta t^{k/2}.
\]
Hence the natural sufficient condition is
\[
\boxed{\delta t^{k/2}\ll a/M.}
\tag{7}
\]

This part of your draft is right. Nonzero covariance is essential: parity alone already makes many monomials blind.

For implementation, it may be cleaner to work directly with rescaled observables. Then \(s=0\), signal order is \(t^{-(k-2)/2}\), and the same condition follows.

---

## 3. What sample size actually implies

### The theorem justified by deterministic closeness

For a **fixed** detectable jet difference \(Q_k\), suppose
\[
\mathbb P(E_n)\ge1-\varepsilon_n,\qquad
E_n=\{\|K_{j,n}-L_j\|_{\infty,S}\le\delta_n,\ j=1,2\}.
\]
If
\[
t_n\longrightarrow\infty,
\qquad
\delta_n t_n^{k/2}\longrightarrow0,
\tag{8}
\]
then on \(E_n\), empirical expectation differences preserve the nonzero leading population coefficient.

For \(\delta_n=O(n^{-1/2})\) and \(t_n=n^\beta\), a sufficient condition is
\[
\boxed{\beta k<1.}
\tag{9}
\]
The same strict inequality works with \(\delta_n=O(\sqrt{\log n/n})\).

This is a clean, honest “empirical correspondence” theorem:

> Every fixed, observable-visible finite jet difference survives empirical perturbation along sufficiently slow temperature schedules.

### Why the fixed-\(T\) logarithmic law is only conditional

At a fixed \(T>1\), condition (7) gives
\[
k\lesssim
\frac{2\log(1/\delta_n)}{\log T}
+\frac{2\log(a/M)}{\log T}.
\]
For root-\(n\) error this suggests \(\log n/\log T\). But to turn that into a theorem with \(k=k_n\to\infty\), you need uniform control of:

1. the asymptotic validity threshold \(T_0(k,Q_k,\phi)\);
2. the signal coefficient \(a_k\);
3. the observable size \(M_k\);
4. the expansion remainder and contributions from higher jets;
5. visibility or conditioning of the chosen observable family.

None follows from analyticity near each individual zero. Gaussian moment constants can grow rapidly with degree, while signal coefficients can be arbitrarily small.

Accordingly:

\[
\boxed{\text{“Resolution }\sim\log n\text{” is a conditional certificate scaling, not a fundamental law.}}
\]

There is also no impossibility conclusion from a sup-norm upper bound alone. Some perturbations are additive constants and have exactly zero effect; others are especially damaging. A minimax impossibility theorem needs a specified statistical experiment and a separated class of alternatives.

### Does increasing temperature help?

For a fixed signal and the sup-norm error model, increasing \(t\) worsens \(\delta t^{k/2}\). But it improves localization and reduces asymptotic contamination. The practical optimum is therefore a bias–perturbation tradeoff, not simply “take \(t\) as small as possible.”

Your present hypotheses do not quantify that tradeoff uniformly. They justify taking \(t\) above the signal’s validity threshold, and no larger than necessary.

---

## 4. A sharper fluctuation-based theorem

There is a precise deterministic formulation that captures the improvement available from empirical structure.

Use probability observables \(\phi=\chi f_t\), put \(R_n=K_n-L\), and interpolate
\[
L_u=L+uR_n,\qquad 0\le u\le1.
\]
Under differentiation-under-the-integral hypotheses,
\[
\frac{d}{du}P_{L_u,t}f_t
=-t\,\operatorname{Cov}_{P_{L_u,t}}(f_t,R_n).
\tag{10}
\]
Suppose, uniformly in \(u\),
\[
\operatorname{Var}_{P_{L_u,t}}(f_t)\le V^2,
\qquad
\operatorname{Var}_{P_{L_u,t}}(R_n)
\le C^2 n^{-1}t^{-q}.
\tag{11}
\]
Then
\[
\boxed{
|P_{K_n,t}f_t-P_{L,t}f_t|
\le CV n^{-1/2}t^{1-q/2}.
}
\tag{12}
\]

Against a rescaled jet signal \(a t^{-(k-2)/2}\), the sufficient condition becomes
\[
\boxed{n^{-1/2}t^{(k-q)/2}\ll a/(CV).}
\tag{13}
\]

Interpretation:

* \(q=0\): the sup-norm-style exponent.
* \(q=1\): a root-\(n\) random linear term near the minimizer.
* \(q=2\): leading random quadratic variation, after eliminating linear variation.
* Higher \(q\): increasingly structured local perturbations.

These are hypotheses to prove, not automatic consequences of a uniform LLN. In particular, (11) must hold along the interpolation, and requires localization and tail control.

### The SLT/posterior temperature \(t\asymp n\)

For an empirical average loss, the ordinary random score gives a local perturbation of order
\[
n^{-1/2}|x|.
\]
At \(x=y/\sqrt n\), multiplication by \(t=n\) makes this an order-one random linear tilt in \(y\). Consequently, the empirical rescaled law need not converge to the population-centered Gaussian. One normally sees a random shift, or recenters at an empirical minimizer.

Thus your sup-norm theorem being uninformative at \(t\asymp n\) is expected. A useful theorem there needs local stochastic expansions, centering, and—in singular settings—appropriate singular local geometry. Population free-energy exponents alone do not supply it.

Finally, sampling observables from the Gibbs law is a separate noise source. If estimated from \(S\) independent draws with bounded variance, a rescaled signal additionally requires roughly
\[
S^{-1/2}\ll t^{-(k-2)/2}.
\]
Keep this distinct from estimating the loss using \(n\) training samples.

---

## 5. The honest probabilistic layer

Your proposed event-based interface is exactly right.

Prove all analytic conclusions deterministically under \(E_n\). Then prove the elementary probability transfer:
\[
E_n\subseteq G_n,\quad \mathbb P(E_n)\ge1-\varepsilon_n
\quad\Longrightarrow\quad
\mathbb P(G_n)\ge1-\varepsilon_n.
\tag{14}
\]

For two empirical losses, either assume a joint event or use a union bound. No independence is needed for the latter.

I would **not** record \(\sqrt{\log n/n}\) as a consequence of “compact parameter set + uniform LLN.” A uniform LLN alone supplies no such rate. Root-\(n\)-type uniform rates require quantitative envelope/tail and complexity assumptions.

A safe external interface is:
\[
\mathbb P\!\left(
\sup_{x\in S}|K_n(x)-L(x)|>\delta(n,\varepsilon)
\right)\le\varepsilon.
\]
An external theorem can instantiate, for example,
\[
\delta(n,\varepsilon)
\le C\sqrt{\frac{v\log n+\log(1/\varepsilon)}n}
\]
under its stated assumptions.

For measurability, a useful Lean formulation is “there exists a measurable good event on which the pointwise bound holds.” This avoids immediately formalizing measurability of an uncountable supremum.

---

## 6. Exact visibility of the monomial family

Let \(\gamma\) be a nondegenerate centered Gaussian, and let \(\mathcal P_{\le m}\) be the polynomials of total degree at most \(m\). Define
\[
\mathcal P_{\le m}^0
=\{p\in\mathcal P_{\le m}:E_\gamma p=0\}.
\]

The clean theorem is:

\[
\boxed{
\bigl(\operatorname{Cov}_\gamma(x^\alpha,Q)\bigr)_{|\alpha|\le m}
\text{ determines exactly }
\operatorname{proj}_{\mathcal P_{\le m}^0}(Q-E_\gamma Q).
}
\tag{15}
\]

Equivalently, the family is blind to \(Q\) precisely when
\[
Q-E_\gamma Q\perp\mathcal P_{\le m}^0.
\tag{16}
\]

In Gaussian-chaos language, it sees exactly the chaos components of degrees \(1,\ldots,m\); it never sees the constant component.

### Restricting to a homogeneous degree-\(k\) jet difference

A homogeneous \(Q_k\) has Gaussian-chaos degrees
\[
k,k-2,k-4,\ldots.
\]
Therefore:

* If \(1\le k\le m\), the family detects every nonzero homogeneous \(Q_k\).
* If \(k>m\), some directions remain visible through lower-chaos components.
* In \(d\ge2\), nonzero homogeneous Gaussian-harmonic degree-\(k\) directions are invisible whenever \(k>m\).
* It is false that every degree-\(k\) homogeneous polynomial is invisible for \(k>m\).

An elementary proof of the first point avoids Hermite theory entirely: if all covariances vanish and \(Q_k\in\mathcal P_{\le m}\), then
\[
\operatorname{Var}_\gamma(Q_k)=0.
\]
Full Gaussian support makes \(Q_k\) constant as a polynomial; positive-degree homogeneity then makes it zero.

### Optional sharper rank theorem

Write \(\Sigma=H^{-1}\) and
\[
\Delta_\Sigma=\sum_{i,j}\Sigma_{ij}\partial_i\partial_j.
\]
Let \(p\) be the largest integer satisfying
\[
1\le p\le\min(m,k),\qquad p\equiv k\pmod2.
\]
If no such \(p\) exists, the covariance map on homogeneous degree \(k\) is zero. Otherwise its kernel is
\[
\boxed{
\ker\!\left(\Delta_\Sigma^{(k-p)/2}:\mathcal H_k\to\mathcal H_p\right),
}
\tag{17}
\]
where \(\mathcal H_j\) here denotes **homogeneous polynomials**, not Hermite chaos. Its rank is
\[
\binom{d+p-1}{p}.
\tag{18}
\]
This uses Gaussian integration by parts and surjectivity of the indicated Laplacian power.

Thus raw observable count overstates independent leading information on a fixed homogeneous jet.

### Formalization route

Start with (15)–(16), not multivariate Hermites:

1. Gaussian polynomial integrability.
2. Covariance as a positive-semidefinite bilinear form.
3. Constants as its exact kernel.
4. Finite-dimensional projection or an equivalent Gram-matrix statement.
5. Monomials span \(\mathcal P_{\le m}\).

Only then add the trace/Laplacian characterization using Stein identities. Your existing covariance/Stein infrastructure sounds well aligned with that second stage. Explicit multivariate Hermite polynomials are unnecessary.

Also, this is **leading-order visibility**. A direction invisible to these leading covariances can affect higher expansion coefficients through nonlinear terms.

---

## 7. Ranked Lean plan

These are rough proof-body estimates assuming the infrastructure you describe; they are not estimates from inspecting the repository.

| Rank | Theorem package | Main statement | Expected size |
|---|---|---|---|
| **1** | `normalizedExpectation_sub_le_relative` | Equation (1), then the \(t\delta\le1\) linear corollary. Add oscillation invariance if convenient. | Small–medium: roughly 100–250 lines |
| **2** | `empirical_signal_separation` | Equation (4), signal lower bound, same-germ upper bound, and threshold certificate (6). | Small: roughly 60–150 lines |
| **3** | `empirical_jet_leadingCoeff_preserved` | Nonzero population coefficient plus \(\delta_n t_n^{k/2}\to0\) implies the same empirical leading coefficient; specialize to \(t_n=n^\beta\), \(\beta k<1\). | Medium: roughly 150–350 lines |
| **4** | `monomial_covariance_visibility` | Vanishing monomial covariances iff orthogonality to centered degree-\(\le m\) polynomials; injectivity on homogeneous degrees \(1,\ldots,m\). | Medium–large: roughly 250–600 lines, infrastructure-dependent |
| **5** | `empirical_resolution_with_highProbability` | Measurable good-event interface and probability transfer for theorem 3; optional eventual/almost-sure version under summable failure probabilities. | Small for event transfer; medium for asymptotic variants |
| **6** | `normalizedExpectation_perturbation_covariance_bound` | Interpolation identity (10) and variance bound (12). This is the bridge to score/Hessian-based empirical analysis. | Large: likely several hundred lines, depending on differentiation-under-integral support |

I would postpone the exact rank formula (17)–(18), sharp total-variation theorem, and minimax lower bounds until after this core.

The resulting headline theorem should be:

> **Conditional on uniform empirical-loss control, every fixed finite jet difference visible to the chosen observable family is preserved along temperature schedules satisfying \(\delta_n t_n^{k/2}\to0\). The observable family’s covariance map identifies precisely which leading jet directions are visible.**

That is already a substantive empirical germ–expectation correspondence, without overstating a universal sample-size resolution law.