**Choose R1, then package a reusable positive-denominator ratio theorem.** It is a useful addition beyond this application, and substantially narrower than a full a.e.-continuous mapping theorem.

There are two important corrections to the proposed application:

1. A lower bound for the **leading coefficient** on \(\{\|X_n\|\le M\}\) is not automatically a lower bound for the **normalised finite-\(n\) denominator** there. You must also control its remainder.
2. Under your fixed-amplitude, equal-start assumptions, the leading coefficients appear to have a common factor. Thus the posterior limit should simplify to a **deterministic corner-value ratio**, not merely a quotient of random variables.

## 1. R1: statement and recommended proof

Here is a clean formulation, with fixed probability measures \(\mu\) on \(\Omega\) and \(\nu\) on \(\Omega'\).

Let \(E\) be a second-countable metric space with its Borel measurable structure, and let
\[
X_n:\Omega\to E,\qquad X:\Omega'\to E.
\]
Assume the maps are a.e. measurable. Suppose that for every \(\varepsilon>0\), there are a.e. measurable maps
\[
Y_n^\varepsilon:\Omega\to E,\qquad
Y^\varepsilon:\Omega'\to E
\]
such that
\[
Y_n^\varepsilon\Rightarrow Y^\varepsilon,
\]
\[
\forall^\mathrm{eventually}n,\quad
\mu\{X_n\ne Y_n^\varepsilon\}\le \varepsilon,
\qquad
\nu\{X\ne Y^\varepsilon\}\le \varepsilon.
\]
Then \(X_n\Rightarrow X\).

Here the inequalities use real-valued probabilities; a Lean version can equivalently use `ENNReal.ofReal ε`.

### Filters and measurability

My recommendation:

- State it along a filter `l`, with `[NeBot l]`.
- **The bounded-test-function argument itself does not require `l` to be countably generated.** If the Mathlib characterization you invoke requires that assumption, inherit it rather than spending this unit removing it.
- Require measurability of the original \(X_n,X\), not just of the approximants. Modification on a small event does not by itself supply the measurability needed for a distributional-convergence statement.
- Mathematically, a.e. measurability suffices here. For a first Lean implementation, **ordinary `Measurable` hypotheses are entirely reasonable** and make the disagreement events straightforwardly measurable. Alternatively use the `AEStronglyMeasurable` hypotheses already employed by your distribution API.

I would not claim an exact compiling signature without checking the installed Mathlib definitions. In particular, let the actual bounded-Lipschitz characterization determine whether the theorem should carry `AEMeasurable` or `AEStronglyMeasurable`.

### Proof

For a bounded Lipschitz test function \(f\), with \(|f|\le K\),
\[
\left|\int f(X_n)\,d\mu-\int f(Y_n^\varepsilon)\,d\mu\right|
\le 2K\,\mu\{X_n\ne Y_n^\varepsilon\}.
\]
The same estimate holds for the limits. Therefore, eventually,
\[
\left|\int f(X_n)\,d\mu-\int f(X)\,d\nu\right|
\le 4K\varepsilon+
\left|\int f(Y_n^\varepsilon)\,d\mu-\int f(Y^\varepsilon)\,d\nu\right|.
\]
The last term tends to zero, and \(\varepsilon\) is arbitrary.

**Extract the integral estimate as a helper lemma.** That is likely the reusable measure-theoretic workhorse and the main source of Lean bookkeeping.

An equally useful interface uses approximants indexed by \(m:\mathbb N\), with disagreement bounds \(r_m\to0\). I would implement one interface and derive the other only if a later application wants it.

## 2. Apply R1 by localising the denominator—not the input norm

Write
\[
(U_n,V_n)\Rightarrow(U,V),\qquad \nu\{V>0\}=1.
\]
For \(c>0\), define
\[
g_c(u,v)=\frac{u}{\max(v,c)}.
\]
This is globally continuous, and
\[
g_c(u,v)=u/v\quad\text{whenever }v\ge c.
\]

Choose \(c>0\) sufficiently small that
\[
\nu\{V\le c\}<\varepsilon/2.
\]
Such a choice follows from \(V>0\) a.s. By portmanteau for the closed half-space,
\[
\limsup_n\mu\{V_n\le c\}
\le \nu\{V\le c\}<\varepsilon/2.
\]
Consequently,
\[
\forall^\mathrm{eventually}n,\quad
\mu\{V_n<c\}\le\varepsilon.
\]
The limiting disagreement probability is also at most \(\varepsilon\). Continuous mapping gives
\[
g_c(U_n,V_n)\Rightarrow g_c(U,V),
\]
and R1 gives
\[
U_n/V_n\Rightarrow U/V.
\]

This avoids:

- the quantitative lower bound from u154;
- a second invocation of input tightness;
- coordinating input localisation with remainder control.

You only need u154’s **strict positivity**, followed by denominator marginal convergence and portmanteau.

### Why the original ball argument needs repair

On \(\{\|X_n\|\le M\}\), u154 gives
\[
A^1(X_n)\ge c_M.
\]
But if
\[
V_n=A^1(X_n)+r_n,
\]
then clipping at \(c_M\) need not preserve \(V_n\). A valid version clips at \(c_M/2\) and works on
\[
\{\|X_n\|\le M\}\cap\{|r_n|\le c_M/2\}.
\]
That route works, but the portmanteau argument above is cleaner and produces a genuinely generic ratio theorem.

### Cost assessment

R1 plus the positive-denominator ratio corollary looks like **two focused units**, assuming your existing portmanteau infrastructure can express an eventual probability bound. I would expect measurability and real/ENNReal integral estimates to dominate the work—not the probability argument.

R2 is unnecessary scope expansion here. R3 is an honest fallback, but I would not stop there given how close this proof is.

## 3. A stronger chart conclusion: the random factor cancels

Under the leading-coefficient formula you describe, for fixed amplitude \(y\),
\[
A^y(x)=\frac{y_{00}}{k_1k_2}\,\operatorname{logMoment}_p(x_{00}).
\]
Thus, if numerator and denominator really use the same phase, chart parameters and leading exponent,
\[
\frac{A^\varphi(x)}{A^1(x)}
=\frac{y_{\varphi,00}}{y_{1,00}},
\]
because the common log-moment factor is strictly positive.

So the paper-facing theorem should include
\[
\boxed{\quad
\frac{Z_n[\varphi]}{Z_n[1]}
\Rightarrow
\frac{y_{\varphi,00}}{y_{1,00}}.
\quad}
\]

If the amplitude construction gives
\[
y_{\varphi,00}=\varphi(0,0)y_{1,00},
\]
this is simply convergence to \(\varphi(0,0)\).

**Check that identity explicitly against your definitions before advertising it.** It depends on a common leading kernel, not merely on two unrelated expansions having the same exponent.

This is also why the generic ratio theorem is worth retaining: it applies beyond the cancellation case. If you want convergence in probability to the constant, that is the usual strengthening of convergence in distribution to a point mass; whether to expose it now depends on the available Mathlib bridge.

## 4. Answers to the other questions

### (a) Finite-\(n\) positivity and totalised division

Use Lean’s totalised division for the convergence theorem. **Finite-\(n\) nonvanishing is not required.**

From \(V_n\Rightarrow V\) and \(V>0\) a.s., you obtain
\[
\mu\{V_n=0\}\longrightarrow0.
\]
You do **not** obtain samplewise eventual nonvanishing in general.

Also, the cancellation identity
\[
(a/s)/(b/s)=a/b
\]
requires \(s\ne0\), but does not require \(b\ne0\) in Lean’s totalised field division. Thus use the eventual nonzero scaling factor—typically once \(N_n>1\)—and ignore any finite initial segment.

Separately, I recommend a chart-integral positivity lemma because it validates the literal posterior interpretation:

> Under the existing integrability and positive-box hypotheses, if the amplitude is strictly positive on the interior of the chart box, then `twoDAmp` is strictly positive.

Interior positivity is sufficient; positivity on measure-zero boundary pieces is unnecessary. The proof should use positivity of the remaining kernel a.e. and positive measure of the interior.

Distinguish clearly:

- \(y_{1,00}>0\): enough for positivity of the **leading coefficient**;
- amplitude positivity on the box: enough for positivity of the **finite-\(n\) chart integral**.

The former does not imply the latter for arbitrary coefficient arrays.

**Priority:** prove the ratio convergence without this extra hypothesis; add finite-\(n\) positivity as a semantic corollary, not a prerequisite.

### (b) Deterministic amplitudes

Yes—**on the interpretation of §4.3 you describe**, \(\eta=\varphi c\) is deterministic, and the empirical phase is the random input. Fixed-amplitude `replaceY` maps are the correct specialisation.

Your random-amplitude theorems are a valid generalisation provided their joint convergence and measurability assumptions are explicit. Present the deterministic specialisation as the paper-facing theorem; present random amplitudes as additional formal generality.

I would avoid claiming textual fidelity to the whole section without reviewing the actual passage and its chart construction.

### (c) What comes after the ratio?

My ranking:

1. **Independent fidelity review**, concentrating first on theorem statements, normalisations and coefficient identifications.
2. **Update `grammar_lean.tex`**, from a reviewed Headline inventory.
3. **Constant/Gaussian dichotomy**, provided the Gaussian input and any nondegeneracy claims are justified.
4. **General-\(d\) product-density milestone.**

The fixed-amplitude constant-limit simplification above is small enough to include with the ratio, rather than postponing it to the broader dichotomy project.

The review should begin now in parallel if your mechanism permits. Seventy-plus new files are enough that another expansion of scope should wait.

### What to annotate

For §4.2, attach references to the statements actually represented by:

- the two-dimensional chart expansion;
- the coefficient formulas and logarithmic/nonlogarithmic slots;
- the precise remainder estimate and its uniformity on bounded coefficient sets;
- the specialisation to the smallest exponent, when used.

For §4.3, attach references to:

- weak convergence of coefficient inputs **as a hypothesis**, unless independently established;
- tightness deduced from that weak convergence;
- normalised remainder convergence in probability;
- normalised chart-integral convergence in distribution;
- joint numerator/denominator convergence;
- leading denominator positivity;
- the posterior quotient limit, once landed;
- its constant-limit simplification under fixed amplitudes.

Do not attach a “formalised” marker to an entire paragraph if it also asserts chart reduction, empirical-process convergence, global chart aggregation or Gaussianity that your referenced theorem does not prove.

Suggested compact caveat:

> **Formalised scope.** The referenced results concern the stated two-dimensional chart model under the explicit coefficient-space, amplitude and sample-size hypotheses. Convergence of the random coefficient input is assumed; tightness, remainder negligibility and the displayed chart-level limits are proved.

For the quotient:

> The quotient theorem uses totalised division and requires positivity of the limiting leading denominator. Finite-sample positivity of the chart normaliser is a separate result under positive-amplitude hypotheses.

For global claims:

> These references do not by themselves establish reduction of the full posterior to this chart or aggregation across multiple charts.

Use these caveats locally or in a shared scope note, rather than repeating a long disclaimer at every dot.

## 5. Recommended next five units

| Unit | Deliverable |
|---|---|
| **u156 SmallProbabilityModification** | Integral difference bound on a disagreement event; R1 approximation theorem. |
| **u157 PositiveDenominatorRatio** | Joint weak convergence plus a.s. positive limiting denominator implies quotient convergence, using clipped division and portmanteau. |
| **u158 FixedAmplitudeJointLimit** | Continuous `replaceY` specialisations; joint leading-coefficient map; joint normalised chart convergence from paired negligible remainders. |
| **u159 ChartPosteriorLimit** | Scale cancellation, quotient theorem, common-factor cancellation to \(y_{\varphi,00}/y_{1,00}\); finite-\(n\) positivity corollary if it fits cleanly. |
| **u160 ReviewedHeadline** | Expose the new wrappers, audit assumptions and scope, and synchronise the inventory with §4.2/§4.3 `\leanref` annotations. |

The independent review and TeX changes need not themselves be counted as Lean units. The substantive stopping point is: **a reviewed, explicitly chart-level posterior theorem, including its deterministic limit in the fixed-amplitude case, before extending dimension or probabilistic scope.**
