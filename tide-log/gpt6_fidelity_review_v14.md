## Verdict

**214–215 are statement-level clean under the supplied conventions.** Headline XVIII proves the conditional weak-limit theorem for the assembled quotient. It does **not itself state a full stochastic remainder expansion**. Proofs and the paper’s chart-decomposition identity are outside this review.

### 1. Unit 214

- **Deterministic convergence ⇒ convergence in measure:** correct under the ambient probability-measure assumptions.
- **Finite vector of in-measure-null sequences:** correct. A finite union bound controls the sup-norm deviation; independence and component measurability are not needed for this implication.
- **Slutsky pairing with deterministic sequences:** correct. The stated topology/Borel assumptions support the distributional pairing; no independence is required.
- **Joint vector Headline XVI:** correct. Joint input convergence, continuity of the vector of limit functionals, and a finite vector of in-measure-null approximation errors give the conclusion. Merely having marginal phase convergence would not suffice.
  - Fixed amplitudes may be signed.
  - `Nseq ≥ 0` is consistent with the inherited chart theorem; convergence to infinity makes any problematic small scales irrelevant asymptotically.
  - The actual phase spaces use cubes of dimension **`d a + 1`**.

The **pair-vector theorem in 215** is likewise correct: numerator and denominator use the same phase on each chart and converge **jointly**, rather than by an invalid pairing of marginal limits.

### 2. Headline XVIII

**Hypotheses and conclusion match the intended finite-sum quotient theorem.**

- `hmin` and `hatt` identify the attained chart minimum; hence each multiplicity is positive.
- Finite nonempty charts guarantee a nonempty selected set: first minimize \(p_a=2l_a\), then maximize multiplicity.
- Deterministic scale ratios converge to precisely those selection indicators.
- Joint convergence plus Slutsky gives the normalized assembled numerator/denominator pair.
- `Nseq > 1` makes the common power/log scale strictly positive, permitting exact cancellation.

**Selected denominator:** it is actually positive **for every** target outcome, not merely almost surely. Every selected term has strictly positive amplitude \(c_a\), hence positive `limChart`; at least one selected chart exists. No uniform deterministic lower bound is required for the quotient limit theorem.

Only \(c_a\), **not** \(\varphi_a\), must be positive.

**“Conditional on the chart decomposition” is honest** if it means the identification of the posterior with these chart sums is assumed externally—not probabilistic conditioning.

### 3. Scope relative to the paper

No missing hypothesis for the displayed theorem, but the application still requires:

- **Weights:** deterministic strictly positive continuous chart weights can be absorbed into \(c_a\). Nonnegative cutoffs that vanish, signed assembly weights, or random weights are not automatically covered. Vanishing amplitudes can also invalidate positivity of a selected leading coefficient.
- **Remainders:** an approximate chart decomposition requires control of omitted numerator and denominator contributions, ordinarily \(o_P(S_*)\) for the common leading scale \(S_*\).
- **Expansion versus weak limit:** the headline states convergence in distribution. It does not explicitly state a same-source expansion using coefficients evaluated at \(X_n\), with an \(o_P(1)\) normalized error.
- **Dependence:** arbitrary dependence across charts is allowed. Common empirical phases must retain their induced joint law; replacing them by independent copies generally changes the answer. Neither independence nor equality of chart phases is assumed.

### 4. Mirror prose

Two adjustments:

1. Replace \([0,1]^{d_a}\) by **\([0,1]^{d_a+1}\)** under the stated dimension-minus-one convention.
2. Replace “the leading-order stochastic expectation expansion” by **“the weak-limit conclusion for the leading-order stochastic expectation”**, unless a separate remainder statement is explicitly referenced.

Suggested ending:

> …the quotient converges in distribution to the ratio of the selected leading-coefficient sums—the weak-limit conclusion for the leading-order stochastic expectation, assuming the stated chart decomposition and joint convergence of the empirical phases.

### 5. Two-chart sanity check

Take two identical chart geometries, so both are selected. Let
\[
c_1=1,\quad c_2=2,\qquad \varphi_1=1,\quad\varphi_2=3.
\]
Writing \(A_a=\operatorname{phaseCoeff}(Z^a,1)>0\), amplitude linearity gives
\[
R_\infty=\frac{A_1+6A_2}{A_1+2A_2}.
\]
For identical phases, \(A_1=A_2\), giving \(7/3\). Otherwise the joint phase law matters. If chart 2 instead has larger exponent, only chart 1 survives and the limit is \(1\).

### Should-fix vs cosmetic

- **Should fix:** mirror dimension; unqualified identification of weak convergence with a full stochastic expansion; any application silently ignoring cutoff weights or remainders.
- **Cosmetic:** say “positive everywhere, hence a.s.”; clarify that “conditional” means “assuming.”
- **No mathematical statement correction identified in 214–215.**
