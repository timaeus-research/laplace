## Overall verdict: **Qualified pass**

Stage 4 faithfully extends the **asymptotic-expansion and remainder-bound conclusions** of Stage 3 to absolutely summable coefficient families on the unit cube. The stability estimate, preservation of the constant phase, and fixed-\(N\) limit argument are mathematically sound as stated.

Two qualifications prevent an unqualified claim that the full paper theorem has been formalised:

1. **The holomorphic-data-to-coefficient-family bridge is not formalised.** `AbsSummable` is implied by the paper’s hypothesis at \(b=1\), but is not an equivalent formulation of it.
2. **The family coefficients are proved to be convergent limits, not explicitly identified with absolutely convergent Taylor/fluctuation series.** This is sufficient for the expansion itself, but does not by itself formalise the paper’s additional coefficient-representation assertion.

This is a statement-level review, using the supplied descriptions of omitted definitions. I have not run Lean or audited proofs.

## Per-unit verdicts

| Unit | Verdict | Assessment |
|---|---|---|
| **241 — `MonoRepPerm`** | **Pass mathematically; excerpt correction needed** | Permutation invariance, append identities, and the power-difference bound are appropriate for uncollected monomial lists. The supplied excerpt contains a duplicate `pow_append_perm` declaration and an unfinished first proof block. |
| **242 — `CoeffStability`** | **Pass** | The moment shift, differentiated phase-series identity, and appended-perturbation estimate have the correct factors and hypotheses. The estimate is exactly suitable for nested truncations. |
| **243 — `CoeffFamily`** | **Pass** | Box truncations exhaust the multi-indices, preserve the constant coefficient, and converge uniformly on the closed cube through the tail-mass bound. Unweighted \(\ell^1\) is the correct sufficient norm at \(b=1\). |
| **244 — `FamilyPhaseIntegral`** | **Pass** | Convergence of the integrals at fixed \(N\ge0\), \(\beta\ge0\) is justified by the stated evaluation bounds and a fixed-\(N\) integrable majorant. No uniformity as \(N\to\infty\) is needed here. |
| **245 — `FamilySpectralCoeff`** | **Qualified pass** | Cauchy convergence, coefficient limits, support preservation, and convergence of finite spectral sums are the right conclusions. They do not yet state an absolutely convergent family-series representation. |
| **246 — `UniformCutoffConst`** | **Pass** | The distinction between monotonicity in \(b\) and in \(|b|\) is correctly handled by using \(|a|+B\). The constant is independent of truncation level and \(N\). |
| **247 — `FamilyTaylorTree`** | **Qualified pass** | Gives the desired cutoff-independent expansion, candidate exponents, and logarithmic degree bound for family data. The qualification concerns the unformalised analytic bridge and coefficient-series identification, not the limiting remainder argument. |

## 1. Limit-defined coefficients versus the paper’s series

### The definition is legitimate

Defining
\[
A_{\mu,j}(c_\xi,c_\eta)
=\lim_{m\to\infty}A_{\mu,j}(\operatorname{trunc}_m c_\xi,
                            \operatorname{trunc}_m c_\eta)
\]
is a faithful way to **construct the asymptotic coefficients**. An explicit series need not be the definition.

Here, the relevant safeguards are present:

- `cauchySeq_truncCoeff` and `tendsto_truncCoeff` establish an actual limit under the hypotheses.
- The definition does not depend on the cutoff \(L\).
- Polynomial support restrictions pass to the limit.
- The same coefficients occur in the remainder theorem for every positive cutoff.

Thus `limUnder` is not being used as an unsupported totalised substitute for convergence.

### What is not established by convergence alone

A convergent sequence of truncation coefficients does **not by itself prove** that the natural Taylor/fluctuation coefficient series is absolutely convergent. It also does not explicitly identify the result with a particular convolution formula.

The missing assertion is structural, not a defect in the coefficient values or in the expansion theorem.

A natural additional theorem would retain the current definition and identify it with a series. Schematically, set
\[
a=c_\xi(0),\qquad
J(0)=0,\quad J(\gamma)=c_\xi(\gamma)\quad(\gamma\ne0),
\]
and let
\[
d_p=c_\eta*J^{*p}.
\]
Using the Stage 3 singleton coefficient kernel \(T_{\mu,j}(p,\gamma;a)\), the intended formula is of the form
\[
A_{\mu,j}
=\sum_{p\ge0}\frac{\beta^p}{p!}
   \sum_\gamma d_p(\gamma)\,T_{\mu,j}(p,\gamma;a),
\]
with the precise normalisation inherited from Stage 3.

The expected absolute-convergence argument is straightforward in principle:
\[
\|d_p\|_1\le \operatorname{mass}(c_\eta)\,
                   \operatorname{mass}(J)^p,
\]
followed by the Stage 3 kernel majorant and the phase-series summation identity. For \(\mu>0\), this leads to a bound involving
\[
\operatorname{mass}(c_\eta)\,
M_{\mu,n,0}\bigl(a+\operatorname{mass}(J)\bigr).
\]

**Recommendation:** Do not replace the limit definition. Add an absolute-summability and identification theorem if the hand-off claims the paper’s coefficient-series assertion. Otherwise, explicitly mark that assertion as not yet formalised.

The derivative wording also requires the identification
\[
c_\gamma=\frac{\partial^\gamma f(0)}{\gamma!}.
\]
For the paper’s analytic inputs, this belongs naturally in the analytic bridge.

## 2. Stability estimate and the constant phase

### Moment shift: correct

For \(t>0\),
\[
t^{\nu-1}(\sqrt t)^{p+1}
=t^{(\nu+1/2)-1}(\sqrt t)^p.
\]
Hence
\[
M_{\nu,r,p+1}(a)=M_{\nu+1/2,r,p}(a).
\]
The shift is \(+1/2\), and the logarithmic order \(r\) is unchanged.

Likewise,
\[
\sum_{p\ge0}\frac{\beta^p}{p!}pB^{p-1}(\sqrt t)^p
=\beta\sqrt t\,e^{\beta B\sqrt t},
\]
which yields the stated \(\beta M_{\nu+1/2,r,0}(a+B)\). The assumptions \(\beta>0,\nu>0,B\ge0\) are appropriate.

The \(p=0\) term vanishes because of the factor \(p\). The \(B=0\) endpoint is also correct: the \(p=1\) term survives.

### Perturbation bound: correct

The condition
\[
B\ge\|J\|_1+\|\Delta\|_1
\]
controls both the perturbed power and its difference from the original power. Using only \(B\ge\|J\|_1\) would not suffice.

The amplitude perturbation is evaluated against the **full perturbed phase power**, so the displayed bound includes mixed phase/amplitude perturbations; it does not omit them. Also, \(E,B\ge0\) follow from the displayed mass inequalities.

One wording qualification is important: this is an **appended-list stability estimate with a fixed constant phase**, not a theorem about arbitrary pairs of polynomial presentations measured by their functional difference. That restricted statement is entirely adequate for the truncation argument.

### Same constant phase: legitimately satisfied

Every box contains the zero multi-index, so
\[
\operatorname{eval}(\operatorname{truncList}c\,m)(0)=c(0)
\]
for every \(m\), including \(m=0\).

New indices between nested boxes are nonconstant. Consequently, successive phase truncations have the same constant phase and differ in their fluctuation lists by precisely the permitted appended perturbation, up to permutation.

For `cauchySeq_truncCoeff` at \(\mu\le0\), the positive-\(\mu\) stability estimate is not applicable. The intended route is nevertheless sound: all candidates are positive when \(h_i\ge0\), \(k_i>0\), so the inherited polynomial off-candidate vanishing makes those sequences identically zero.

## 3. Fixed-\(N\) limit and the uniform constant

The limit passage is sound.

For each fixed \(N\ge1\):

1. The polynomial integrals converge to `familyPhaseIntegral`.
2. The finite spectral sums converge to `familySpectralSum`.
3. Every truncation satisfies the same remainder bound, with
   \[
   a=c_\xi(0),\qquad E=\operatorname{mass}(c_\eta),
   \qquad B=\operatorname{mass}(c_\xi).
   \]
4. Continuity of subtraction and absolute value passes the inequality to the limit.

There is **no interchange of \(m\to\infty\) with \(N\to\infty\)**. Establishing the bound separately for each \(N\), with one constant independent of \(N\), produces the claimed uniform inequality.

The use of the full phase mass for \(B\) is conservative but valid; it need not exclude the constant coefficient.

### Monotonicity and the absolute value

Write \(s=\|\operatorname{fluct}\xi\|_1\le B\). Then
\[
a+s\le |a|+B,\qquad |a+s|\le |a|+B.
\]
The first inequality supports monotonicity of \(M\) in its phase parameter. The second supports monotonicity of `tailConst` in the absolute value of that parameter.

Thus \(|a|+B\) correctly controls both components of the cutoff constant. Replacing it indiscriminately by \(a+B\) would not justify the tail-constant comparison when \(a<0\).

## 4. Exact relationship to the paper’s analytic hypothesis

`AbsSummable` is a **sufficient, strictly weaker assumption on the power-series data**, not an exact restatement of holomorphic extension to a polydisc of radius \(R>1\).

An absolutely summable family defines a continuous function on the closed unit cube and a holomorphic power series on the open unit polydisc. It need not extend holomorphically across the unit boundary. For example,
\[
\sum_{m\ge1}\frac{z^m}{m^2}
\]
has summable coefficients but its derivative is singular at \(z=1\).

### Required Cauchy-estimate bridge

For each paper input \(f\), the bridge should prove:

- Given a holomorphic extension \(F\) to \(D_R\), \(R>1\), agreeing with the real-valued input on the cube, define its Taylor coefficients at zero.
- These coefficients are real and satisfy
  \[
  c_\gamma=\frac{\partial^\gamma f(0)}{\gamma!}.
  \]
- Choose \(1<r<R\). If
  \[
  M_r=\sup_{\lvert z_i\rvert\le r}|F(z)|,
  \]
  then Cauchy estimates give
  \[
  |c_\gamma|\le M_r r^{-|\gamma|}.
  \]
- Therefore
  \[
  \sum_\gamma|c_\gamma|
  \le M_r(1-r^{-1})^{-d}<\infty.
  \]
- The Taylor series agrees with \(f\) on the entire closed unit cube, with absolute and uniform convergence.
- Substitution of these evaluation identities identifies the paper’s integral with `familyPhaseIntegral`, modulo the measure-zero distinction between the closed cube and the half-open integration box.

This must be done for both \(\xi\) and \(\eta\).

The general-\(b\) rescaling remains outside the displayed Stage 4 statements.

## 5. Expansion form and hand-off wording

The logarithmic degree is correct:
\[
j\in\{0,\ldots,n\},\qquad d=n+1,
\]
so \(\deg P_\mu\le d-1\). The corollary’s indexing is
\[
C_{\mu,m}=A_{\mu,m-1},\qquad 1\le m\le d.
\]

Off-candidate vanishing permits taking \(\Lambda^*\) to be the subset of candidates with a nonzero coefficient polynomial. Allowing zero coefficient polynomials in the displayed candidate sum is harmless.

The little-\(o\) statement is correctly restricted to \(L'<L\). A cutoff strictly below \(L\) does not generally give \(o(N^{-L})\), because an omitted term at exponent \(L\) may be nonzero.

### Suggested hand-off text

> Stage 4 proves a quantitative asymptotic expansion for standard integrals on the unit box whose phase and amplitude are represented by absolutely summable real monomial coefficient families. The coefficients are cutoff-independent limits of polynomial-truncation coefficients, vanish outside the paper’s candidate exponent set, and give logarithmic degree at most \(d-1\).
>
> The paper’s holomorphic-extension hypothesis implies these coefficient-family assumptions by Cauchy estimates, but that bridge is not formalised here. An explicit identification of the family coefficients with absolutely convergent Taylor/fluctuation series is also not yet formalised. The existing restrictions on dimension, \(h\), \(k\), and \(\beta\) remain in force.

Avoid saying simply “the full analytic Taylor-tree theorem is formalised” without these qualifications.

## Should-fix before author hand-off

1. **Resolve the coefficient-series claim.** Either add the absolute-convergence/identification theorem or expressly exclude that part of the paper’s conclusion from the formalised claim.
2. **State the analytic bridge precisely and label it unformalised.** Do not describe `AbsSummable` as equivalent to extension to \(D_R\), \(R>1\).
3. **Correct the duplicate/incomplete `pow_append_perm` excerpt.** If this reflects the actual source rather than a paste artifact, it needs source cleanup; no mathematical redesign is indicated.
4. **Use accurate scope language:** unit box, \(d=n+1\), \(h_i\in\mathbb N\), \(k_i>0\), \(\beta>0\), and family-data inputs.
5. **Describe u242 as appended-perturbation stability with fixed constant phase**, rather than unrestricted polynomial Lipschitz stability.
6. **Document the paper correspondence** \(P_\mu(X)=\sum_{j=0}^n A_{\mu,j}X^j\), \(C_{\mu,m}=A_{\mu,m-1}\), and the candidate-lattice containment inherited from Stage 3.

Useful follow-ups, but not blockers for the qualified family-expansion claim, include polynomial compatibility and independence from the particular exhausting truncation scheme.

## Sanity checks performed

- Checked the \(+1/2\) moment shift and the factor \(\beta\) in the differentiated phase series.
- Checked \(p=0\) and \(B=0\) endpoints of the power-difference/series formulas.
- Checked that box truncations preserve the constant phase from level zero onward.
- Checked that amplitude perturbations include their interaction with the perturbed phase.
- Checked positivity of candidate exponents and the route for \(\mu\le0\).
- Checked both monotonicity requirements, especially negative constant phase.
- Checked independence of the cutoff bound from truncation level and \(N\).
- Checked \(d=1\): no logarithmic powers, and constant-phase monomial amplitudes yield exponents \((h+r+1)/(2k)\), as required.
- Checked the distinction between \(O(N^{-L}\log^{d-1}N)\) and little-\(o\) at a strictly smaller exponent.
- Reviewed the **reported**, not independently rerun, numerical test: for \(d=1\), \(L=5/2\), scaling the remainder by \(N^{5/2}\) is appropriate and may approach a nonzero omitted coefficient. The reported values are consistent with that behaviour, but do not test absolute convergence, logarithmic multiplicities, or the analytic bridge.
