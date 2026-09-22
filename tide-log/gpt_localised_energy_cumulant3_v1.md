**Vote: A+B+C, staged with A+B as the firm checkpoint; defer D.** The mathematics is correct. The principal corrections are to the numerical-consistency description and the Gamma-law wording.

### 1. A and B: identities and coefficients

**The Stein consistency identity closes exactly.** Including the anchor contribution,
\[
\begin{aligned}
4c_3+\frac{3a}{\lambda^2}-\lambda c_5-\frac{15\alpha}{2\lambda^3}
&=\left(-10+\frac{35}{2}-\frac{15}{2}\right)\frac{\alpha}{\lambda^3}
 +(12+3-15)\frac a{\lambda^2}\\
&=0.
\end{aligned}
\]
Your displayed calculation yielding \(-3a/\lambda^2\) omitted the explicit \(+3a/\lambda^2\). **`locFifthCoeff` is consistent.**

The formula for \(t^4m_7\) in A is correct. Each \(t\)-multiplied remainder is bounded by the landed \(O(1/t)\) rates, and \(t^3m_5\) is bounded. This route requires **\(\gamma\ne0\)**—presumably supplied by E2’s positivity assumptions. Do not silently introduce division by \(\gamma\) if the theorem admits \(\gamma=0\).

**All seven coefficients of the \(\ell^3\) expansion are correct.** The leading third moment is \(15/8\), and
\[
\frac{15}{8}-3\frac34\frac12+2\left(\frac12\right)^3=1.
\]
Thus both B estimates follow with \(O(1/t)\) scaled errors.

For degrees \(8,\ldots,12\), **bounded \(t^4\)-scaled absolute moments suffice**. Your even envelopes and neighbour inequalities provide these eventually for \(t\ge1\). Crucially, degree seven needs the **signed** bound; replacing it by an absolute-moment bound generally loses the desired rate.

The numerical “Stein leading consistency” is **identically zero when evaluated using the exact coefficients**. Nonzero finite-\(t\) values must be labelled as a residual using scaled moments, not as values of that coefficient identity.

### 2. C: exact differentiation chain

Correct. Write \(M_j(t)=\langle\ell^j\rangle_t\). Then
\[
M_1'=-(M_2-M_1^2),\qquad
M_2'=-(M_3-M_1M_2),
\]
so
\[
(M_2-M_1^2)'=-M_3+3M_1M_2-2M_1^3=-\kappa_3.
\]
Consequently,
\[
f''(t)=\sum_i\kappa_{3,i}(t),\qquad
|t^3f''(t)-d|\le K/t
\]
eventually.

The necessary qualifications:

- Keep the localiser strength, anchor, frame, and potential parameters **fixed in \(t\)**.
- Supply the differentiation theorem’s domination/integrability hypotheses; pointwise integrability alone is not generally enough to differentiate under the integral.
- For `deriv (deriv f) t`, use `deriv f = −Var` **locally**, not merely at \(t\). The identity throughout \((0,\infty)\) gives exactly this at every \(t>0\).
- Finite sums introduce no further analytic issue.

### 3. Wording and Gamma interpretation

**Change “first three temperature derivatives of the localised energy.”** These are the energy expectation and its **first two derivatives**, or the first three derivatives of \(-\log Z_{\rm loc}\).

Also say **cumulants**, not moments. For Gamma shape \(k\), **rate** \(t\), the first three cumulants are
\[
k/t,\qquad k/t^2,\qquad 2k/t^3.
\]

Suggested wording:

> The LLC \(d/2\) governs the localised mean energy and its first two temperature derivatives: \(t\langle L\rangle\to d/2\), \(-t^2\partial_t\langle L\rangle\to d/2\), and \(t^3\partial_t^2\langle L\rangle\to d\). These match the first three cumulants of a Gamma law with shape \(d/2\) and rate \(t\).

Worth stating, but **these estimates alone do not establish convergence in law**. Until D is formalised, describe the last exact quantity as \(\sum_i\kappa_{3,i}\), rather than claiming a landed direct multidimensional cumulant identity.

### 4. Lean route and priorities

- **A:** Prove the coefficient cancellation separately with `field_simp`/`ring`, then rewrite the scaled recursion into remainder form. Gather one eventual threshold including \(t\ge1\).
- **B:** Separate the pointwise polynomial identity from expectation linearity and from bounds. Establish monomial integrability first. A small reusable lemma that products of bounded \(O(1/t)\)-accurate quantities retain that accuracy will simplify cumulant assembly.
- **C:** Prefer **one-dimensional derivative identities for \(M_1,M_2\)** if existing infrastructure permits; then differentiate the landed finite-sum variance splitting. This can avoid repeating frame independence reductions. Otherwise the proposed frame-probe route is sound.
- Build `HasDerivAt` results for coordinate variances and their finite sum first; convert to nested `deriv` only at the final interface using local equality.

**Best target this tide:** the exact second-derivative identity plus its \(d/t^3\) leading law. D is a useful later identification, not a prerequisite. The next substantial asymptotic target remains second-order energy variance, requiring the missing second-order fifth/sixth moments.