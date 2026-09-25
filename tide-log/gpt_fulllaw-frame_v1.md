**A–D are correct under the standard positivity and stability assumptions**, with two important distinctions: algebraic uniqueness is weaker than dynamical stability, and the limiting quantities \(\alpha_j,s_j,q_j\) must not be substituted for their finite-\(t\) counterparts when asserting finite-\(t\) stability.

## 1. Exact law, denominator conditions, and uniqueness

Assume real matrices, an orthogonal \(U\), and
\[
A=U\operatorname{diag}(a)U^\top,\qquad
D_i=U\operatorname{diag}(d_i)U^\top.
\]
For the trace formulas, also assume \(H=U\operatorname{diag}(\lambda)U^\top\).

### A: the off-diagonal formula is correct

Writing \(b_{kl}=\sum_i d_{ik}d_{il}\), conjugation gives
\[
\widehat{AXA^\top}_{kl}=a_ka_l\widehat X_{kl},
\qquad
\widehat{B(X)}_{kl}=b_{kl}\widehat X_{kl}.
\]
Thus
\[
\widehat\Sigma_{kl}
=\frac{\widehat N_{kl}}{1-a_ka_l-cb_{kl}}
\]
is exactly right, including off-diagonal entries.

If every denominator is nonzero, this is the **unique fixed point among all matrices**, without any norm hypothesis. I would state that directly, then give identification with the existing `fullFixed` as a corollary under its contraction assumptions.

Nonzero denominators alone do **not** guarantee that this fixed point is PSD or that iteration converges. Those require a stability/positivity statement.

### A clean sufficient condition—and an exact stability criterion

For \(c\ge0\), define
\[
r_j=a_j^2+cv_j,\qquad r=\max_j r_j.
\]
The cleanest sufficient condition is
\[
\boxed{r<1.}
\]
Indeed, \(m_{kl}=a_ka_l+cb_{kl}\) is the Gram matrix of the vectors
\[
(a_j,\sqrt c\,d_{1j},\ldots,\sqrt c\,d_{nj}),
\]
so
\[
|m_{kl}|\le\sqrt{r_kr_l}\le r<1.
\]
Consequently every denominator \(1-m_{kl}\) is positive, with the uniform lower bound \(1-r\).

Your proposed Cauchy–Schwarz argument also works. At the same time/scaling, set
\[
s_j(a)=1-a_j^2,\qquad q_j(a)=cv_j/s_j(a).
\]
Then \(|a_j|<1\) and \(q_j(a)<1\) imply \(r_j<1\). The inequality
\[
\sqrt{(1-a_k^2)(1-a_l^2)}\le1-a_ka_l
\]
follows by squaring: the difference of the squares is \((a_k-a_l)^2\).

There is a useful stronger result here. For the homogeneous operator
\[
T(X)=AXA^\top+cB(X),
\]
the matrix units in the \(U\)-frame are eigenvectors with eigenvalues \(m_{kl}\). Hence, for \(c\ge0\),
\[
\rho(T)=\max_{kl}|m_{kl}|=\max_j(a_j^2+cv_j).
\]
Thus \(r<1\) is the **exact convergence criterion for iteration from every initial matrix**, not merely a convenient sufficient bound. It is also a Frobenius-norm contraction criterion, potentially much less restrictive than the existing \(\ell^\infty\)-based bound.

For \(N\succeq0\), stability gives
\[
\Sigma=\sum_{n\ge0}T^n(N)\succeq0.
\]

### B: correct

The trace only sees diagonal frame entries:
\[
\operatorname{tr}(H\Sigma)
=\sum_j\frac{\lambda_j\widehat N_{jj}}
 {1-a_j^2-cv_j}.
\]
Since \(\widehat N=2hI+h^2t^2\widehat C\), the displayed minibatch LLC formula follows exactly.

### C: correct with explicit anchored assumptions

A clean assumption package is:

- \(t\to+\infty\), \(\eta>0\), and \(g\) fixed;
- \(U,\lambda,C,d,c\) fixed, with \(c\ge0\);
- \(0<\eta\lambda_j<2\), so \(s_j=1-\alpha_j^2>0\);
- \(cv_j<s_j\) for every \(j\).

Then
\[
a_j(t)=\alpha_j-\frac{\eta g}{t},
\qquad
1-a_j(t)^2-cv_j\longrightarrow s_j-cv_j>0.
\]
Therefore finite-\(t\) stability holds **eventually**, regardless of whether the old \(\ell^\infty\) contraction hypothesis holds.

Directly,
\[
\frac{\mathrm{LLC}_{\rm full}-\mathrm{LLC}^{\rm ULA}}t
=
\frac12\sum_j\lambda_j
\left[
\frac{2\eta/t+\eta^2\widehat C_{jj}}
 {1-a_j(t)^2-cv_j}
-\frac{2\eta/t}{1-a_j(t)^2}
\right],
\]
which converges to the stated \(\sigma_{\rm full}\).

Two wording corrections:

- The two additive-noise contributions to the unnormalised LLC are \(O(1)\).
- The minibatch contribution is \(O(t)\), and is \(\Theta(t)\) only for an excited mode, \(\widehat C_{jj}>0\).

If C is stated specifically using the existing `fullFixed`, retain its domain hypotheses or first extend the fixed-point construction to this sharper commuting stability region.

## 2. Full slope, first-order deficit, and R₁

Yes: this is precisely the full slope I had in mind:
\[
\boxed{\sigma_{\rm full}=\sum_j\frac{w_j}{1-q_j}.}
\]

D is also correct:
\[
\sigma_{\rm mb}=\sum_jw_j,\qquad
\sigma_1=\sum_jw_jq_j.
\]
For \(w_j\ge0\) and \(0\le q_j<1\),
\[
\boxed{
\sigma_{\rm full}-(\sigma_{\rm mb}+\sigma_1)
=\sum_j\frac{w_jq_j^2}{1-q_j}\ge0.
}
\]
This is an **exact first-order truncation deficit**, not just an asymptotic bound in small \(c\). The approximation is first order in the feedback strength \(c\), with other data fixed.

“Understates” should mean “weakly underestimates”: strict inequality requires at least one mode with \(w_j>0\) and \(q_j>0\).

Yes, record the amplification ratio, provided \(\sigma_{\rm mb}>0\):
\[
\frac{\sigma_{\rm full}}{\sigma_{\rm mb}}
=\sum_j\frac{w_j}{\sum_kw_k}\frac1{1-q_j}.
\]
It is a weighted average of the modal amplification factors. Call it the exact version of R₁ **if R₁’s baseline is indeed the constant-noise slope**; otherwise state the baseline explicitly.

Near \(q_j=1\), amplification diverges only if that mode carries nonvanishing weight. A critical but unexcited mode need not make the LLC slope diverge.

## 3. Strongest reachable bundle

I would prioritise **A–D plus the elementary denominator lemma**:

1. Entrywise action of \(T\).
2. Explicit fixed point and uniqueness from nonzero denominators.
3. Denominator positivity from \(a_j^2+cv_j<1\).
4. Identification with `fullFixed` under its existing hypotheses.
5. Exact trace/LLC formula.
6. Anchored slope.
7. Exact deficit, inequality, and optional amplification ratio.

This is a coherent result: exact solution → observable → limit → quantified diagnostic error. Given the existing frame and limit infrastructure, it is a stronger target than branching into noncommuting theory.

The best nearby addition is the **sharp commuting stability criterion**. If spectral-radius formalisation is expensive, record the Gram bound and a frame-coordinate contraction theorem instead; the mathematical content is largely the same.

For blow-up, distinguish:

- \(r_j\uparrow1\): the full resolvent becomes singular;
- a particular covariance/LLC observable diverges only if its numerator observes the critical mode.

For a subsequent noncommuting tide, a natural sufficient condition is
\[
T(I)=AA^\top+c\sum_iD_iD_i^\top\preceq rI,\qquad r<1.
\]
Positivity then gives an operator-norm contraction on symmetric matrices and a PSD Neumann-series fixed point. This survives without commutativity. A literal Schur-multiplier reduction generally does not: noncommuting noise couples frame entries.

## 4. Suggested staged E8 paragraph

> In the simultaneously diagonalizable case, the multiplicative-noise feedback admits an exact modewise solution \(\leanref{commuting_full_fixed}\), with stability condition \(a_j^2+c\sum_i d_{ij}^2<1\) in every mode. Under anchored scaling, a fixed common eigenframe, \(C\succeq0\), \(c\ge0\), and strict limiting stability \(0\le q_j<1\), the full inflation slope is \(\sigma_{\rm full}=\sum_jw_j/(1-q_j)\) \(\leanref{commuting_full_slope}\). The constant-noise plus first-order diagnostic is therefore a lower bound, with exact deficit \(\sum_jw_jq_j^2/(1-q_j)\) \(\leanref{commuting_slope_deficit}\). This isolates a mechanism by which first-order diagnostics can miss substantial amplification near a stability boundary in an excited mode; it is an exact result for the commuting linear-response model, not a general claim about noncommuting samplers or nonlinear stationary laws.

The `\leanref` names above are proposed placeholders.

**Vote: formalise A–D, including direct uniqueness and the \(a_j^2+cv_j<1\) denominator lemma; add the ratio if cheap, and defer noncommuting extensions.**