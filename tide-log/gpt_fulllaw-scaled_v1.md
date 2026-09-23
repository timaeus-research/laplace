**Vote: approve A–D under the stable, positive-curvature assumptions, with qualifications about nonzero slopes and the distinction between a first-order lower bound and the full correction.**

## 1. A–D and the scaling reconciliation

Assume a fixed finite dimension, \(H=Q\operatorname{diag}(\lambda_j)Q^\top\) with \(\lambda_j>0\), fixed \(g,C,D_i\), \(C\succeq0\), \(c\ge0\), and
\[
0<\eta\lambda_j<2\qquad\text{for every }j.
\]
Then
\[
\rho_j=1-\eta\lambda_j-\eta g/t\longrightarrow\alpha_j,
\qquad
s_j:=1-\alpha_j^2=\eta\lambda_j(2-\eta\lambda_j)>0.
\]

- **A is correct:** entrywise convergence implies matrix convergence in finite dimension:
  \[
  \Sigma^{mb}(t)\to\Sigma_\infty,\qquad
  \widehat S_{\infty,kl}=\frac{\eta^2\widehat C_{kl}}{1-\alpha_k\alpha_l}.
  \]

- **B is correct:** \(B\) is a fixed continuous linear map, so the first-order correction, denoted \(\mathrm{corr}_1(t)\), satisfies
  \[
  \frac{\mathrm{corr}_1(t)}t\to
  \sigma_1=\frac c2\sum_j\frac{\lambda_j\bigl(Q^\top B(\Sigma_\infty)Q\bigr)_{jj}}{s_j}.
  \]

- **C is correct.** Directly,
  \[
  \frac{LLC^{mb}-LLC^{ULA}}t
  =\frac{ht^2}{4}\sum_j\frac{\lambda_j\widehat C_{jj}}{p_j\kappa_j}
  \longrightarrow
  \frac{\eta}{4}\sum_j\frac{\widehat C_{jj}}{1-\eta\lambda_j/2}.
  \]

- **D follows by addition.**

### Two necessary qualifications

**Fixed \(c\):** the candidates explicitly stipulate this. If the E8 coefficient has the form \(c=\gamma h^2t^2\), with fixed sampling factor \(\gamma\), then indeed \(c=\gamma\eta^2\) is \(t\)-independent. But \(h=\eta/t\) alone does not establish that for an unspecified coefficient: the note should display the definition of \(c\).

**Finite does not automatically mean nonzero.** The limit of each diagonal entry of \(\widehat B(\Sigma^{mb})\) is finite, but it can vanish. In fact,
\[
B(\Sigma_\infty)
=\sum_i(D_i\Sigma_\infty^{1/2})(D_i\Sigma_\infty^{1/2})^\top.
\]
Thus, for \(c>0\), \(\sigma_1>0\) precisely when some \(D_i\Sigma_\infty^{1/2}\ne0\). Accordingly, the first-order term is always \(O(t)\), and is **\(\Theta(t)\) when \(\sigma_1>0\)**.

Positive curvature and strict step stability matter: zero-curvature directions or \(\eta\lambda_j=2\) invalidate the displayed denominator argument.

### Reconciliation with tides 107/114

There is no contradiction. The identity
\[
1-\rho_j^2=hp_j(2-hp_j)
\]
has different asymptotics in different regimes:

- With \(p_j\) fixed and \(h\to0\), it is \(\Theta(h)\).
- With \(p_j=t\lambda_j+g\) and \(h=\eta/t\), it tends to \(s_j>0\).

So the **additive covariance resolvent** is \(O(1)\) along the anchored scaling, not \(O(1/h)\).

However, this does **not** by itself establish stability of the full multiplicative-noise covariance law. Its limiting operator is
\[
\mathcal T_\infty(X)=A_\infty X A_\infty^\top+cB(X),
\qquad
A_\infty=Q\operatorname{diag}(\alpha_j)Q^\top.
\]
A uniform full-law stability margin requires a separate condition, such as \(\operatorname{spr}(\mathcal T_\infty)<1\). If the earlier \(L\) concerns that full operator, its gap must be checked separately.

## 2. Diagnostic ratio and commuting simplification

**Yes:** when \(\sigma_{mb}>0\),
\[
R_1=\frac{\sigma_1}{\sigma_{mb}}
\]
is a useful measure of the **first-order Hessian-fluctuation contribution relative to constant gradient-noise inflation**.

It is not generally the ratio of the *full* Hessian correction to that inflation. At fixed \(c\), higher-order multiplicative-noise terms can also be \(\Theta(t)\); increasing \(t\) does not suppress them.

If the \(D_i\) are diagonal in the chosen eigenframe, write
\[
v_j=\sum_i\widehat d_{ij}^{\,2}.
\]
Your formula is correct:
\[
\sigma_1
=\frac c2\sum_j
\frac{\lambda_jv_j\eta^2\widehat C_{jj}}{(1-\alpha_j^2)^2}
=\boxed{\frac c2\sum_j
\frac{v_j\widehat C_{jj}}{\lambda_j(2-\eta\lambda_j)^2}}.
\]

An especially useful interpretation is
\[
w_j:=\frac{\eta\widehat C_{jj}}{2(2-\eta\lambda_j)},
\qquad
q_j:=\frac{cv_j}{\eta\lambda_j(2-\eta\lambda_j)}.
\]
Then
\[
\sigma_{mb}=\sum_jw_j,\qquad
\sigma_1=\sum_jw_jq_j,\qquad
R_1=\frac{\sum_jw_jq_j}{\sum_jw_j}.
\]
Thus the ratio is a noise-weighted average of the modewise feedback strengths \(q_j\).

For the stated full covariance recursion, when stable, the corresponding full slope in this diagonal setting is
\[
\sum_j\frac{w_j}{1-q_j}.
\]
This makes clear why the first-order diagnostic can understate the effect near \(q_j=1\).

One technical caveat: commuting with \(H\) alone does not ensure diagonality in a common frame when \(H\) has repeated eigenvalues. Your “sharing the eigenframe” assumption is the appropriate stronger condition.

## 3. Suggested Summary 2 wording

**Add the observation, but explicitly call it first-order.** For example:

> At fixed relative step \(h=\eta/t\), constant gradient noise produces an asymptotically linear LLC inflation, with slope \(\sigma_{mb}\). The first-order Hessian-fluctuation term also grows linearly when nonzero, with slope \(\sigma_1\). For the stable full law, their sum gives an asymptotic lower bound on the inflation slope; higher-order Hessian-fluctuation contributions need not be negligible.

More precisely, whenever the full stationary law exists for all sufficiently large \(t\), tide 115 gives
\[
\liminf_{t\to\infty}
\frac{LLC_{\rm full}-LLC^{ULA}}t
\ge \sigma_{mb}+\sigma_1.
\]

Also retain the original \(ht^2\operatorname{tr}(C_g)/(2d)\) statement only with its existing normalization and approximation assumptions: fixed relative step does not make the finite-step factors \(1-\eta\lambda_j/2\) tend to one.

**Final vote: yes to A–D and to adding the diagnostic; revise “the Hessian-fluctuation correction has slope \(\sigma_1\)” to “the first-order Hessian-fluctuation term has slope \(\sigma_1\).”**