**Vote: formalise A–D now, with B as the reusable core theorem and C–D as its payoff.** E is a good cheap addition if the rational-function inequalities are straightforward in the existing library. Defer the correlated-average theorem, but record its exact autocovariance formula in the note.

The main conclusions are correct. The important qualifications are:
- B needs control of surviving initial-condition memory, not merely \(k\to\infty\), in general.
- The proposed harmonic centre mixes scaled and unscaled terms.
- “Single-draw \(O(1)\) accuracy” should not suggest consistency of the scaled LLC estimator.

## 1. Correctness of A–E and the choice of centre

Write
\[
\alpha_i=1-\eta\lambda_i,\qquad
a_i=1-\eta\lambda_i/2>0,
\]
and take \(t\to+\infty\). All finite-temperature stability assertions can be made **eventually in \(t\)**.

### A: correct

For the real-valued quadratic statistic under the normalised tilted Gaussian,
\[
\mathbb E[(q-a)^2]
=\mathbb E[q^2]-(\mathbb E q)^2+(\mathbb E q-a)^2.
\]
Positive-definite precision gives the necessary polynomial integrability; Hermitian \(H\) ensures a real quadratic form in the appropriate setting. Algebraically, positive definiteness of \(H\) is not needed for A.

For reuse, the strongest cheap abstraction is the usual identity for **any square-integrable real random variable**, followed by the Gaussian specialisation. Whether that is cheapest in Lean depends on the existing expectation interface.

### B: correct, but its schedule hypothesis is sufficient rather than necessary

Your decomposition of the mean term is sound. An especially transparent equivalent presentation is
\[
t^2v_i\lambda_i^2\mu_{k,i}^2
=(t\sigma_i^2)(1-\rho_i^{2k})\lambda_i^2
  \bigl(\sqrt t\,\mu_{k,i}\bigr)^2,
\]
where
\[
\mu_{k,i}=\widehat m_i+\rho_i^k(\widehat x_{0,i}-\widehat m_i).
\]
Since \(\widehat m_i=O(t^{-1})\), the issue is precisely whether the initial-condition memory is \(o(t^{-1/2})\).

The strict envelope
\[
\max_i|\alpha_i|<r<1
\]
gives \(|\rho_i(t)|\le r\) eventually. Consequently,
\[
t r^{2k(t)}\to0
\]
kills that memory and proves the result. It also already implies \(k(t)\to\infty\), so the latter hypothesis is logically redundant.

**Merely \(k\to\infty\) does not suffice for a generic fixed start.** In one dimension, choose \(0<|\alpha|<1\), \(x_0\ne0\), and
\[
k(t)=\lfloor c\log t\rfloor,\qquad
0<c<\frac1{2\log(1/|\alpha|)}.
\]
Then the covariance contribution converges to its stationary limit, but the mean-memory contribution has size
\[
t|\rho(t)|^{2k(t)}x_0^2
\asymp t^{\,1-2c\log(1/|\alpha|)}
\]
and diverges.

However, the condition involving a chosen \(r\) is not necessary. The sharper condition is modewise control of the actual surviving memory,
\[
t\,\rho_i(t)^{2k(t)}\widehat x_{0,i}^{\,2}\to0.
\]
For example, if \(x_0=0\), then \(\mu_{k,i}=O(t^{-1})\) uniformly in \(k\), and \(k\to\infty\) alone suffices. Only modes excited by the fixed start require the stronger memory condition.

### C: correct

For \(k(t)=\lceil\kappa\log t\rceil_+\),
\[
t r^{2k(t)}
\le t^{\,1-2\kappa\log(1/r)}
\]
eventually. Thus the stated strict threshold proves B.

### D: correct, with careful bookkeeping of units

The exact identity to formalise is
\[
t^2\mathbb E_k[(q-L_{\rm loc}(t))^2]
=t^2\operatorname{Var}_k(q)
 +\bigl(t\mathbb E_kq-tL_{\rm loc}(t)\bigr)^2,
\]
where \(L_{\rm loc}(t)=\langle L\rangle_{\rm loc}\) is a deterministic number.

Thus C and tide 108 give
\[
t^2\mathbb E_k[(q-L_{\rm loc}(t))^2]\longrightarrow V_\eta+b_\eta^2.
\]

Here **the centre is \(L_{\rm loc}(t)\)**; \(\mathbb E_kq-L_{\rm loc}(t)\) is the bias, not the centre.

There is a scaling error in the proposed harmonic expression. The harmonic Gibbs energy is
\[
G(t)=\frac12\operatorname{tr}(HP_t^{-1})
       +\frac12\widehat m^{\mathsf T}H\widehat m,
\]
and its scaled value is
\[
tG(t)=\frac12\operatorname{tr}(tHP_t^{-1})
       +\frac t2\widehat m^{\mathsf T}H\widehat m.
\]
The expression in the question has \(t\) in only the first term.

Under the stated budget,
\[
tL_{\rm loc}(t)-tG(t)=C_1'/t+O(t^{-2}),
\]
so the **unscaled** centres differ by \(O(t^{-2})\). Hence D has the same leading limit when centred at \(G(t)\). Moreover, since \(tG(t)\to d/2\),
\[
\mathbb E_k[(tq-d/2)^2]\longrightarrow b_\eta^2+V_\eta.
\]

**Record all three interpretations**, preferably through one centre-transfer lemma: any deterministic centre \(c(t)\) satisfying
\[
t(c(t)-L_{\rm loc}(t))\to0
\]
has the same limiting scaled MSE. This is a cheap, useful addition.

### E: correct, and strictly increasing for a nonempty positive spectrum

Indeed,
\[
b_\eta'=\frac14\sum_i\frac{\lambda_i}{a_i^2}>0,
\qquad
V_\eta'=\frac12\sum_i\frac{\lambda_i}{a_i^3}>0.
\]
Therefore
\[
(b_\eta^2+V_\eta)'=2b_\eta b_\eta'+V_\eta'>0.
\]
For Lean, direct denominator comparisons may be cheaper than differentiation. Strictness needs \(d>0\); the empty-dimensional case is constant.

## 2. Best bundle and cheap additions

### Recommended dependency chain

1. **A:** bias–variance decomposition.
2. **B:** variance convergence under abstract memory decay.
3. **C:** logarithmic-schedule specialisation.
4. **D:** MSE limit, using tide 108.
5. **Centre transfer:** harmonic and \(d/2\) targets.
6. **E**, if inexpensive.

B is the substantive new analytic result. D makes the tide a coherent completion of the single-draw error story.

### (i) Correlated averages: an exact short route exists

For a fixed deterministic start, let \(v_{s,i}\) and \(\mu_{s,i}\) be the variance and mean in mode \(i\). Gaussian AR(1) structure gives
\[
\operatorname{Cov}(X_{s,i},X_{s+\ell,i})
=v_{s,i}\rho_i^\ell.
\]
The Gaussian quadratic covariance identity then yields
\[
\boxed{
\operatorname{Cov}(q(X_s),q(X_{s+\ell}))
=
\frac12\sum_i\lambda_i^2v_{s,i}^2\rho_i^{2\ell}
+\sum_i\lambda_i^2v_{s,i}\rho_i^\ell
       \mu_{s,i}\mu_{s+\ell,i}.
}
\]
This is an exact nonstationary formula, not an approximation.

After the logarithmic burn-in, for each fixed lag,
\[
t^2\operatorname{Cov}(q(X_k),q(X_{k+\ell}))
\longrightarrow
\frac12\sum_i a_i^{-2}\alpha_i^{2\ell}.
\]
The difference from the stationary covariance is \(o(1)\) on this scaled level, by the same memory estimates as B.

For **fixed \(n\)** consecutive post-burn-in draws, their average therefore has limiting scaled MSE
\[
b_\eta^2+\frac12\sum_i a_i^{-2}F_n(\alpha_i^2),
\]
where
\[
F_n(z)=\frac1{n^2}
\left[n+2\sum_{\ell=1}^{n-1}(n-\ell)z^\ell\right].
\]
For independent replicas of the \(k\)-step law, it is instead simply
\[
b_\eta^2+\frac{V_\eta}{n}.
\]

The correlated-average theorem is a good next tide. Growing \(n=n(t)\) requires uniform estimates, not just fixed-lag convergence. The exact formula and geometric envelope provide a promising route, but that should be a separate claim.

### (ii) Small-step error versus burn-in: yes

You get
\[
\inf_{0<\eta<2/\lambda_{\max}}(b_\eta^2+V_\eta)
=\lim_{\eta\downarrow0}(b_\eta^2+V_\eta)=d/2.
\]
The infimum is not attained at a positive step size.

For the sharp limiting contraction factor
\[
R(\eta)=\max_i|1-\eta\lambda_i|,
\]
small \(\eta\) gives \(R(\eta)=1-\eta\lambda_{\min}\), hence
\[
\kappa_{\rm crit}^{\rm sharp}(\eta)
=\frac1{2\log(1/R(\eta))}
\sim\frac1{2\eta\lambda_{\min}}.
\]
Any admissible envelope \(r>R(\eta)\) gives a larger sufficient threshold, which also diverges.

This is a **single-draw error versus burn-in iteration-count trade-off**, not yet an optimal-computational-cost theorem for averaged estimators.

### (iii) Distinguish the covariance transient from the whole variance transient

Yes:
\[
\rho_i^{2k}=o(t^{-1})
\]
follows from the same threshold
\[
\kappa>\frac1{2\log(1/r)}.
\]

But the generic fixed-start correction to the **scaled variance** includes \(t\rho_i^{2k}\), as well as cross terms of order \(\rho_i^k\). To guarantee
\[
t^2\operatorname{Var}_k(q)-t^2\operatorname{Var}_\infty(q)
=o(t^{-1}),
\]
a sufficient envelope threshold is the doubled one:
\[
\kappa>\frac1{\log(1/r)}.
\]
Also, the stationary scaled variance itself generally has \(O(t^{-1})\) corrections to \(V_\eta\). Thus one should not conflate these statements.

## 3. Suggested wording for D

I would write:

> In the anchored Gaussian model, with exact-gradient ULA, fixed deterministic initial state, and step size \(h=\eta/t\) for fixed \(0<\eta<2/\lambda_{\max}\), a logarithmic burn-in \(k(t)=\lceil\kappa\log t\rceil_+\) above the stated contraction threshold gives
> \[
> \operatorname{RMSE}\bigl(q(X_{k(t)}),\langle L\rangle_{\rm loc}\bigr)
> =\frac{\sqrt{b_\eta^2+V_\eta}+o(1)}{t}.
> \]
> Equivalently, the scaled LLC statistic \(tq(X_{k(t)})\) has limiting bias \(b_\eta\), variance \(V_\eta\), and RMSE \(\sqrt{b_\eta^2+V_\eta}\) relative to the scaled localised-energy target.

Then add:

> This is not single-draw consistency for the LLC: the scaled sampling fluctuations remain nonzero, and at fixed positive \(\eta\) so does the discretisation bias. The anharmonic target enters through the established expectation comparison; this is not a theorem about ULA run on the full anharmonic loss.

That is more precise than “\(O(1)\) accurate on the scale of \(t^{-1}\).” The clean distinction is: **unscaled energy RMSE is \(O(t^{-1})\); scaled LLC RMSE remains \(O(1)\).**

**Final vote: A+B+C+D, plus centre transfer. Add E if cheap; save correlated averages for the next tide.**