## 1. Time-change audit

**The exponents are correct.** Put
\[
c=(D_0/D)^{q/\gamma},\qquad \tau=tc.
\]
Then
\[
D_0\tau^{-\gamma/q}=Dt^{-\gamma/q}.
\]
Thus the cutoff variable—and therefore both units evaluated at that variable—is unchanged. The other two identities are
\[
(Ac^{\gamma p})\tau^{-\gamma p}=At^{-\gamma p},
\qquad
(Bc^{-\delta})\tau^\delta=Bt^\delta.
\]
Since \(c^{\gamma p}=(D_0/D)^{qp}\) and \(c^{-\delta}=(D_0/D)^{-q\delta/\gamma}\), your statement has exactly the right powers.

For \(\lambda=\gamma p+\beta\delta-\eta\gamma\),
\[
\frac{t^\lambda/\log(t)^k}{(tc)^\lambda/\log(tc)^k}
=c^{-\lambda}\left(1+\frac{\log c}{\log t}\right)^k.
\]
With \(D(t)\to D_0>0\), eventually \(D(t)>0\), \(c(t)\to1\), and \(\tau(t)\to\infty\). Consequently:

* \(t>1\) and \(\tau(t)>1\) eventually;
* the displayed ratio tends to \(1\), including when \(k=0\);
* fixed-\(b\) limits compose directly with \(\tau\);
* any threshold requirement such as \(\tau(t)\ge e\) holds eventually. No monotonicity or invertibility of \(t\mapsto\tau(t)\) is needed.

One bookkeeping point: squeeze the **nonnegative kernel with the amplitude \(A\) removed**, then multiply by the transformed amplitude. Your theorem permits arbitrary \(A_0\), correctly; it should not silently use \(A(t)\ge0\).

### Scope of \(\gamma>0\)

It is exactly appropriate for the shrinking-cut regime \(s=\sigma t^{-\gamma}\to0\).

* The displayed algebra actually works for \(\gamma\ne0\), subject to the corresponding nonzero-power identities.
* That does **not** automatically extend the analytic theorem to \(\gamma<0\).
* At \(\gamma=0\), this argument genuinely disappears: varying \(D\) changes the unit evaluation without a compensating time change. Merely measurable units need not be stable under that variation.

So retain \(\gamma>0\), and state the shrinking-cut scope explicitly. I see no additional hypothesis needed in the supplied theorem signature.

## 2. Is the Euclidean analytic claim closed?

**For the explicitly nondegenerate, strictly positive-exponent active-truth regime: yes, based on the inventory and signatures supplied.** I would not certify an unrestricted “every resolution chart” claim without checking its hypothesis-discharge layer.

The remaining audit checklist is:

1. **Strict LP regime.** Resolution alone does not imply
   \[
   r_i+1=\beta\kappa_i-\eta Q_i,\qquad \beta,\eta>0,
   \]
   nor \(\kappa_i>0\) on every coordinate. The classification/certificate must supply these, with genuine spectators separated out. The endpoints \(\beta=0\) or \(\eta=0\) are not covered by this theorem.

2. **Noncollapsing coordinates.** Your `hc₀`, `hc₁` are substantive restrictions, not cosmetic genericity assumptions. Either the note excludes their failure or it needs (e). Solved-pair independence does not, by itself, remove this issue.

3. **Unit positivity and extension.** On a sufficiently small closed chart box, a continuous positive phase unit gives the required uniform lower bound. But “analytic unit” alone means nonvanishing, not positive: sign handling must establish positivity on the relevant branch. Global measurable extensions satisfying the displayed bounds must preserve the kernel on its integration domain.

4. **Traces.** For continuous resolution units, simultaneous collapse of the active coordinates gives the required trace. With spectators, retain them in that trace and check the bounds on their entire integration domain. Pointwise-in-\(u\) traces are enough here because your theorem already supplies domination; no extra uniform trace hypothesis should be inserted.

5. **Signed tests.** `hWb` is a nonnegative-weight theorem. If the chart wrapper claims convergence against arbitrary real test functions, it needs the positive/negative decomposition or an equivalent signed extension.

6. **Branches and boxes.** Along \(\sigma(t)\to\sigma_0\ne0\), the sign is eventually fixed. Verify that all admissible \((\varepsilon,b)\) branches, their Jacobian factors, and chart cutoffs are included exactly once. A bounded weight can absorb cutoffs, but not an omitted branch or multiplicity.

Thus **(h) is a regression/integration test, not a missing analytic argument**. Likewise (g) is a missing export. And (e) is a missing theorem only if the note claims that boundary regime.

## 3. Ranking

For the next bounded research rounds, I would rank:

1. **Compact-\(\sigma\) uniformity:** high-value, low-risk consequence of the moving theorem.
2. **(g) General-truth hironaka export:** the principal remaining delivery dependency; put this first instead if completing the mirrored note is the immediate objective.
3. **`xy = s` total-kernel bookkeeping:** exercises assembly and the mixed log endpoint using an existing record.
4. **(h) Mixed vertex/tied/active example:** useful integration test, but avoid another expensive record construction until the export interface settles.
5. **(e) Constant-unit boundary theorem:** clean extension with a genuinely different coefficient.
6. **Weighted mixed truth, \(h<0\):** move higher if that trichotomy is explicitly promised in the note.
7. **Support-separated distinguishability:** useful downstream, not needed to complete the asymptotic theorem.

### Top item: statement to formalise

First prove a reusable compactness lemma. Here is an interface sketch, not a claim about existing declaration names:

```lean
theorem eventually_uniform_of_moving
    {C : Set ℝ} (hC : IsCompact C)
    {F : ℝ → ℝ → ℝ} {L : ℝ → ℝ}
    (hL : ContinuousOn L C)
    (hmove :
      ∀ σ₀ ∈ C, ∀ σ : ℝ → ℝ,
        (∀ᶠ t in atTop, σ t ∈ C) →
        Tendsto σ atTop (𝓝 σ₀) →
        Tendsto (fun t ↦ F t (σ t)) atTop (𝓝 (L σ₀))) :
    ∀ ε > 0, ∀ᶠ t in atTop,
      ∀ σ ∈ C, |F t σ - L σ| < ε
```

Specialise with
\[
F(t,\sigma)=N(t)\,\mathrm{termKernel}(t,\sigma),\qquad
L(\sigma)=\int\varphi\,d\mu_{\mathrm{activeTruth},\sigma},
\]
for compact \(C\subset\mathbb R\setminus\{0\}\), with the chart data, normaliser and test function fixed.

Prove continuity of \(L\) from the explicit coefficient/measure formula, separately on the two sign components if convenient. The compactness proof is the usual contradiction: escaping times, bad parameters, a convergent parameter subsequence, and an interpolated parameter path to invoke `hmove`.

**Do not advertise this as uniformity over test functions or total-variation convergence.** It is uniform in \(\sigma\) for each fixed admissible test.

### Precise shape of (e)

The boundary coefficient is **not generally the old coefficient with one coordinate deleted**.

Use logarithmic free coordinates \(x_{\mathrm{free}}=t^{-w}\), and define
\[
v=t^\delta\prod_i x_i^{\kappa_i},
\qquad
u=Dt^{-\gamma/q}\prod_i x_i^{-Q_i/q}.
\]
Write the solved coordinates as
\[
x_j=t^{-f_j(w)}z_j(v,u),\qquad
z_j(v,u)=
\exp\!\left[
M^{-1}
\binom{\log v}{q\log(D/u)}
\right]_j,
\]
where \(M\) has rows given by the solved \(\kappa\)- and \(Q\)-coefficients. Let \(J\) consist of the solved coordinates whose affine collapse function \(f_j\) is identically zero—the `c_j = a_j = 0` case.

For **\(W=a=1\)**, retaining the other hypotheses and nondegeneracy of the remaining solved coordinates, the expected statement is
\[
\frac{t^{\gamma p+\beta\delta-\eta\gamma}}{\log(t)^k}K(t)
\longrightarrow
\frac{AqD^{-q\eta}\operatorname{vol}(F')}{|\det M|}
\int_0^\rho u^{q\eta-1}
\int_0^\infty
v^{\beta-1}e^{-Bv}
\prod_{j\in J}\mathbf1_{(0,\rho)}(z_j(v,u))
\,dv\,du .
\]

The face \(F'\) is the same limiting face; its identically zero inequalities are simply vacuous. The frozen-coordinate box restrictions survive inside the \((v,u)\)-integral. For \(J=\varnothing\), the inner integral is \(\Gamma(\beta)B^{-\beta}\), recovering your existing theorem.

**This constant-unit version is tractable.** The old gamma majorant still dominates; the new work is the indicator limit and its null boundary. General units then require a **partial trace retaining the frozen coordinates**, evaluated at \(z_J(v,u)\), rather than the current all-active-coordinates-zero trace.