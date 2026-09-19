1. **(P)–(U) are correct. The AM–GM route loses nothing at the SuperPoly level.**

   Write \(h_t=a_t-b_t\). For \(t\ge0\),
   \[
   Dh_t\ge0,\qquad |h_t|\le t|D|,
   \qquad |h_t|^2\le tDh_t.
   \]
   The last step uses \(|D||h_t|=Dh_t\), so it is worth exposing the sign lemma separately.

   For \(t>0\) and \(n\in\mathbb N\), your AM–GM inequality gives
   \[
   F_\eta(t):=\int\eta^2|h_t|
   \le \frac{A_\eta}{2}t^{-n}
       +\frac12t^{n+1}E_\eta(t),
   \qquad A_\eta=\int\eta^2.
   \]
   Since \(E_\eta\) is SuperPoly, its decay at exponent \(2n+1\) makes the second term \(o(t^{-n})\). Thus \(F_\eta=O(t^{-n})\) for every \(n\).

   **The one bookkeeping point:** to conclude little-\(o\) at exponent \(N\), use the big-\(O\) estimate at exponent \(N+1\). Your proposed helper is exactly right.

   Schematic Lean shapes, using inverse natural powers to avoid real-power bookkeeping:
   ```lean
   -- SuperPoly f := ∀ N : ℕ,
   --   f =o[atTop] (fun t : ℝ => (t ^ N)⁻¹)

   theorem superPoly_of_eventually_le_inv_pow
       (h : ∀ N : ℕ, ∃ C : ℝ,
         ∀ᶠ t : ℝ in atTop, |f t| ≤ C * (t ^ N)⁻¹) :
       SuperPoly f

   theorem laplace_density_sq_le
       (ht : 0 ≤ t) (h₁ : 0 ≤ l₁) (h₂ : 0 ≤ l₂) :
       |Real.exp (-t * l₁) - Real.exp (-t * l₂)| ^ 2 ≤
         t * ((l₂ - l₁) *
           (Real.exp (-t * l₁) - Real.exp (-t * l₂)))
   ```

   No hidden integrability issue under your stated hypotheses:
   * all the smooth-cutoff integrands are continuous and compactly supported;
   * bounded measurable compactly supported tests are integrable against these densities;
   * for \(t\ge0\), the useful domination is simply \(e^{-tL_i}\le1\).

   Remember that agreement gives \(I_2-I_1\), whereas \(E_\eta=I_1-I_2\): one SuperPoly negation.

2. **Both losses being smooth is sufficient, but not genuinely necessary.**

   What this proof needs for the test is
   \[
   \eta^2(L_2-L_1)\in C_c^\infty.
   \]
   Consequently, **smoothness of \(D=L_2-L_1\)** is enough, together with suitable measurability/local integrability assumptions on the densities. For example, both losses could have the same nonsmooth continuous summand, while their difference is smooth.

   Likewise, with a \(C_c^k\) tested class, \(D\in C^k\) suffices; requiring both losses to be \(C^k\) is a convenient stronger hypothesis.

   So I would phrase the restriction as:

   > With only smooth-test agreement, this direct energy-test argument requires the cutoff difference \(\eta^2D\) to be smooth. Merely assuming both losses are \(C^k\) does not justify that test.

   I would **not** promote that into a necessity theorem saying no alternative argument or weaker hypothesis could work. For this tide, retaining `ContDiff ℝ ⊤ L₁` and `ContDiff ℝ ⊤ L₂` is perfectly reasonable.

3. **The clean primary target is compact-local total variation; several proposed limitations disappear after proving it.**

   **(a) Continuous cutoffs work as a corollary.** Although you cannot directly test at \(\eta^2D\) for continuous \(\eta\), domination by a larger smooth cutoff gives
   \[
   \int \eta^2|h_t|=o(t^{-\infty})
   \]
   for every continuous compactly supported \(\eta\). More generally, every bounded measurable compactly supported weight works. No corresponding unrestricted, noncompact weight conclusion follows without tail assumptions.

   **(b) Yes: package the compact-set statement.**
   ```lean
   theorem superPoly_localTV
       (hK : IsCompact K) :
       SuperPoly (fun t =>
         ∫ x in K,
           |Real.exp (-t * L₂ x) - Real.exp (-t * L₁ x)|)
   ```
   This is genuinely uniform over bounded tests supported in \(K\):
   \[
   \sup_{\substack{|\varphi|\le1\\\operatorname{supp}\varphi\subset K}}
   |I_2(\varphi,t)-I_1(\varphi,t)|
   \le \int_K|h_t|.
   \]
   In particular, the bound also applies to **\(t\)-dependent tests** satisfying the same support and supremum bound.

   **(c) Local \(L^\infty\) is actually true under your smoothness assumptions.** On a fixed enlarged ball,
   \[
   \|\nabla h_t\|\le Ct\qquad(t\ge1),
   \]
   because \(\nabla e^{-tL_i}=-t e^{-tL_i}\nabla L_i\) and \(L_i\ge0\). A Lipschitz peak of height \(H\) therefore occupies a ball of radius comparable to \(H/t\). Consequently,
   \[
   \sup_K|h_t|
   \le C_K\left(t^d\int_{K'}|h_t|\right)^{1/(d+1)}
   \]
   for a suitable enlarged compact neighborhood \(K'\). Local \(L^1\)-SuperPoly implies local \(L^\infty\)-SuperPoly.

   This is a nice later theorem, but the geometric/interpolation infrastructure makes it a poor addition to the present tide. **Global** \(L^\infty\) does not follow without additional control at infinity.

   **(d) Normalization is easy for the tests covered by (U).** Assuming finite positive \(Z_i\), \(|\varphi|\le M\), and
   \[
   Z_1^{-1}=O(t^{d/2}),\qquad Z_2/Z_1-1=o(t^{-\infty}),
   \]
   use the identity
   \[
   \frac{I_2}{Z_2}-\frac{I_1}{Z_1}
   =
   \frac{I_2-I_1}{Z_1}
   +\frac{I_2}{Z_2}\left(1-\frac{Z_2}{Z_1}\right).
   \]
   Since \(|I_2/Z_2|\le M\), both terms are SuperPoly. This formulation avoids proving a separate polynomial bound for \(1/Z_2\).

   **Important scope correction:** (U) covers bounded measurable **compactly supported** \(\varphi\). It does not establish this normalized conclusion for arbitrary globally bounded measurable tests. Partition-function agreement alone does not control total variation in remote tails.

4. **For (P), I would use the elementary exponential argument rather than hunt for a specialized Lipschitz lemma.**

   Establish first:
   ```lean
   theorem abs_exp_neg_sub_le
       (hx : 0 ≤ x) (hy : 0 ≤ y) :
       |Real.exp (-x) - Real.exp (-y)| ≤ |x - y|
   ```

   Split on `x ≤ y`. In that branch put \(u=y-x\ge0\), and use
   \[
   e^{-x}-e^{-y}=e^{-x}(1-e^{-u}),\qquad
   0\le e^{-x}\le1,\qquad
   0\le1-e^{-u}\le u.
   \]
   The final inequality follows directly from `Real.add_one_le_exp (-u)`. The other branch is symmetry.

   Useful basic API: `Real.add_one_le_exp`, `Real.exp_add`, and exponential monotonicity. I would not rely on an exact specialized Lipschitz lemma name without checking the pinned Mathlib revision.

   Practical proof structure:
   * derive exponential ordering first;
   * rewrite absolute values using that ordering;
   * use `mul_le_mul`-style lemmas for product inequalities;
   * reserve `nlinarith` for the resulting polynomial facts.

   For the sign lemma, split on `L₁ x ≤ L₂ x`, rather than divide by \(t\). This handles \(t=0\) without extra machinery.

   For the integral layer, I would expose:
   ```lean
   theorem superPoly_weightedTV
       (hη : ContDiff ℝ ⊤ η)
       (hηc : HasCompactSupport η) :
       SuperPoly (fun t =>
         ∫ x, (η x)^2 *
           |Real.exp (-t * L₂ x) - Real.exp (-t * L₁ x)|)

   theorem superPoly_test_of_bounded_measurable_compact
       (hφm : Measurable φ)
       (hφc : HasCompactSupport φ)
       (hM : 0 ≤ M)
       (hφM : ∀ x, |φ x| ≤ M) :
       SuperPoly (fun t => I₂ φ t - I₁ φ t)
   ```
   Here the ambient hypotheses and definitions are omitted schematically.

   Two likely Lean friction points:
   * supply integrability before rewriting a difference of integrals as an integral of a difference;
   * choose the containing ball with slack, so the bump’s “equals one” API does not create boundary problems.

5. **Yes to wiring (C), but preserve the exact established anchor hypotheses.**

   The new upgrade should depend only on smooth-test exact agreement plus the loss assumptions. Keep the projective/anchor reasoning upstream:
   \[
   \text{projective agreement + anchor}
   \Longrightarrow \text{smooth exact agreement}
   \Longrightarrow \text{local TV}
   \Longrightarrow \text{bounded measurable compact-test agreement}.
   \]
   Continuous compact-test agreement then becomes a small corollary.

   If “one common analytic zero” abbreviates an already-proved theorem supplying the necessary local equality/calibration, fine. A bare common zero should not silently replace the anchor hypotheses.

   Around 300 lines is plausible **if** bump selection, compact-support integrability, and the SuperPoly closure lemmas already exist. Otherwise those utilities, rather than the main argument, will dominate the count.

**Vote: yes—ship P+V+local-TV+U+C together; leave local \(L^\infty\) and noncompact-tail extensions for a later tide.**