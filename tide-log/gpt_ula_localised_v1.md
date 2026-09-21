### 1. Mathematics

**A–C are correct under the stated positivity and stability assumptions.**

- **Conjugation:** Yes:
  \[
  (U^\top PU)^2=U^\top P(UU^\top)PU=U^\top P^2U.
  \]
  Both orthogonality identities are available for square orthogonal \(U\).
- **ULA covariance:** In direction \(i\), the recursion has coefficient \(1-ha_i\) and noise variance \(2h\), hence stationary variance
  \[
  \frac{2h}{1-(1-ha_i)^2}=\frac1{a_i(1-ha_i/2)}.
  \]
  Stability is \(0<ha_i<2\). Thus, assuming a nonempty spectrum, it is equivalent to \(h(t\lambda_{\max}+\gamma)<2\). Increasing localisation **tightens** the allowable step size.
- **B:** Correct. At \(\gamma=0\), it becomes
  \[
  \frac12\sum_i\frac1{1-ht\lambda_i/2},
  \]
  namely the unlocalised formula for precision \(tH\) (equivalently, effective step \(ht\) for \(H\)). As \(h\to0\), it tends to `localisedLLC`; at \(h=0\), the algebraic covariance definition already gives the exact inverse.
- **C:** Correct: each nonnegative exact LLC contribution is multiplied by
  \[
  1\le\frac1{1-ha_i/2}\le\frac1{1-hp_{\max}/2}.
  \]
  The stated excess is a **relative per-direction excess**, strictly increasing in \(a_i\) for fixed \(h>0\). At \(hp_{\max}=0.1\), its maximum is \(1/19\approx5.26\%\), not exactly \(5\%\).

The localisation interpretation is right **for this experiment’s fixed \(hp_{\max}\)**: \(a_i/p_{\max}\) approaches one as \(\gamma\) grows, bringing more directions near maximal inflation. Distinguish the predicted excesses \(1.5\%,2.3\%,4.0\%\) from the measured excesses, approximately \(0.7\%,2.0\%,3.7\%\). The numerical agreement supports, rather than proves, the residual’s attribution to ULA bias.

### 2. Lean

Prefer the **direct conjugation plus explicit inverse** route: it matches the seabed and avoids unnecessary Lyapunov machinery.

1. Prove a reusable product-conjugation lemma using \(UU^\top=1\).
2. Distribute conjugation over subtraction and scalar multiplication.
3. Rewrite the conjugated \(P\), then use diagonal multiplication.
4. Establish denominator nonvanishing from \(a_i>0\) and \(1-ha_i/2>0\), and exhibit the inverse.

Yes, `Matrix.diagonal_sub` is the relevant lemma; its usual direction expands a diagonal of a difference, so use it backwards to combine diagonals. Likewise use the diagonal scalar-multiplication identity.

Keep `(h / 2) • (P * P)` explicit. The expression `((h / 2) • P) * P` is mathematically equal by `smul_mul`, but is not the same syntactic expression; parentheses and normalization avoid rewrite friction.

### 3. Scope

**A+B+C is a coherent tide; ~200 lines is plausible**, depending on existing conjugation helpers.

- Per-direction variances are **already supplied by A**; a coordinate corollary is cheap.
- A stability iff in terms of **all** \(t\lambda_i+\gamma\) is useful. The \(\lambda_{\max}\) version may require nonempty-index and maximum bookkeeping; do not make it a blocker.
- For the left panel, a cheap optional corollary is
  \[
  1\le\frac{\operatorname{tr}\Sigma_{\rm ULA}}
               {\operatorname{tr}P^{-1}}
  \le\frac1{1-hp_{\max}/2},
  \]
  assuming positive denominator/nonempty dimension. Check which ratio orientation the caption uses.

A+B+C captures the covariance prediction and its quantitative bias explanation without expanding into avoidable maximum-eigenvalue infrastructure.

Vote: A+B+C