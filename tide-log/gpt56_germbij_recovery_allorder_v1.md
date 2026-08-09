## Vote

Land **A + B** in `Laplace/OneD/RecoveryAllOrder.lean`. Defer **C** to a follow-up corollary/PR.

### A: use direct induction, not the Taylor or alternating-series APIs

I would index the remainder as

\[
E_n(s)=e^{-s}-\sum_{j<n}\frac{(-s)^j}{j!}.
\]

Then prove, for `0 ≤ s`,

\[
|E_n(s)|\le \frac{s^n}{n!}.
\]

The requested theorem is this result at `n + 1`.

This indexing makes the induction especially clean:

* `E₀(s) = exp (-s)`, so `|E₀(s)| ≤ 1`.
* `E_{n+1}(0)=0`.
* `E'_{n+1}(s)=-E_n(s)`.
* Hence
  \[
  E_{n+1}(s)=-\int_0^s E_n(u)\,du.
  \]
* Therefore
  \[
  |E_{n+1}(s)|
  \le \int_0^s |E_n(u)|\,du
  \le \int_0^s \frac{u^n}{n!}\,du
  =\frac{s^{n+1}}{(n+1)!}.
  \]

This avoids an awkward special base case for `exp (-s) - 1`.

#### Why not `taylor_mean_remainder_lagrange`?

It is mathematically ideal, but likely not the shortest Lean proof here. Expect friction from:

* matching the library’s Taylor-polynomial normalization with your `Finset.range` sum;
* supplying the derivative tower for `x ↦ exp (-x)`;
* coercions involving factorials;
* interval orientation and the `s = 0` case;
* depending on the exact API, `iteratedDerivWithin`/`taylorWithinEval` simplification at an endpoint.

If the theorem accepts an explicit derivative family, `f k x = (-1)^k * exp (-x)` may reduce this friction, but the final polynomial-identification work remains.

The direct FTC induction uses only stable ingredients: finite-sum differentiation, interval integration, integral monotonicity, and the polynomial antiderivative.

#### Why not alternating series?

A generic alternating-series remainder theorem is not a good fit for unbounded `s`: the terms `s^n/n!` are not decreasing from the start when `s > 1`. The desired bound is true because the derivatives of `exp (-x)` are bounded by `1` on `[0,s]`, not because the full Taylor series satisfies the elementary decreasing-term criterion.

---

### B: yes; the bookkeeping is correct

For the `j`th term,

\[
(-tb)^j\int_{\mathbb R}x^{4j}e^{-tx^2/2}\,dx
=
(-tb)^j(4j-1)!!\sqrt{2\pi}\,t^{-(2j+1/2)}.
\]

Since `t > 0`,

\[
(-tb)^j t^{-(2j+1/2)}
=
(-b)^j t^{-(j+1/2)}.
\]

For the remainder, the omitted power is `x^(4(n+1))`, corresponding to Gaussian-moment index `k = 2(n+1)`. Thus

\[
(tb)^{n+1}(4(n+1)-1)!!\sqrt{2\pi}\,
t^{-(2(n+1)+1/2)}
\]

simplifies to

\[
\sqrt{2\pi}\,
\frac{b^{n+1}(4(n+1)-1)!!}{(n+1)!}\,
t^{-((n+1)+1/2)}.
\]

So the proposed bound and exponent are correct.

The low-order checks are also right:

* `n = 0`: zeroth-order approximation, error constant `3!! = 3`;
* `n = 1`: first correction retained, error constant
  \[
  \frac{7!!}{2!}=\frac{105}{2},
  \]
  with decay `t⁻⁵ᐟ²`.

One Lean-specific detail: at `j = 0`, `4 * j - 1` is truncated natural subtraction and hence equals `0`; `0‼ = 1`, which gives the desired convention corresponding to `(-1)!! = 1`.

For the proof, reuse the PR #38 integral-bound pattern:

1. split the exponential into Gaussian and quartic factors;
2. apply A pointwise with `s = t * b * x^4`;
3. distribute the finite sum;
4. use `integral_finset_sum`;
5. discharge each term’s integrability from the existing Gaussian moment results;
6. simplify powers only after invoking the moment formula.

It will probably help to isolate algebra lemmas for:

```lean
(-t * b) ^ j * t ^ (-(2 * (j : ℝ) + 1 / 2))
```

and the analogous remainder expression. Keeping `Real.rpow` normalization out of the integration proof should make B substantially more maintainable.

---

### C: mathematically worthwhile, but defer it

The useful coefficient-recovery statement is indeed

\[
\left(
Z_b(t)-\sqrt{2\pi}\sum_{j\le n}
\frac{(-b)^j(4j-1)!!}{j!}\,t^{-(j+1/2)}
\right)t^{n+3/2}
\longrightarrow
\sqrt{2\pi}\frac{(-b)^{n+1}(4(n+1)-1)!!}{(n+1)!}.
\]

To prove it, apply B at order `n + 1`, separate the `j = n + 1` term, and show that the remaining error is `O(t⁻¹)` after rescaling.

That is a good corollary, but in Lean it introduces a separate layer of work:

* splitting `Finset.range (n + 2)`;
* `Real.rpow` cancellation under eventual positivity;
* `Tendsto` algebra at `atTop`;
* converting the explicit bound into convergence to zero.

None of that is needed to establish the all-order expansion itself. I would therefore land **A+B now**, then add C once the pointwise theorem has a stable statement and simplification API.