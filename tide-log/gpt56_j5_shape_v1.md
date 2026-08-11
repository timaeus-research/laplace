## 1. Exact decomposition

Write, for \(j=1,2\),

\[
a_j(q,x):=\frac{L_j(qx)-L_j(0)}{q^2},
\qquad
\chi_j(q,x):=\mathbf 1_{\{qx\in U_j\}},
\]

and

\[
I_j(P,q):=\int \chi_j(q,x)\,P(x)e^{-a_j(q,x)}\,dx.
\]

Let

\[
N_j(q):=I_j(P,q),\qquad D_j(q):=I_j(1,q),\qquad r:=k-2.
\]

Then the exact quotient identity is

\[
\frac{N_1}{D_1}-\frac{N_2}{D_2}
=
\frac{N_1-N_2}{D_1}
-
\frac{N_2}{D_2}\frac{D_1-D_2}{D_1}.
\]

Equivalently,

\[
\frac{N_1}{D_1}-\frac{N_2}{D_2}
=
\frac{(N_1-N_2)-\frac{N_2}{D_2}(D_1-D_2)}{D_1}.
\]

After division by \(q^r\),

\[
\frac{1}{q^r}
\left(\frac{N_1}{D_1}-\frac{N_2}{D_2}\right)
=
\frac{(N_1-N_2)/q^r}{D_1}
-
\frac{N_2}{D_2}\,
\frac{(D_1-D_2)/q^r}{D_1}.
\]

This is the best form for Lean: only one eventually-nonzero denominator, `D₁`, appears in the outer division.

A suitable algebra lemma is:

```lean
lemma div_sub_div_rearranged
    {N₁ N₂ D₁ D₂ : ℝ} (hD₁ : D₁ ≠ 0) (hD₂ : D₂ ≠ 0) :
    N₁ / D₁ - N₂ / D₂ =
      (N₁ - N₂) / D₁ - (N₂ / D₂) * ((D₁ - D₂) / D₁) := by
  field_simp
  ring
```

For the rate-divided form, it is usually easier to apply this pointwise and then use `Tendsto.sub`, `Tendsto.mul`, and `Tendsto.div`.

### The two unnormalized limits needed

Let

\[
K_H(x):=\exp\!\left(-\tfrac12\langle x,Hx\rangle\right),
\qquad
Z:=\int K_H(x)\,dx,
\]

and

\[
Q(x):=
\operatorname{taylorHomogeneousTerm}_k(L_1,x)
-
\operatorname{taylorHomogeneousTerm}_k(L_2,x).
\]

The analytic core should prove, first for arbitrary polynomial-growth \(P\),

\[
\frac{I_1(P,q)-I_2(P,q)}{q^{k-2}}
\longrightarrow
-\int P(x)Q(x)K_H(x)\,dx.
\]

Applying the same theorem with `P := 1` gives

\[
\frac{D_1(q)-D_2(q)}{q^{k-2}}
\longrightarrow
-\int Q(x)K_H(x)\,dx.
\]

Ordinary H4/H5 convergence gives

\[
D_j(q)\to Z,
\qquad
\frac{N_2(q)}{D_2(q)}
\to \frac{\int P K_H}{Z}.
\]

Substitution into the quotient identity gives

\[
-\frac{\int P Q K_H}{Z}
+
\frac{\int P K_H}{Z}\frac{\int Q K_H}{Z}
=
-\operatorname{Cov}_{\gamma_H}(P,Q).
\]

That is exactly the desired sign.

### Exponential difference lemma

Do not use a chosen mean-value point `ξ`; such a choice is awkward to make measurable and unnecessary.

The clean scalar package is the integral secant identity

\[
e^{-a}-e^{-b}
=
-(a-b)\int_0^1
e^{-((1-t)b+ta)}\,dt.
\]

It simultaneously provides:

1. the exact factorization;
2. the pointwise limit of the secant;
3. the domination estimate
   \[
   |e^{-a}-e^{-b}|
   \le |a-b|\max(e^{-a},e^{-b}).
   \]

A Lean-flavoured scalar lemma is:

```lean
lemma exp_neg_sub_exp_neg_eq
    (a b : ℝ) :
    Real.exp (-a) - Real.exp (-b) =
      -(a - b) *
        ∫ t in (0 : ℝ)..1,
          Real.exp (-((1 - t) * b + t * a)) := by
  -- Apply the fundamental theorem of calculus to
  -- t ↦ exp (-((1-t) * b + t * a)).
```

Likely supporting API:

- `Real.hasDerivAt_exp`
- `HasDerivAt.comp`
- `intervalIntegral.integral_deriv_eq_sub`
- `Real.exp_neg`
- `Real.exp_le_exp`
- the existing 1D secant-bound lemma from `TaylorCompare`

In practice, I would:

- use the integral identity or a custom continuous secant lemma for the pointwise limit;
- reuse the existing 1D secant bound for domination.

For \(q>0\), put

\[
d_q(x):=a_1(q,x)-a_2(q,x).
\]

Since \(r=k-2\),

\[
\frac{d_q(x)}{q^r}
=
\frac{
  (L_1(qx)-L_2(qx))-(L_1(0)-L_2(0))
}{q^k}.
\]

The equality uses \(q^2q^{k-2}=q^k\). In Lean, establish `q ≠ 0` from `q > 0`, use

```lean
Nat.sub_add_cancel (Nat.le_of_lt hk)
```

for `2 + (k - 2) = k`, followed by `pow_add` and `field_simp`.

J4 then gives

```lean
Tendsto
  (fun q => (a₁ q x - a₂ q x) / q ^ (k - 2))
  (nhdsWithin 0 (Set.Ioi 0))
  (𝓝 (Q x))
```

and the scalar secant tends to `-Real.exp (-quad x)`. Their product tends to `-Q x * K_H x`.

---

## 2. Domination at rate \(q^{k-2}\)

### Local common region

Choose a fixed ball

\[
B_\rho:=\{y:\|y\|<\rho\}
\subseteq U_1\cap U_2
\]

on which:

1. both losses have the quadratic lower bound
   \[
   L_j(y)-L_j(0)\ge c\|y\|^2;
   \]
2. matched lower jets and bounded \(k\)-th derivatives imply
   \[
   \left|
   (L_1-L_2)(y)-(L_1-L_2)(0)
   \right|
   \le C\|y\|^k.
   \]

For \(y=qx\), this yields

\[
\left|\frac{a_1(q,x)-a_2(q,x)}{q^{k-2}}\right|
\le C\|x\|^k.
\]

The secant estimate and the two lower bounds give

\[
\left|
\frac{e^{-a_1(q,x)}-e^{-a_2(q,x)}}{q^{k-2}}
\right|
\le
C\|x\|^k e^{-c\|x\|^2}.
\]

Therefore the divided integrand is dominated by

\[
C\,|P(x)|\,\|x\|^k e^{-c\|x\|^2}.
\]

For polynomial-growth `P`, this is integrable. This should be discharged using the Gaussian integrability layer around:

```lean
integrable_mul_quadKernel_of_polynomialGrowth
```

possibly after proving polynomial growth for

```lean
fun x => P x * ‖x‖ ^ k
```

using the existing closure lemmas such as `HasPolynomialGrowth.mul`.

### Unequal domains and the tail split

Equality `U₁ = U₂` is not mathematically necessary.

Let

\[
\chi_\rho(q,x):=\mathbf 1_{\{qx\in B_\rho\}}.
\]

Because \(B_\rho\subseteq U_j\),

\[
\begin{aligned}
\chi_1 e^{-a_1}-\chi_2 e^{-a_2}
={}&
\chi_\rho(e^{-a_1}-e^{-a_2})\\
&+(\chi_1-\chi_\rho)e^{-a_1}
-(\chi_2-\chi_\rho)e^{-a_2}.
\end{aligned}
\]

The first term is the local Taylor-comparison term. The last two are domain-tail terms.

On the support of either tail,

\[
\|qx\|\ge\rho,
\qquad\text{hence}\qquad
\|x\|\ge \rho/q.
\]

For \(r=k-2\),

\[
q^{-r}\le \rho^{-r}\|x\|^r.
\]

Thus, assuming the H4 quadratic lower bound is valid on each whole integration domain,

\[
\frac{
  |\chi_j-\chi_\rho|\,|P(x)|e^{-a_j(q,x)}
}{q^r}
\le
\rho^{-r}|P(x)|\|x\|^r e^{-c_j\|x\|^2}.
\]

The right side is integrable and independent of \(q\), while the tail indicator converges pointwise to zero. Ordinary dominated convergence therefore proves the rate-divided tail tends to zero.

This is preferable to developing a separate “Gaussian tails are \(o(q^N)\) for every \(N\)” theorem. You only need the fixed exponent `N = k - 2`, and the elementary trade

```text
q⁻ʳ ≤ ρ⁻ʳ ‖x‖ʳ
```

does the job. A generic all-`N` Gaussian-tail lemma may still be useful infrastructure, but it is not logically required here.

### Is a `sqrt q` split needed?

Not under the strong H4-style assumptions:

- a quadratic lower bound on the relevant domains;
- a fixed ball on which the order-\(k\) Taylor bound holds.

The natural split is the original-variable fixed ball `‖qx‖ < ρ`, equivalently the rescaled ball `‖x‖ < ρ/q`.

A `sqrt q` split is useful in the 1D precedent when one only has weaker local control and must balance Taylor error against a separate outer estimate. Here the exponential secant estimate plus quadratic lower bounds already gives a fixed Gaussian dominator, so introducing `sqrt q` would complicate the generic proof without improving the estimate.

If `LocalLaplaceDomain` supplies only a local lower bound and not a quantitative estimate on `U \ Bρ`, then additional tail data is necessary. Two viable alternatives are:

1. a quadratic lower bound throughout `U`; or
2. a strict tail gap plus enough integrable-envelope data to control the volume/growth outside the ball.

A bare statement

\[
L(y)-L(0)\ge\eta>0
\quad\text{outside }B_\rho
\]

is not by itself sufficient on an unbounded domain unless paired with an integrability/growth assumption. The global-on-`U` quadratic lower bound is the cleanest J5 interface.

---

## 3. Recommended `HigherLaplaceDomain` structure

The genuinely new local input is an order-\(k\), uniform Taylor bound. The tail/coercivity data should remain in `LocalLaplaceDomain` if H4 already exposes it.

A practical structure is:

```lean
structure HigherLaplaceDomain
    (k : ℕ)
    (L : EuclidD d → ℝ)
    (H : Matrix (Fin d) (Fin d) ℝ)
    extends LocalLaplaceDomain L H where

  contDiff_k : ContDiffAt ℝ k L 0

  taylorRadius : ℝ
  taylorRadius_pos : 0 < taylorRadius

  taylorBall_subset :
    Metric.ball 0 taylorRadius ⊆ toLocalLaplaceDomain.domain

  taylorRemainderConst : ℝ
  taylorRemainderConst_nonneg : 0 ≤ taylorRemainderConst

  taylorRemainder_bound :
    ∀ y ∈ Metric.ball 0 taylorRadius,
      ‖L y -
          ∑ j ∈ Finset.range k,
            taylorHomogeneousTerm j L y‖
        ≤ taylorRemainderConst * ‖y‖ ^ k
```

Field names such as `domain` must of course be changed to the actual `LocalLaplaceDomain` projection names.

### Prefer deriving the remainder field if feasible

Mathematically, `ContDiffAt ℝ k L 0` in finite dimension should imply the displayed local remainder bound after shrinking the radius. Therefore the cleaner conceptual definition is:

```lean
structure HigherLaplaceDomain ... extends LocalLaplaceDomain L H where
  contDiff_k : ContDiffAt ℝ k L 0
```

followed by a theorem:

```lean
theorem HigherLaplaceDomain.exists_taylor_remainder_bound
    (A : HigherLaplaceDomain k L H) :
    ∃ ρ > 0, ∃ C ≥ 0,
      Metric.ball 0 ρ ⊆ A.domain ∧
      ∀ y ∈ Metric.ball 0 ρ,
        ‖L y -
            ∑ j ∈ Finset.range k,
              taylorHomogeneousTerm j L y‖
          ≤ C * ‖y‖ ^ k := ...
```

However, Mathlib’s iterated Fréchet derivative/Taylor API can make this derivation expensive. If J5 is meant to unblock the programme rather than develop a general Taylor library, storing the remainder bound directly is a reasonable engineering choice.

An intermediate design is to store a bounded-derivative hypothesis:

```lean
  derivRadius : ℝ
  derivRadius_pos : 0 < derivRadius
  derivBall_subset :
    Metric.ball 0 derivRadius ⊆ toLocalLaplaceDomain.domain

  iteratedFDeriv_bound :
    ∃ C ≥ 0, ∀ y ∈ Metric.ball 0 derivRadius,
      ‖iteratedFDeriv ℝ k L y‖ ≤ C
```

and prove the remainder estimate once. But unless that derivative bound is needed elsewhere, the direct remainder field gives a substantially smaller proof surface.

### Tail field, if not inherited from H4

If `LocalLaplaceDomain` does not already provide a quadratic lower bound on all of its indicator domain, add:

```lean
  coerciveConst : ℝ
  coerciveConst_pos : 0 < coerciveConst

  loss_lower_bound :
    ∀ y ∈ toLocalLaplaceDomain.domain,
      coerciveConst * ‖y‖ ^ 2 ≤ L y - L 0
```

This one field supports both:

- the local Gaussian domination;
- the rate-divided domain-tail estimate.

If H4 already has an equivalent field, do not duplicate it.

### Should the domains be equal?

No. Requiring `U₁ = U₂` would simplify the first implementation but is unnecessarily restrictive for a germ theorem.

The pairwise proof can choose

```lean
ρ := min A₁.taylorRadius A₂.taylorRadius
```

or a smaller positive radius, and prove

```lean
Metric.ball 0 ρ ⊆ A₁.domain ∩ A₂.domain.
```

Unequal-domain effects are then exactly the two retreating tails above.

Jet matching also belongs in the theorem, not in either individual structure:

```lean
hlower :
  ∀ j < k,
    iteratedFDeriv ℝ j L₁ 0 =
      iteratedFDeriv ℝ j L₂ 0
```

For proof ergonomics, a private pair-data construction can collect the minimum radius and minimum coercivity constant:

```lean
private structure PairwiseRateData ... where
  ρ : ℝ
  hρ : 0 < ρ
  ball_subset₁ : Metric.ball 0 ρ ⊆ A₁.domain
  ball_subset₂ : Metric.ball 0 ρ ⊆ A₂.domain
  c : ℝ
  hc : 0 < c
  lower₁ : ...
  lower₂ : ...
  taylorDifference_bound : ...
```

That need not become public API.

---

## 4. Staging and first checkpoint

I recommend several tides, but generic `k` from the beginning. The cubic case does not remove any of the difficult components:

- exponential secant;
- domain-tail split;
- rate-divided domination;
- normalized quotient algebra.

It only changes `k - 2` to `1`. Since J4 is already generic, implementing a separate cubic theorem would likely duplicate the main proof.

### Tide J5a: scalar exponential calculus

Prove a reusable scalar lemma of the form:

```lean
theorem tendsto_exp_neg_sub_div
    {a₁ a₂ s : ℝ → ℝ}
    {u v : ℝ}
    (ha₁ : Tendsto a₁ l (𝓝 u))
    (ha₂ : Tendsto a₂ l (𝓝 u))
    (hd :
      Tendsto (fun q => (a₁ q - a₂ q) / s q) l (𝓝 v)) :
    Tendsto
      (fun q =>
        (Real.exp (-a₁ q) - Real.exp (-a₂ q)) / s q)
      l
      (𝓝 (-Real.exp (-u) * v))
```

The exact hypotheses should include eventual nonvanishing of `s` if the expression uses ordinary division.

Also expose the secant bound:

```lean
lemma abs_exp_neg_sub_exp_neg_le
    (a b : ℝ) :
    |Real.exp (-a) - Real.exp (-b)|
      ≤ |a - b| * max (Real.exp (-a)) (Real.exp (-b))
```

Reuse the 1D theorem if it is already suitably general.

### Tide J5b: retreating Gaussian-tail lemma

This is the first small analytic checkpoint:

```lean
theorem tendsto_integral_retreating_tail_div_pow
    {P : EuclidD d → ℝ}
    (hP_meas : StronglyMeasurable P)
    (hP_growth : HasPolynomialGrowth P)
    {ρ c : ℝ} (hρ : 0 < ρ) (hc : 0 < c)
    (r : ℕ) :
    Tendsto
      (fun q =>
        (∫ x,
          Set.indicator
            {x | ρ ≤ q * ‖x‖}
            (fun x => P x * Real.exp (-c * ‖x‖ ^ 2)) x) /
          q ^ r)
      (nhdsWithin 0 (Set.Ioi 0))
      (𝓝 0)
```

The support predicate may be more convenient as `ρ / q ≤ ‖x‖`. The proof uses

\[
q^{-r}\le \rho^{-r}\|x\|^r
\]

on the support, then `MeasureTheory.tendsto_integral_filter_of_dominated_convergence`.

This lemma completely isolates the domain mismatch.

### Tide J5c: local rate-DCT lemma

Prove the common-ball result:

```lean
theorem tendsto_local_divided_integrand_difference
    {k : ℕ} (hk : 2 < k)
    ...
    {P : EuclidD d → ℝ}
    (hP_cont : Continuous P)
    (hP_growth : HasPolynomialGrowth P) :
    Tendsto
      (fun q =>
        ∫ x,
          commonBallIndicator q x *
          P x *
          ((Real.exp (-a₁ q x) - Real.exp (-a₂ q x)) /
            q ^ (k - 2)))
      (nhdsWithin 0 (Set.Ioi 0))
      (𝓝 (-∫ x, P x * Q x * quadKernel H x))
```

Its dominator is

```lean
fun x => C * |P x| * ‖x‖ ^ k * Real.exp (-c * ‖x‖ ^ 2)
```

and its pointwise convergence is exactly J4 plus J5a.

### Tide J5d: unnormalized pairwise integral theorem

Combine the local term and the two domain tails:

```lean
theorem tendsto_pairwise_integral_difference
    {k : ℕ} (hk : 2 < k)
    ...
    {P : EuclidD d → ℝ}
    (hP_cont : Continuous P)
    (hP_growth : HasPolynomialGrowth P) :
    Tendsto
      (fun q =>
        (I₁ P q - I₂ P q) / q ^ (k - 2))
      (nhdsWithin 0 (Set.Ioi 0))
      (𝓝 (-∫ x, P x * Q x * quadKernel H x))
```

This is the first major public checkpoint. It is also the genuinely load-bearing J5 theorem: once it exists, normalization is routine algebra.

### Tide J5e: normalized theorem

Apply J5d to `P` and `1`, combine with ordinary H4/H5 convergence and eventual denominator positivity:

```lean
theorem tendsto_pairwise_normalized_moment_difference
    {k : ℕ} (hk : 2 < k)
    ...
    {P : EuclidD d → ℝ}
    (hP_cont : Continuous P)
    (hP_growth : HasPolynomialGrowth P) :
    Tendsto
      (fun q =>
        (rescaledPosteriorMoment A₁ P q -
           rescaledPosteriorMoment A₂ P q) /
          q ^ (k - 2))
      (nhdsWithin 0 (Set.Ioi 0))
      (𝓝 (-gaussianCovariance H P Q))
```

Use the existing positivity theorem, likely `eventually_integrand_one_pos`, or derive eventual nonzero denominators from convergence to the positive Gaussian mass.

## Bottom line

The decisive analytic estimate is

\[
\left|
P(x)\frac{e^{-a_1(q,x)}-e^{-a_2(q,x)}}{q^{k-2}}
\right|
\le
C|P(x)|\|x\|^k e^{-c\|x\|^2}.
\]

The decisive tail estimate is

\[
q^{-(k-2)}\mathbf 1_{\{\|x\|\ge\rho/q\}}
\le
\rho^{-(k-2)}\|x\|^{k-2}.
\]

Together they avoid a `sqrt q` split, avoid requiring equal domains, and reduce the final normalized statement to two applications of one generic unnormalized rate-DCT theorem.