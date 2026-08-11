## 1. Unrestricted exponential remainder versus a smaller cutoff

Your unrestricted-\(x\) route is sound, and with the current infrastructure it is the better route.

A useful scalar lemma is:

```lean
theorem abs_exp_sub_sum_range_le (N : ℕ) (x : ℝ) :
    |Real.exp x -
        ∑ i ∈ Finset.range (N + 1), x ^ i / (i.factorial : ℝ)|
      ≤ |x| ^ (N + 1) * Real.exp |x| /
          ((N + 1).factorial : ℝ)
```

Up to harmless reassociation of the right-hand side.

The series proof is mathematically straightforward:

\[
\sum_{k\ge 0}\frac{|x|^{N+1+k}}{(N+1+k)!}
\le
\frac{|x|^{N+1}}{(N+1)!}
\sum_{k\ge0}\frac{|x|^k}{k!},
\]

using

\[
(N+1)!\,k!\le (N+1+k)!.
\]

The potentially annoying part in Lean is not the analysis but the factorial/cast bookkeeping. It is still a one-time reusable scalar lemma, and is likely cheaper than adding another localization scale.

I would put the factorial inequality in a separate natural-number lemma, for example:

```lean
theorem factorial_mul_factorial_le_factorial_add (m k : ℕ) :
    m.factorial * k.factorial ≤ (m + k).factorial
```

There may already be a factorial/binomial lemma from which this follows; exact names vary across Mathlib versions. The identity

```lean
Nat.choose_eq_factorial_div_factorial
```

or divisibility facts around binomial coefficients may help, but a direct induction on `k` may be less brittle.

### Why the \(q\)-power extraction works

For

```lean
A q z := ∑ s ∈ Finset.Icc 1 N,
  q ^ s * exponentTerm s L z
```

and `0 ≤ q ≤ 1`,

\[
|A(q,z)|
\le q\sum_{s=1}^N |V_s(z)|.
\]

Hence

\[
|A(q,z)|^{N+1}
\le q^{N+1}
  \left(\sum_{s=1}^N |V_s(z)|\right)^{N+1}.
\]

A convenient Lean statement is:

```lean
theorem abs_exponentCorrection_pow_le
    (a : ℕ → ℝ) (N : ℕ) {q : ℝ}
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    |∑ s ∈ Finset.Icc 1 N, a s * q ^ s| ^ (N + 1)
      ≤ q ^ (N + 1) *
          (∑ s ∈ Finset.Icc 1 N, |a s|) ^ (N + 1)
```

This follows immediately from the existing `abs_exponent_sum_le` and monotonicity of powers.

After multiplying by the Gaussian core, the unrestricted remainder gives exactly the desired shape:

\[
e^{-T_2(z)}
  \left|e^{-A(q,z)}-\sum_{i=0}^N\frac{(-A(q,z))^i}{i!}\right|
\le
q^{N+1}Q(z)e^{-\gamma\|z\|^2},
\]

provided the mesoscopic estimate gives

\[
|A(q,z)|\le T_2(z)-\gamma\|z\|^2.
\]

### Why a \(q^{-1/4}\) cutoff is not cheaper

A smaller cutoff would require at least:

1. a second varying set;
2. a new Gaussian superpolynomial-tail theorem at radius \(q^{-1/4}\), producing \(e^{-c/\sqrt q}\);
3. annulus estimates for both the exact integrand and all coefficient terms;
4. extra indicator/eventual-membership bookkeeping.

There is also a real issue with the Peano remainder. For \(N=0\), on a fixed \(q^{-1/4}\) window one only gets

\[
|\rho_q(z)|\le \varepsilon(q)\|z\|^2,
\]

with no rate on \(\varepsilon(q)\). This need not make \(\rho_q(z)\) absolutely bounded by \(1\) uniformly over that window. Relative-to-quadratic control remains available, but absolute smallness does not.

So the smaller-window route does not actually eliminate the need for an unrestricted or relative exponential estimate in full generality.

**Recommendation:** prove the unrestricted scalar exponential remainder once and keep the existing mesoscopic window.

---

## 2. The three-tide decomposition

The decomposition is good, with two adjustments:

1. Tide 5a should cover coefficients above degree \(N\), not only \(j\le N\), because the polynomial-tail term uses them.
2. The final \(q\)-uniform Gaussian majorant should be packaged explicitly, probably at the boundary between 5b and 5c.

### Tide 5a: coefficient functions and polynomial growth

Define:

```lean
noncomputable def correctionCoeffFn
    (D : ForwardExpansionDomain N L H) (j : ℕ)
    (z : EuclidD d) : ℝ :=
  expCorrectionCoeff
    (fun s ↦ exponentTerm s L z) N j
```

Suggested outputs:

```lean
theorem continuous_correctionCoeffFn
    (D : ForwardExpansionDomain N L H) (j : ℕ) :
    Continuous (D.correctionCoeffFn j)
```

and either the project’s growth predicate:

```lean
theorem correctionCoeffFn_hasPolynomialGrowth
    (D : ForwardExpansionDomain N L H) (j : ℕ) :
    HasPolynomialGrowth (D.correctionCoeffFn j)
```

or a directly usable bound:

```lean
theorem abs_correctionCoeffFn_le
    (D : ForwardExpansionDomain N L H) (j : ℕ) :
    ∃ C ≥ 0, ∃ K : ℕ, ∀ z,
      |D.correctionCoeffFn j z| ≤ C * (1 + ‖z‖) ^ K
```

The polynomial tail of `gradedExpPoly` may involve degrees as high as \(N^2\), since `exponentPoly` has degree at most \(N\) and its \(i\)-th power has degree at most \(iN\). Therefore either:

- prove continuity/growth for arbitrary `j`, as above; or
- prove it for `j ≤ N * N`.

Arbitrary `j` is cleaner, and coefficients beyond the polynomial degree are simply zero.

An exact coefficient formula such as

```lean
theorem exponentPoly_coeff (a : ℕ → ℝ) (N j : ℕ) :
    (exponentPoly a N).coeff j =
      if j ∈ Finset.Icc 1 N then a j else 0
```

is useful. For powers, induction through `Polynomial.coeff_mul` is reasonable. The relevant coefficient identity is usually exposed through a theorem equivalent to convolution of coefficients; if rewriting with `Polynomial.coeff_mul` becomes awkward, induction on the finite polynomial construction itself may be easier.

Also include the coefficient integrability theorem here or at the start of 5c:

```lean
theorem integrable_monomial_gaussian_correctionCoeff
    (D : ForwardExpansionDomain N L H)
    (α : MultiIndex d) (j : ℕ) :
    Integrable (fun z =>
      |monomial α z| *
        Real.exp (-taylorHomogeneousTerm 2 L z) *
        |D.correctionCoeffFn j z|)
```

This requires the quadratic lower bound discussed in question 4.

### Tide 5b: scalar quantitative bounds

I would include three reusable scalar results.

#### Unrestricted Taylor remainder

```lean
theorem abs_exp_sub_sum_range_le (N : ℕ) (x : ℝ) :
    |Real.exp x -
        ∑ i ∈ Finset.range (N + 1),
          x ^ i / (i.factorial : ℝ)|
      ≤ |x| ^ (N + 1) * Real.exp |x| /
          ((N + 1).factorial : ℝ)
```

#### First-order perturbation bound

For example:

```lean
theorem abs_exp_add_sub_exp_le (x y : ℝ) :
    |Real.exp (x + y) - Real.exp x|
      ≤ Real.exp x * |y| * Real.exp |y|
```

This follows from

\[
e^{x+y}-e^x=e^x(e^y-1)
\]

and an unrestricted bound

\[
|e^y-1|\le |y|e^{|y|}.
\]

For the actual negative exponents, it may be convenient to expose:

```lean
theorem abs_exp_neg_add_sub_exp_neg_le (A δ : ℝ) :
    |Real.exp (-(A + δ)) - Real.exp (-A)|
      ≤ |δ| * Real.exp (|A| + |δ|)
```

The right side is slightly coarse but exactly suited to Gaussian absorption.

#### Polynomial tail bound

A scalar result of the form:

```lean
theorem gradedExpPoly_tail_bound
    (a : ℕ → ℝ) (N : ℕ) :
    ∃ C : ℝ, ∀ {q : ℝ},
      0 ≤ q → q ≤ 1 →
      |(gradedExpPoly a N).eval q -
          ∑ j ∈ Finset.range (N + 1),
            expCorrectionCoeff a N j * q ^ j|
        ≤ C * q ^ (N + 1) *
            polynomialMajorant a N
```

may be too abstract because `a s` will later depend on `z`. A more useful formulation could retain the finite high-degree coefficient sum:

```lean
theorem gradedExpPoly_tail_bound'
    (a : ℕ → ℝ) (N : ℕ) {q : ℝ}
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    |(gradedExpPoly a N).eval q -
        ∑ j ∈ Finset.range (N + 1),
          expCorrectionCoeff a N j * q ^ j|
      ≤ q ^ (N + 1) *
          ∑ j ∈ Finset.Ico (N + 1) (N * N + 1),
            |expCorrectionCoeff a N j|
```

The upper bound may need adjustment for `N = 0` or according to the degree estimate you prove. Using

```lean
(gradedExpPoly a N).natDegree + 1
```

is mathematically immediate but is undesirable after `a` is instantiated pointwise, because it makes the indexing bound depend syntactically on `z`. A uniform bound such as `N * N + 1` is better.

### Tide 5c: mesoscopic analytic package and integration

Before the final DCT, prove a single q-uniform majorant theorem. This is the key hidden dependency:

```lean
theorem normalized_local_remainder_bound
    (D : ForwardExpansionDomain N L H)
    (α : MultiIndex d) :
    ∃ C ≥ 0, ∃ K : ℕ, ∃ γ > 0,
      ∀ᶠ q in 𝓝[>] (0 : ℝ),
        ∀ z ∈ mesoscopicSet d q,
          |
            monomial α z *
              Real.exp (-taylorHomogeneousTerm 2 L z) *
              (
                Real.exp
                  (-(exponentCorrection D q z +
                      q ^ N * D.scaledRem q z))
                  -
                ∑ j ∈ Finset.range (N + 1),
                  q ^ j * D.correctionCoeffFn j z
              ) / q ^ N
          |
          ≤ C * (1 + ‖z‖) ^ K *
              Real.exp (-γ * ‖z‖ ^ 2)
```

This theorem is the real interface consumed by DCT. It combines:

- the scalar bounds from 5b;
- the homogeneous-term growth estimates;
- the Peano window estimate;
- the half-quadratic absorption;
- coefficient growth from 5a.

I would place it in 5c rather than 5b, because it depends on `ForwardExpansionDomain`, the mesoscopic set, and the Gaussian core. Tide 5b should remain scalar/algebraic.

Also expect two outer-tail removals in the final proof:

1. the exact rescaled numerator, via `integrand_meso_tail_isLittleO`;
2. the finite coefficient polynomial, via `gaussian_meso_tail_isLittleO` and coefficient growth.

---

## 3. DCT formulation

Use an integral over all of `EuclidD d` with the varying-window indicator folded into the integrand.

That is cleaner than varying set integrals.

Define the normalized local remainder:

```lean
noncomputable def normalizedWindowRemainder
    (D : ForwardExpansionDomain N L H)
    (α : MultiIndex d) (q : ℝ) (z : EuclidD d) : ℝ :=
  (mesoscopicSet d q).indicator
    (fun z =>
      monomial α z *
        Real.exp (-taylorHomogeneousTerm 2 L z) *
        (
          Real.exp
            (-(exponentCorrection D q z +
                q ^ N * D.scaledRem q z))
            -
          ∑ j ∈ Finset.range (N + 1),
            q ^ j * D.correctionCoeffFn j z
        ) / q ^ N)
    z
```

Then prove:

```lean
theorem tendsto_integral_normalizedWindowRemainder
    (D : ForwardExpansionDomain N L H)
    (α : MultiIndex d) :
    Tendsto
      (fun q ↦ ∫ z, normalizedWindowRemainder D α q z)
      (𝓝[>] (0 : ℝ))
      (𝓝 0)
```

The filter-indexed dominated-convergence theorem to look for is:

```lean
MeasureTheory.tendsto_integral_filter_of_dominated_convergence
```

The exact argument order varies by Mathlib version, but it asks for the usual four ingredients:

- eventual a.e. strong measurability of `f q`;
- an integrable dominating function;
- eventual a.e. domination;
- a.e. pointwise convergence.

### Pointwise convergence

For fixed `z`:

1. `eventually_mem_mesoscopicSet z` makes the indicator eventually equal to one;
2. `tendsto_scaledRem D z` supplies `ρ_q(z) → 0`;
3. `exp_graded_expansion` supplies the scalar \(o(q^N)\);
4. `IsLittleO.tendsto_div_nhds_zero` converts that into convergence of the normalized residual to zero.

The coefficient order in `exp_graded_expansion` is

```lean
expCorrectionCoeff a N j * q ^ j
```

whereas the integrated expression may naturally be written as `q ^ j * ...`; a `ring` or finite-sum congruence should resolve this.

### Domination

Use the majorant theorem proposed above and then:

```lean
integrable_pow_mul_exp_neg_mul_sq
```

possibly after converting `(1 + ‖z‖)^K` to a finite sum or bounding it by a constant times `1 + ‖z‖^K`.

A useful helper is:

```lean
theorem integrable_one_add_norm_pow_mul_gaussian
    (K : ℕ) {γ : ℝ} (hγ : 0 < γ) :
    Integrable (fun z : EuclidD d =>
      (1 + ‖z‖) ^ K * Real.exp (-γ * ‖z‖ ^ 2))
```

Proving this once will simplify several later obligations.

### Measurability traps

The fact that `mesoscopicSet q` is closed and varies with `q` is not a problem. DCT only needs measurability in `z` for each fixed `q`, not joint measurability in `(q,z)`.

You already have:

```lean
measurableSet_mesoscopicSet q
```

so use `MeasurableSet.indicator` or the corresponding a.e.-strong-measurability lemma.

The main trap is `scaledRem`: it is built from `L`, so ensure the inherited regularity gives continuity/measurability of `L`. If simplification does not infer this automatically, prove once:

```lean
theorem continuous_scaledRem
    (D : ForwardExpansionDomain N L H) {q : ℝ} (hq : q ≠ 0) :
    Continuous (D.scaledRem q)
```

or merely:

```lean
theorem aestronglyMeasurable_scaledRem
    ...
```

Since DCT is along `𝓝[>] 0`, measurability is only needed eventually, so `q ≠ 0` is available.

### Why not set integrals directly?

A set integral is definitionally an indicator integral anyway. With a varying set, working directly with

```lean
∫ z in mesoscopicSet d q, ...
```

usually leaves you manually unfolding `Measure.restrict` or `Set.indicator` when proving pointwise convergence. Folding the indicator into the function from the start makes the DCT application explicit and predictable.

---

## 4. Half-quadratic bound and the \(T_2/H\) bridge

Bridge `taylorHomogeneousTerm 2 L` to the quadratic form first, then formulate all analytic bounds using `taylorHomogeneousTerm 2 L`.

That gives the best division of responsibilities:

- the coefficient and exponent-split layer naturally uses `taylorHomogeneousTerm 2 L`;
- the existing positive-definiteness/coercivity package naturally uses `H`;
- one early bridge transfers positivity from `H` to `T₂`;
- the integration layer then never needs to rewrite back and forth.

For example:

```lean
theorem taylorHomogeneousTerm_two_eq_qform
    (D : ForwardExpansionDomain N L H) (z : EuclidD d) :
    taylorHomogeneousTerm 2 L z =
      (1 / 2 : ℝ) * Matrix.quadraticForm H z := by
  ...
```

Use the repository’s actual quadratic-form notation.

Then derive a named lower bound:

```lean
theorem taylorHomogeneousTerm_two_lower
    (D : ForwardExpansionDomain N L H) :
    ∃ γ > 0, ∀ z : EuclidD d,
      γ * ‖z‖ ^ 2 ≤ taylorHomogeneousTerm 2 L z
```

If the inherited domain already has a canonical Gaussian rate, expose that exact constant instead of existentially choosing another one:

```lean
theorem gaussianRate_mul_norm_sq_le_T2
    (D : ForwardExpansionDomain N L H) (z : EuclidD d) :
    D.gaussianRate * ‖z‖ ^ 2 ≤
      taylorHomogeneousTerm 2 L z
```

Do not assume without proof that this rate is literally the same as `LocalLaplaceDomain.c`; use whichever positive-definiteness constant is already attached to `H`, then weaken it as necessary.

### Strengthen the remainder window lemma using Peano

The existing `abs_scaledRem_le` only gives a fixed constant. For the half-quadratic estimate, especially when `N = 0`, you need the arbitrary-small Peano version:

```lean
theorem eventually_abs_scaledRem_le
    (D : ForwardExpansionDomain N L H)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ q in 𝓝[>] (0 : ℝ),
      ∀ z ∈ mesoscopicSet d q,
        |D.scaledRem q z|
          ≤ ε * ‖z‖ ^ (N + 2)
```

This follows directly from `D.taylorPeano` plus `smul_mem_ball_of_mesoscopic`.

Then derive the form actually needed in the exponent:

```lean
theorem eventually_abs_scaledPerturbation_le_quadratic
    (D : ForwardExpansionDomain N L H)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ q in 𝓝[>] (0 : ℝ),
      ∀ z ∈ mesoscopicSet d q,
        |q ^ N * D.scaledRem q z|
          ≤ ε * ‖z‖ ^ 2
```

On the window,

\[
q^N\|z\|^{N+2}
=
\|z\|^2(q\|z\|)^N
\le \|z\|^2,
\]

eventually, because \(q\|z\|\le\sqrt q\le1\).

Likewise prove the homogeneous correction estimate:

```lean
theorem eventually_abs_exponentCorrection_le_quadratic
    (D : ForwardExpansionDomain N L H)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ q in 𝓝[>] (0 : ℝ),
      ∀ z ∈ mesoscopicSet d q,
        |∑ s ∈ Finset.Icc 1 N,
            q ^ s * exponentTerm s L z|
          ≤ ε * ‖z‖ ^ 2
```

Here

\[
q^s|V_s(z)|
\le C_s\|z\|^2(q\|z\|)^s
\le C_s q^{s/2}\|z\|^2.
\]

Finally combine the two using a quarter of the Gaussian rate for each:

```lean
theorem exponentCorrection_le_quadratic_on_meso
    (D : ForwardExpansionDomain N L H) :
    ∃ γ > 0,
      ∀ᶠ q in 𝓝[>] (0 : ℝ),
        ∀ z ∈ mesoscopicSet d q,
          |∑ s ∈ Finset.Icc 1 N,
              q ^ s * exponentTerm s L z|
            + |q ^ N * D.scaledRem q z|
            ≤
              taylorHomogeneousTerm 2 L z -
                γ * ‖z‖ ^ 2
```

This form is stronger and more directly useful than merely bounding the total signed correction:

```lean
|A + δ| ≤ ...
```

The scalar estimates use `exp (|A| + |δ|)`, so a bound on the sum of absolute values avoids cancellation issues.

A simpler constant-based version is also fine:

```lean
theorem abs_corrections_le_half_gaussianRate
    ...
    ≤ (D.gaussianRate / 2) * ‖z‖ ^ 2
```

From it derive the Gaussian absorption lemma:

```lean
theorem gaussian_absorb_corrections_on_meso
    (D : ForwardExpansionDomain N L H) :
    ∀ᶠ q in 𝓝[>] (0 : ℝ),
      ∀ z ∈ mesoscopicSet d q,
        Real.exp (-taylorHomogeneousTerm 2 L z) *
            Real.exp
              (|exponentCorrection D q z| +
                |q ^ N * D.scaledRem q z|)
          ≤ Real.exp
              (-(D.gaussianRate / 2) * ‖z‖ ^ 2)
```

This is the exact interface the quantitative remainder proof wants.

## Recommended implementation order inside stage 5

1. Prove the \(T_2/H\) bridge and a named positive Gaussian lower bound.
2. Prove arbitrary-small Peano control uniformly on the mesoscopic window.
3. Prove absolute correction absorption into a weakened Gaussian.
4. Build coefficient-function continuity and polynomial growth, including high-degree tail coefficients.
5. Add the unrestricted exponential and perturbation inequalities.
6. Prove the normalized q-uniform Gaussian majorant.
7. Apply filter-indexed DCT with the indicator folded into the integrand.
8. Remove the exact and coefficient outer tails using the existing stage-2 results.
9. Package `numerator_hasExpansion`.

That keeps the scalar algebra reusable while concentrating all domain-specific uniformity in one majorant theorem immediately before DCT.