## A. Correctness of the proposed statements

Yes, with a few useful qualifications.

Let
\[
L_{k,a}(x)=\sum_{i=0}^{d-1} a_i x_i^{2k_i},
\qquad a_i>0,\quad k_i\ge 1,
\]
and let \(t>0\).

### 1. Factorization

For \(j : \mathrm{Fin}\,d\to\mathbb N\), define the even monomial
\[
x^{2j}=\prod_i x_i^{2j_i}.
\]
Then
\[
e^{-tL_{k,a}(x)}
 =\prod_i e^{-t a_i x_i^{2k_i}},
\]
so finite-product Fubini gives
\[
\int_{\mathbb R^d}x^{2j}e^{-tL_{k,a}(x)}\,dx
=
\prod_i
\int_{\mathbb R}u^{2j_i}e^{-t a_i u^{2k_i}}\,du.
\]

In particular,
\[
Z_{k,a}(t)
=
\prod_i Z_{k_i,a_i}(t).
\]

After dividing by the partition function,
\[
\left\langle \prod_i x_i^{2j_i}\right\rangle_t
=
\prod_i \left\langle x^{2j_i}\right\rangle_{t,k_i,a_i}.
\]

There is no analytic failure here: for \(t>0\), \(a_i>0\), and \(k_i\ge1\), every one-dimensional factor is finite and the partition factors are strictly positive.

The one-dimensional formula is
\[
\int_{\mathbb R}u^{2j}e^{-ta u^{2k}}\,du
=
\frac1k
\Gamma\!\left(\frac{2j+1}{2k}\right)
(ta)^{-\frac{2j+1}{2k}},
\]
and hence
\[
\left\langle x^{2j}\right\rangle_{t,k,a}
=
\frac{\Gamma((2j+1)/(2k))}
     {\Gamma(1/(2k))}
(ta)^{-j/k}.
\]

Therefore
\[
\left\langle \prod_i x_i^{2j_i}\right\rangle_t
=
C_{k,a,j}\,
t^{-\sum_i j_i/k_i},
\]
where
\[
C_{k,a,j}
=
\prod_i
\frac{\Gamma((2j_i+1)/(2k_i))}
     {\Gamma(1/(2k_i))}
a_i^{-j_i/k_i}>0.
\]

This is exact, not merely asymptotic.

### 2. Affine versus linear exponent

There is a small normalization distinction worth making explicit.

Set
\[
q_i=\frac1{2k_i}.
\]

For the **unnormalized** monomial integral with multi-index \(\alpha\),
\[
I_\alpha(t)=\int x^\alpha e^{-tL(x)}\,dx,
\]
the nonzero even moments have exponent
\[
\ell_{\mathrm{un}}(\alpha)
=
\sum_i(\alpha_i+1)q_i
=
\ell_{\mathrm{un}}(0)+\sum_i\alpha_iq_i.
\]
Thus
\[
q_i=
\frac{\ell_{\mathrm{un}}(2e_i)-\ell_{\mathrm{un}}(0)}2.
\]

For the **normalized** moment,
\[
M_\alpha(t)=\frac{I_\alpha(t)}{I_0(t)},
\]
the partition-function exponent cancels:
\[
\ell_{\mathrm{norm}}(\alpha)=\sum_i\alpha_iq_i.
\]
So it is linear, or affine with zero intercept, and
\[
q_i=\frac{\ell_{\mathrm{norm}}(2e_i)}2.
\]

Thus the draft’s formula involving \(\ell(0)\) is exactly the unnormalized convention. For normalized moments, \(\ell(0)=0\).

It is best to restrict the formal statement to even monomials, or possibly absolute monomials. Ordinary odd monomials have zero expectation and therefore do not have a positive leading constant from which an exponent can be read.

### 3. Weight recovery from coordinate second moments

The \(i\)-th normalized second moment is
\[
M_i(t)
=
\langle x_i^2\rangle_t
=
\frac{\Gamma(3/(2k_i))}
     {\Gamma(1/(2k_i))}
(t a_i)^{-1/k_i}.
\]

Thus its power-law exponent is
\[
\frac1{k_i}=2q_i.
\]

If two models satisfy
\[
M_i(t)=M'_i(t)
\]
on a ray, or eventually as \(t\to\infty\), power-law rigidity gives
\[
\frac1{k_i}=\frac1{k'_i},
\]
hence \(k_i=k'_i\) and \(q_i=q'_i\).

An eventual equality hypothesis
```lean
∀ᶠ t in atTop, M i t = M' i t
```
is equivalent to equality on some sufficiently large ray, so it matches the shape of a “rigidity on a ray” theorem after unpacking `eventually_atTop`.

An `IsEquivalent` hypothesis is also enough, provided it is genuine asymptotic equivalence with ratio \(1\), not merely equality of logarithmic rates or a `Theta` relation. Two positive exact power laws can be asymptotically equivalent only if both their exponents and leading coefficients agree.

### 4. Scale recovery

Once \(k_i=k'_i\), equality or asymptotic equivalence of the second moments gives
\[
a_i^{-1/k_i}=(a'_i)^{-1/k_i},
\]
so \(a_i=a'_i\).

This can be implemented either directly from the closed form or via the merged one-dimensional `BaseRecovery` result. At temperature \(t\), the coordinate marginal is the one-dimensional model with effective coefficient \(t a_i\), so injectivity of \(M_2\) in its coefficient gives
\[
t a_i=t a'_i,
\]
and \(t>0\) permits cancellation.

One qualification: “single observable per coordinate” means the entire large-\(t\) behavior of that observable, including its leading coefficient. A single scalar value \(M_i(t_0)\) at one temperature does not determine both the discrete parameter \(k_i\) and the continuous parameter \(a_i\).

Also, this is coordinate-wise identifiability in a fixed labelled coordinate system. If coordinates are considered only up to permutation, the conclusion should similarly be stated up to permutation.

---

## B. Cheapest Lean staging and API choices

### Recommendation: prove the analytic core on `Fin d → ℝ`

The cheapest route is:

1. Prove all product-integral statements on the plain Pi type
   ```lean
   Fin d → ℝ
   ```
   with its product volume measure.
2. Add thin `EuclidD d` wrappers afterward using
   ```lean
   PiLp.volume_preserving_toLp
   ```

The product structure is native on `Fin d → ℝ`, and this is exactly the domain expected by the existing
```lean
integral_fintype_prod_volume_eq_prod
```
machinery. Starting directly on `EuclideanSpace ℝ (Fin d)` introduces `PiLp` coercions and transport bookkeeping into every Fubini proof for no mathematical gain.

The rest of the multivariate development can consume wrappers on
```lean
EuclidD d := EuclideanSpace ℝ (Fin d)
```
after the core theorem is established.

### Suggested parameterization

To reuse the existing one-dimensional API with minimal conversion overhead, use the same type for \(k\) as those results, likely:
```lean
(k : Fin d → ℕ)
(hk : ∀ i, 0 < k i)
(a : Fin d → ℝ)
(ha : ∀ i, 0 < a i)
```

Using `PNat` or a custom positive-integer structure is aesthetically attractive, but only worthwhile if the existing 1D API already uses it.

Definitions can be along the lines of:
```lean
def separablePotential
    (k : Fin d → ℕ) (a : Fin d → ℝ)
    (x : Fin d → ℝ) : ℝ :=
  ∑ i, a i * (x i) ^ (2 * k i)

def evenMonomial
    (j : Fin d → ℕ)
    (x : Fin d → ℝ) : ℝ :=
  ∏ i, (x i) ^ (2 * j i)
```

Always place `0 < t` in the closed-form statements. The large-\(t\) recovery theorems can discharge this eventually because positivity is automatic at `atTop`.

### Stage 1: unnormalized product factorization

Prove one theorem subsuming both partition functions and moment numerators:
```lean
∫ x, evenMonomial j x *
      Real.exp (-t * separablePotential k a x)
=
∏ i, ∫ u, u ^ (2 * j i) *
      Real.exp (-t * a i * u ^ (2 * k i))
```

The algebraic preparation is:

- distribute `-t` across the finite sum;
- rewrite `Real.exp` of a sum as a finite product;
- combine the monomial product and exponential product into one product;
- invoke `integral_fintype_prod_volume_eq_prod`.

Taking `j = 0` gives partition-function factorization.

Because the existing finite-product integral theorem is described as unconditional, there should be no need to build a separate multivariate integrability library before applying Fubini. Positivity and finiteness still enter later through the one-dimensional closed forms.

### Stage 2: normalized factorization

Define the normalized moment as numerator divided by partition function and prove
```lean
separableMoment k a j t
  =
∏ i, oneDMoment (k i) (a i) (j i) t
```

This should largely be:

- rewrite numerator and denominator by Stage 1;
- use the finite-product division identity, likely through `Finset.prod_div_distrib` or equivalent;
- identify each quotient with the existing 1D normalized moment.

One can establish nonvanishing denominators from the merged one-dimensional partition-function formula. Algebraically, the product-of-quotients identity itself may not require nonvanishing because division is total in a field, but positivity is still useful for the mathematical API and subsequent recovery.

### Stage 3: coordinate marginal corollary

Before formalizing the full multi-index Gamma formula, prove the cheapest recovery-facing statement:
```lean
coordinateSecondMoment k a i t
  =
oneDSecondMoment (k i) (t * a i)
```
or whatever parametrization matches the existing 1D `BaseRecovery` API.

All factors other than \(i\) cancel because their observable exponent is zero. This is the key bridge to reuse the one-dimensional recovery seabed directly.

This theorem is probably the highest value-to-effort first milestone: it is genuinely multidimensional but delegates all special-function and rigidity work to the established 1D theory.

### Stage 4: exact multi-index power law

Then add:
```lean
separableMoment k a j t
  =
C k a j * t ^ (-∑ i, (j i : ℝ) / k i)
```
using `Real.rpow` in the actual implementation.

It may be cheaper initially to leave this as a product of one-dimensional closed forms:
```lean
∏ i, oneDClosedForm (k i) (a i) (j i) t
```
and only later normalize products of `Real.rpow` into a single exponent. Finite-product `rpow` algebra can create more Lean friction than the analytic factorization itself.

A separate exponent theorem can state the conceptual result without forcing every downstream theorem to rewrite into a single `rpow`.

### Stage 5: recovery

Prove coordinate-wise:

1. eventual equality or `IsEquivalent` of second-moment functions implies `k i = k' i`;
2. after rewriting by that equality, 1D base recovery gives `a i = a' i`;
3. apply `funext` to conclude `k = k'` and `a = a'`;
4. conclude equality of the separable potentials.

For eventual equality, unpack the `atTop` hypothesis into a threshold and invoke the existing ray-rigidity theorem. For `IsEquivalent`, use the existing asymptotic version directly after rewriting the coordinate moments to the one-dimensional exact power-law form.

### Euclidean-space wrapper

After the Pi-type theory works, define the corresponding potential and observables on `EuclidD d` and transport integrals through:
```lean
PiLp.volume_preserving_toLp
```

Use the associated `MeasurePreserving` integral-composition lemma already employed elsewhere in the repository. Under `toLp`, coordinate evaluation is unchanged, so the transported integrand should simplify back to the Pi-type definition.

This organization keeps:

- product Fubini and Gamma calculations on the easy representation;
- public multivariate statements on `EuclidD d`;
- the measure-preserving bridge localized to one wrapper file.

I would not duplicate the complete proof on both representations.

---

## C. Is this the right minimal germ?

### Yes: the separable class is the right low-risk first tide

It gives the first constructive recovery result that is simultaneously:

- degenerate;
- genuinely multidimensional;
- anisotropic;
- equipped with unknown weights;
- fully recoverable from explicit moment data;
- almost entirely reducible to already merged 1D theorems.

It is a genuine subclass of the quasi-homogeneous story: assigning
\[
q_i=\frac1{2k_i}
\]
makes every term \(a_i x_i^{2k_i}\) have weighted degree \(1\).

It also cleanly demonstrates the central section 7.4(b) mechanism:
\[
\text{moment exponents} \longrightarrow q_i,
\qquad
\text{leading constants} \longrightarrow a_i.
\]

What it does not yet address is recovery of coefficients of mixed monomials or the Gelfand–Leray moment problem. That limitation should be stated explicitly, but it does not make the result artificial.

### The smallest meaningful first theorem

The most trivial-looking statement that is still a real step outward is not the full multi-index factorization theorem. It is:

> For a separable weighted-monomial potential on `EuclidD d`, the normalized \(i\)-th coordinate second moment is exactly the corresponding one-dimensional second moment; consequently, equality or asymptotic equivalence of these coordinate moment functions recovers \(k_i\) and \(a_i\).

This requires only:

- partition/numerator product factorization;
- cancellation of irrelevant coordinates;
- existing 1D rigidity and base recovery.

It already yields injectivity of
\[
(k,a)\mapsto \bigl(t\mapsto \langle x_i^2\rangle_t\bigr)_{i<d}.
\]

The full exponent-affinity theorem should then be the next layer, rather than a prerequisite.

### Why not start with \(x^4+x^2y^2+y^4\)?

That example is useful, but not the best first constructive theorem.

It is homogeneous with the common weights
\[
q_x=q_y=\frac14,
\]
so it does not exercise recovery of distinct unknown anisotropic weights. Moreover, exact coefficient recovery no longer follows from coordinate-wise 1D base recovery. One either:

- proves only the scaling exponent, which says little about the mixed coefficient; or
- begins a genuinely new moment-identification problem.

Its integrals do not factor, so it abandons the strongest existing seabed immediately.

It would be a reasonable later test case for a general scaling theorem, but not the cheapest first constructive recovery result.

### A conceptually better second tide: abstract anisotropic scaling

After the separable theorem, the natural next step is a general quasi-homogeneous scaling lemma.

If
\[
P(\delta_s x)=sP(x),
\qquad
\delta_s(x)_i=s^{q_i}x_i,
\]
then a diagonal change of variables gives
\[
I_\alpha(t)
=
t^{-\left(\sum_iq_i+\sum_i\alpha_iq_i\right)}
I_\alpha(1),
\]
and hence
\[
M_\alpha(t)
=
t^{-\sum_i\alpha_iq_i}M_\alpha(1).
\]

For \(\alpha=2e_i\), positivity of the second moment gives exponent \(2q_i\), so the weights are recoverable without separability.

That theorem captures the real quasi-homogeneous mechanism and immediately applies to mixed examples such as \(x^4+x^2y^2+y^4\). However, it is more expensive in Lean because it needs:

- the diagonal dilation map;
- its Jacobian or volume-scaling theorem;
- `Real.rpow` bookkeeping;
- change of variables on `EuclidD`;
- integrability assumptions for a general \(P\).

An abstract version assuming a suitable pushforward/measure-scaling identity could reduce the initial burden, but it would still need a concrete instantiation to become a constructive result.

## Recommended roadmap

1. **Coordinate marginal theorem on `Fin d → ℝ`.**
2. **Coordinate second-moment recovery of every \(k_i,a_i\).**
3. **Transported `EuclidD d` theorem.**
4. **Full even multi-index factorization and exact exponent affinity.**
5. **General anisotropic quasi-homogeneous scaling theorem.**
6. **Only then, mixed-term/Gelfand–Leray coefficient recovery.**

This gives a small, robust first extension beyond the 1D degenerate theory while laying the exact API needed for the genuinely nonseparable quasi-homogeneous case.